import sys
from datetime import datetime
import time
import os

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

if len(sys.argv) > 1:
	sys_path = os.path.abspath(sys.argv[1])

sys.path.insert(0, sys_path+"/src")

from verifier_operators import *


if __name__ == '__main__':
	file_base = sys_path
	
	list_case_id = ["s6"]
	list_scale = ["3", "10", "20", "50", "80", "100"]
	times = 3
	log_level = 3

	#configs["case_generator"]["non_violation"] = True

	for case_id in list_case_id:
		result_base_path = file_base + "/results/" + str(case_id)
		my_mkdir(file_base + "/results")
		my_mkdir(result_base_path)
		my_mkdir(result_base_path + "/raw_data")
		my_mkdir(file_base+"/temp/"+ str(case_id))

		pan_para = ['-m1000000']
		pan_compile = [ '-o', 'pan', 'pan.c', '-DVECTORSZ=450000', '-DT_RAND', '-DP_RAND']
		# if len(sys.argv) > 4:
		# 	pan_para = sys.argv[4]
		# 	pan_para = pan_para.split(" ")
		# 	if "-l" in pan_para:
		# 		pan_compile.append("-DNP")
		
		with open(result_base_path + "/runtime", "w") as fw:
			for scale in list_scale:
				logger.info("Working on case "+case_id+" scale "+str(scale))
				pml_base_path = file_base + "/temp/" + str(case_id) + "/" + str(scale)
				my_mkdir(file_base+"/temp/"+ str(case_id) + "/" + str(scale))
				my_mkdir(pml_base_path + "/configs")

				total_mem = 0
				total_elapsed_time = 0

				total_time = 0
				for i in range(times):
					logger.info("Times "+str(i))
					t1 = time.time()
					cur_mem, cur_elapsed_time = verifer_operator(result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para)
					t2 =  time.time()
					total_mem += float(cur_mem)
					total_elapsed_time += float(cur_elapsed_time)

					cur_total_time = (t2 - t1)
					total_time += cur_total_time

					
				total_mem = total_mem * 1.0 / times
				total_elapsed_time = total_elapsed_time * 1.0 / times
				total_time = total_time * 1.0/times
				fw.write(scale + " " + str(total_time) + " " + str(total_elapsed_time) + " " + str(total_mem) + "\n")

