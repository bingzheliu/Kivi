import json
import subprocess
import sys

from model_generator import model_generator
from result_parser import *

log_level = 6

def run_script(commands, print_stdout):
	s_output = ""
	for s in commands:
		s_output += (s + " ")
	print("running " + s_output)

	spin_script = subprocess.Popen(commands,
	                     stdout=subprocess.PIPE, 
	                     stderr=subprocess.PIPE)
	stdout, stderr = spin_script.communicate()

	if print_stdout:
		myprint(stdout.decode())
	myprint(stderr.decode())
	
	return stdout, stderr

def myprint(output):
	if len(output) > 0:
		print(output)

if __name__ == '__main__':
	file_base = sys.argv[1]
	case_id = sys.argv[2]
	scale = sys.argv[3]

	model_generator(file_base, case_id, scale)

	stdout, stderr = run_script(['libs/Spin/Src/spin', '-a', 'temp/main.pml'], True)
	
	stdout, stderr = run_script(['gcc', '-o', 'pan', 'pan.c', '-DVECTORSZ=450000'], True)

	with open(file_base + "/results/" + str(case_id) + "_" + str(scale), "w") as fw:
		stdout, stderr = run_script(['./pan', '-m10000000'], False)
		with open(file_base + "/results/raw_data/exec_" + str(case_id) + "_" + str(scale), "w") as fr:
			fr.write(stdout.decode())
		failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())
		fw.write(failure_type + " " + str(total_mem) + " " + str(elapsed_time) + '\n')
		print(failure_type, total_mem, elapsed_time)
		myprint(failure_details)

		if error_trail_name != None:
			stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
			with open(file_base + "/results/raw_data/error_" + str(case_id) + "_" + str(scale), "w") as fr:
				fr.write(stdout.decode())
			result_log, failure_details = parse_spin_error_trail(stdout.decode(), failure_type, log_level)
			print(result_log)
			fw.write(result_log)



		

