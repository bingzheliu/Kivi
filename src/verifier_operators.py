import json
import subprocess

from model_generator import model_generator
from result_parser import *
from util import *


def run_script(commands, print_stdout):
	s_output = ""
	for s in commands:
		s_output += (s + " ")
	logger.info("running " + s_output)

	spin_script = subprocess.Popen(commands,
	                     stdout=subprocess.PIPE, 
	                     stderr=subprocess.PIPE)
	stdout, stderr = spin_script.communicate()

	myprint(stderr.decode(), logger.error)
	
	return stdout, stderr

def myprint(output, log_func=logger.info):
	if len(output) > 0:
		log_func(output)

# TODO: keep steam the output from the ./pan, and if see "max search depth too small", we could just stop the execuation and adjust the running configs for pan
def verifer_operator(file_base, case_id, scale, log_level, pan_para):
	main_filename = model_generator(file_base, case_id, scale)

	stdout, stderr = run_script([file_base + '/libs/Spin/Src/spin', '-a', file_base + '/temp/' + case_id + "/" + main_filename], True)
	
	stdout, stderr = run_script(['gcc', '-o', 'pan', 'pan.c', '-DVECTORSZ=450000'], True)

	with open(file_base + "/results/" + str(case_id) + "/" + str(scale), "w") as fw:
		if pan_para != "":
			stdout, stderr = run_script(['./pan', '-m36900', pan_para], False)
		else:
			stdout, stderr = run_script(['./pan', '-m10000000'], False)
		with open(file_base + "/results/" + str(case_id) + "/raw_data/exec_" + str(case_id) + "_" + str(scale), "w") as fr:
			fr.write(stdout.decode())
		failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())
		fw.write(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time) + '\n')
		logger.critical(failure_type + " " + str(total_mem) + " " + str(elapsed_time))
		myprint(failure_details)

		if error_trail_name != None:
			stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
			with open(file_base + "/results/" + str(case_id) + "/raw_data/error_" + str(case_id) + "_" + str(scale), "w") as fr:
				fr.write(stdout.decode())
			result_log, failure_details = parse_spin_error_trail(stdout.decode(), failure_type, log_level)
			myprint(result_log, logger.debug)
			fw.write(result_log)

	return total_mem, elapsed_time


if __name__ == '__main__':
	case_id = sys.argv[1]
	scale = sys.argv[2]

	file_base = sys.argv[1] = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
	if len(sys.argv) > 3:
		file_base = sys.argv[3]

	result_base_path = file_base + "/results/" + str(case_id)
	my_mkdir(result_base_path)
	my_mkdir(result_base_path + "/raw_data")
	my_mkdir(file_base+"/temp/"+ str(case_id))
	my_mkdir(file_base+"/temp/"+ str(case_id) + "/configs")

	pan_para = ""
	if len(sys.argv) > 4:
		pan_para = sys.argv[4]

	verifer_operator(file_base, case_id, scale, log_level, pan_para)

	
