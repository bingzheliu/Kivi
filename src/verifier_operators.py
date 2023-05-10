# TODO: 1. add options (OptionParser) to the system


import json
import subprocess

from model_generator import model_generator
from result_parser import *
from util import *
from case_generator import *
from small_scale_finder import *

# TODO: deal with the situation where max search is too small
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

# TODO: keep steam the output from the ./pan, and if see "max search depth too small", we could just stop the execuation and adjust the running configs for pan
def verifer_operator_one(json_config, result_base_path, pml_base_path, file_base, case_id, scale, run_count, log_level, pan_compile, pan_para, queue_size_default):
	main_filename = model_generator(json_config, pml_base_path, file_base, case_id, scale, queue_size_default=queue_size_default)

	stdout, stderr = run_script([file_base + '/libs/Spin/Src/spin', '-a', pml_base_path + "/" + main_filename], True)
	myprint(stdout, logger.debug)

	stdout, stderr = run_script(['gcc'] + pan_compile, True)

	with open(result_base_path + "/" + str(scale)+ "_" + str(run_count), "w") as fw:
		stdout, stderr = run_script(['./pan']+pan_para, False)
		with open(result_base_path + "/raw_data/exec_" + str(case_id) + "_" + str(scale) + "_" + str(run_count), "w") as fr:
			fr.write(stdout.decode())
		failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())
		fw.write(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time) + '\n')
		logger.critical(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time))
		myprint(failure_details)

		if error_trail_name != None:
			stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
			with open(result_base_path + "/raw_data/error_" + str(case_id) + "_" + str(scale)+ "_" + str(run_count), "w") as fr:
				fr.write(stdout.decode())
			result_log, failure_details = parse_spin_error_trail(stdout.decode(), failure_type, log_level)
			myprint(result_log, logger.debug)
			fw.write(result_log)

	return failure_type, failure_details, total_mem, elapsed_time

def verifer_operator_adjust_queue(json_config, result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para):
	run_count = 0
	queue_size = 10
	failure_type, failure_details, total_mem, elapsed_time = verifer_operator_one(deepcopy(json_config), result_base_path, pml_base_path, file_base, case_id, scale, run_count, log_level, pan_compile, pan_para, None)

	while queue_size < 200:
		if len(failure_details.split("\n")) > 1 and "Queue is full!" in failure_details.split("\n")[1]:
			run_count += 1
			logger.critical("trying queue size "+str(queue_size))
			failure_type, failure_details, total_mem, elapsed_time = verifer_operator_one(deepcopy(json_config), result_base_path, pml_base_path, file_base, case_id, scale, run_count, log_level, pan_compile, pan_para, queue_size)
			queue_size *= 2
		else:
			break

	if queue_size > 200:
		failure_type, failure_details, total_mem, elapsed_time = verifer_operator_one(deepcopy(json_config), result_base_path, pml_base_path, file_base, case_id, scale, run_count, log_level, pan_compile, pan_para, None)

	return failure_type, failure_details, total_mem, elapsed_time

def verifer_operator(result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para):
	if int(scale) == 0:
		json_config = get_case_temeplate(file_base, case_id)
		all_setup, json_config_template = finding_smallest_scale(json_config, pml_base_path, file_base, case_id)
		for s in all_setup:
			new_json_config, num_node, num_pod = generate_case_json(json_config_template, s)
			logger.critical("===========================")
			logger.critical("Working on setup: " + str_setup(s))

			failure_type, failure_details, total_mem, elapsed_time = verifer_operator_adjust_queue(new_json_config, result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para)
		
			if failure_type != "None":
				logger.critical("Failure found at scale " + str_setup(s))
				if not configs["small_scale_finder"]["stop_after_first_violation"]:
					break

	else:
		config_filename = pml_base_path + "/configs/" + case_id + "_" + scale + ".json"
		case_generator(case_id, scale, config_filename)
		with open(config_filename) as f:
			json_config = json.load(f)

		failure_type, failure_details, total_mem, elapsed_time = verifer_operator_adjust_queue(json_config, result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para)

	return total_mem, elapsed_time

# TODO: better ways to do user configs
if __name__ == '__main__':
	case_id = sys.argv[1]
	scale = sys.argv[2]

	if len(sys.argv) > 3:
		file_base = os.path.abspath(sys.argv[3])
	

	result_base_path = file_base + "/results/" + str(case_id)
	pml_base_path = file_base + "/temp/" + str(case_id) + "/" + str(scale)
	my_mkdir(file_base + "/results")
	my_mkdir(result_base_path)
	my_mkdir(result_base_path + "/raw_data")
	my_mkdir(file_base+"/temp/"+ str(case_id))
	my_mkdir(file_base+"/temp/"+ str(case_id) + "/configs")

	my_mkdir(file_base+"/temp/"+ str(case_id) + "/" + str(scale))
	my_mkdir(pml_base_path + "/configs")
	
	# bounded model checking
	pan_para = ['-m10000000']
	#'-DSAFETY', '-DNOCOMP', '-DSFH',
	pan_compile = [ '-o', 'pan', 'pan.c', '-DVECTORSZ=450000']
	if len(sys.argv) > 4:
		pan_para = sys.argv[4]
		pan_compile_added = []
		if "-l" in pan_para:
			pan_compile_added = pan_compile_added + ['-DNP']

		if "-RS" in pan_para:
			pan_compile_added = pan_compile_added + ['-DT_RAND', '-DP_RAND']

		if "-v" in pan_para:
			pan_compile_added = pan_compile_added + ['-DCHECK']


		pan_compile = pan_compile_added + pan_compile
		pan_para = pan_para.split(" ")

	verifer_operator(result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para)

	
