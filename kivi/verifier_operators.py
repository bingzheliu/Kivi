# TODO: 1. add options (OptionParser) to the system
import subprocess

from util import *
from model_generator import model_generator
from result_parser import parse_pan_output, parse_spin_error_trail
from cases.case_generator import case_generator
from small_scale_finder import finding_smallest_scale, generate_case_json, str_setup

# TODO: keep steam the output from the ./pan, and if see "max search depth too small", we could just stop the execuation and adjust the running configs for pan
def verifier_operator_one(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, queue_size_default):
	main_filename = model_generator(json_config, pml_base_path, file_base + "/kivi/templates", queue_size_default=queue_size_default)

	if queue_size_default is not None:
		queue_size = queue_size_default
	else:
		queue_size = 0

	stdout, stderr = run_script([file_base + '/libs/Spin/Src/spin', '-a', pml_base_path + "/" + main_filename], True)
	myprint(stdout, logger.debug)

	stdout, stderr = run_script(['gcc'] + pan_compile, True)

	result_log = ""
	with open(result_base_path + "/" + case_name + "_" + str(queue_size), "w") as fw:
		stdout, stderr = run_script(['./pan']+pan_runtime, False)
		with open(result_base_path + "/raw_data/exec_" + case_name + "_" + str(queue_size), "w") as fr:
			fr.write(stdout.decode())
		failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())
		fw.write(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time) + '\n')
		logger.critical(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time))
		myprint(failure_details)

		if error_trail_name != None:
			stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
			with open(result_base_path + "/raw_data/error_" + case_name + "_" + str(queue_size), "w") as fr:
				fr.write(stdout.decode())
			result_log, failure_details = parse_spin_error_trail(stdout.decode(), log_level, failure_type)
			myprint(result_log, logger.debug)
			fw.write(result_log)

	return failure_type, result_log, failure_details, total_mem, elapsed_time

def verifier_operator_adjust_queue(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base):
	queue_size = 10
	failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, None)

	while queue_size < 200:
		if len(failure_details.split("\n")) > 1 and "Queue is full!" in failure_details.split("\n")[1]:
			logger.critical("trying queue size "+str(queue_size))
			failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, queue_size)
			queue_size *= 2
		else:
			break

	if queue_size > 200:
		failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, None)

	return failure_type, result_log, failure_details, total_mem, elapsed_time

def verifier_operator(json_config, case_name, file_base, result_base_path, pml_base_path):
	pan_runtime = ["-" + o.strip() for o in args.pan_runtime.split(",")]
	pan_compile = ['-o', 'pan', 'pan.c']
	pan_compile.extend(["-" + o.strip() for o in args.pan_compile.split(",")])
	logger.debug("pan_runtime:" + str(pan_runtime))
	logger.debug("pan_compile:" + str(pan_compile))
	log_level = args.verbose_level
	failures = []

	if args.loop:
		pan_compile.append("-DNP")
		pan_runtime.append("-l")

	if not args.original:
		all_setup, json_config_template = finding_smallest_scale(json_config, pml_base_path)
		for s in all_setup:
			new_json_config, num_node, num_pod = generate_case_json(json_config_template, s)
			logger.critical("===========================")
			logger.critical("Working on setup: " + str_setup(s))

			failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_adjust_queue(new_json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base)

			if failure_type != "None":
				failures.append((failure_type, result_log, failure_details, total_mem, elapsed_time))
				logger.critical("Failure found at scale " + str_setup(s))
				if not args.all_violation:
					break

	else:
		failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_adjust_queue(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base)

		if failure_type != "None":
			failures.append((failure_type, result_log, failure_details, total_mem, elapsed_time))
			logger.critical("Failure found!")

	return failures

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

	verifier_operator(result_base_path, pml_base_path, file_base, case_id, scale, log_level, pan_compile, pan_para)

	
