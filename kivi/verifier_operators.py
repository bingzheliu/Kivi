import subprocess
import random
import datetime

from util import *
from config import *
from model_generator import model_generator
from result_parser import parse_pan_output, parse_spin_error_trail
from cases.case_generator import case_generator
from small_scale_finder import finding_smallest_scale, generate_case_json, str_setup

intent_groups = {"never":[], "loop":["loop"], "assert":["no_feasiable_node", "kernel_panic", "checkOscillation", \
				"checkMinReplicas", "checkExpReplicas", "checkEvictionCycle", "checkBalanceNode"]}

# intents can be seperated into subsets in this function.
def analyze_divide_intents(json_config):
	new_intents = []

	all_intents = deepcopy(json_config["intents"])
	# first, the intents in different intent groups must be divided, as the are verified in different ways.
	group_to_intents = {}
	group_count = {}
	for k in intent_groups:
		group_count[k] = 0
	for intent in all_intents:
		# put all of the str into one group
		if isinstance(intent, str):
			if "str_group" not in group_to_intents:
				group_to_intents["str_group"] = []
			group_to_intents["str_group"].append(deepcopy(intent))
		else:
			for ig in intent_groups:
				if intent["name"] in intent_groups[ig]:
					# never needs to be seperated
					if ig == "never":
						group_to_intents["never_"+str(group_count[ig])] = []
						group_to_intents["never_"+str(group_count[ig])].append(deepcopy(intents))
						group_count[ig] += 1
					else:
						cur_group = ig+"_"+str(group_count[ig])
						if cur_group not in group_to_intents:
							group_to_intents[cur_group] = []

						# user can define how many intents to be verified at the same time. Default is all possible intents at the same time, and will skip the following. 
						if args.intents_group > 0 and len(group_to_intents[cur_group]) >= args.intents_group:
							group_count[ig] += 1
							cur_group = ig+"_"+str(group_count[ig])
							group_to_intents[cur_group] = []

						group_to_intents[cur_group].append(deepcopy(intent))

	intent_group_list = list(group_to_intents.values())

	# print(all_intents)
	# print("======")
	# print(intent_group_list)
	# print("======")

	return intent_group_list

# TODO: keep steam the output from the ./pan, and if see "max search depth too small", we could just stop the execuation and adjust the running configs for pan
def verifier_operator_one(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, queue_size_default):
	intent_group_list = analyze_divide_intents(json_config)
	new_failures = []
	for intents in intent_group_list:
		# TODO: may need to process loop seperately. 
		cur_json_config = deepcopy(json_config)
		cur_json_config["intents"] = intents
		logger.critical("Currently working on the following intents:")
		logger.critical(intents)
		main_filename = model_generator(cur_json_config, pml_base_path, file_base + "/kivi/templates", queue_size_default=queue_size_default)

		if queue_size_default is not None:
			queue_size = queue_size_default
		else:
			queue_size = 0

		success, stdout, stderr = run_script([file_base + '/libs/Spin/Src/spin', '-a', pml_base_path + "/" + main_filename], True)
		myprint(stdout, logger.debug)

		success, stdout, stderr = run_script(['gcc'] + pan_compile, True)

		result_log = ""

		success = False
		if args.random:
			while not success:
				timeout = args.timeout if args.timeout is not None else default_timeout
				rand = random.randint(1, 1000)
				success, stdout, stderr = run_script(['./pan']+pan_runtime+['-RS'+str(rand)], False, timeout)
		else:
			if args.timeout:
				success, stdout, stderr = run_script(['./pan']+pan_runtime, False, args.timeout)
			else:
				success, stdout, stderr = run_script(['./pan']+pan_runtime, False)

		# with open(file_base + "/bin/eval/results/" + case_name.split("_")[0].strip() + "/pan_" + str(queue_size), "w") as fr:
		# 		fr.write(str(datetime.datetime.now()))
		# 		fr.write(stdout.decode())

		if args.file_debug > 0:
			with open(result_base_path + "/raw_data/exec_" + case_name + "_" + str(queue_size), "w") as fr:
				fr.write(stdout.decode())

		failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())

		if args.file_debug > 0:
			with open(result_base_path + "/" + case_name + "_" + str(queue_size), "w") as fw:
				fw.write(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time) + '\n')

		logger.critical(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time))
		myprint(failure_details)

		if error_trail_name != None:
			success, stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
			if args.file_debug > 0:
				with open(result_base_path + "/raw_data/error_" + case_name + "_" + str(queue_size), "w") as fr:
					fr.write(stdout.decode())
			result_log, failure_details = parse_spin_error_trail(stdout.decode(), log_level, failure_type)
			myprint(result_log, logger.debug)
			if args.file_debug > 0:
				with open(result_base_path + "/" + case_name + "_" + str(queue_size), "w") as fw:
					fw.write(result_log)

		new_failures.append((failure_type, result_log, failure_details, total_mem, elapsed_time))
		if failure_type != "None":
			logger.critical("Failure found at intent " + str(intents))
			if not args.all_violation:
				break

	return new_failures

def verifier_operator_adjust_queue(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base):
	queue_size = 10
	new_failures = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, None)

	while queue_size < 500:
		for failure in new_failures:
			failure_details = failure[2]
		if len(failure_details.split("\n")) > 1 and "Queue is full!" in failure_details.split("\n")[1]:
			logger.critical("trying queue size "+str(queue_size))
			new_failures = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, queue_size)
			queue_size *= 2
		else:
			break

	if queue_size > 500:
		logger.critical("Queue size exceed limit!")
		return []
		#failure_type, result_log, failure_details, total_mem, elapsed_time = verifier_operator_one(deepcopy(json_config), case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base, None)

	return new_failures

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
	if args.random:
		if "-DT_RAND" not in pan_compile:
			pan_compile.append("-DT_RAND")
		if "-DP_RAND" not in pan_compile:
			pan_compile.append("-DP_RAND")

	print(args)
	if not args.original:
		# Note: if the sort_favor for finding_smallest_scale is not "Nodes", will need to change the below arg.extreamly_high_confidence line to find the right break point.
		all_setup, json_config_template = finding_smallest_scale(json_config, pml_base_path)
		heatmap_name = "eval/results/heatmap/heatmap_" + case_name
		if args.case_non_violation:
			heatmap_name = heatmap_name + "_cn"
		with open(heatmap_name, "w") as fw:
			#all_setup = [{'nodes': {0: 14}, 'd': {0: 40}}]
			for s in all_setup:
				new_json_config, num_node, num_pod = generate_case_json(json_config_template, s)
				if not args.extreamly_high_confidence and num_node > high_confidence_node:
					logger.critical("Reach the upper bound of high confidence node. Verification finished!")
					break

				logger.critical("===========================")
				logger.critical("Working on setup: " + str_setup(s))

				new_failures = verifier_operator_adjust_queue(new_json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base)

				failure_found = False
				no_fesiable_node = False
				for failure in new_failures:
					if failure[0] != "None":
						failures.append(deepcopy(failure))
						logger.critical("Failure found at scale " + str_setup(s))
						failure_found = True
						if "No feasiable node!" in failure[1]:
							no_fesiable_node = True
				if not args.all_violation and failure_found:
					break

				node_str = ""
				d_str = ""
				for n in s["nodes"]:
					node_str += (str(s["nodes"][n]) + " ")
				for d in s["d"]:
					d_str += (str(s["d"][d]) + " ")

				index = node_str + d_str
				
				if failure_found:
					msg = str(len(failures)) + " failure(s) are found!\n"
					msg += (failures[-1][1] + "\n")

					logger.critical(msg)
					if no_fesiable_node:
						fw.write(index + " 3\n")
					else:
						fw.write(index + " 0\n")
				else:
					fw.write(index + " 1\n")
					#success, stdout, stderr = run_script(['cp'] + ['-r'] + [pml_base_path] + [file_base + '/bin/eval/results/heatmap/non_violation_pml/'+case_name], False)

	else:
		new_failures = verifier_operator_adjust_queue(json_config, case_name, log_level, pan_compile, pan_runtime, result_base_path, pml_base_path, file_base)

		for failure in new_failures:
			if failure[0] != None:
				failures.append(deepcopy(failure))
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

	
