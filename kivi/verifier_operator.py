# This module implements the verifier operator

import subprocess
import random
import datetime
import json

from util import *
from config import *
from model_generator import model_generator
from processing_default import default_intents
from result_parser import parse_pan_output, parse_spin_error_trail
from cases.case_generator import case_generator
from small_scale_finder import finding_smallest_scale, generate_case_json, str_setup

# The verifier operator that runs multiple verification cycles, each cycle look into one topology.
class VeriferOperator():
	def __init__(self, json_config, file_base, result_base_path, pml_base_path, case_name=None):
		# json_config contains the cluster setup.
		self.json_config = json_config
		self.file_base = file_base
		self.result_base_path = result_base_path
		self.pml_base_path = pml_base_path
		if case_name is not None:
			self.case_name = case_name

		self.log_level = args.verbose_level

		self.intent_groups = {"never":[], "loop":["loop"], "assert":["no_feasible_node", "kernel_panic", "checkOscillationReplicaNum", \
				"checkMinReplicas", "checkExpReplicas", "checkEvictionCycle", "checkBalanceNode"]}

		self.intents = ["no_feasible_node", "kernel_panic", "checkOscillationReplicaNum", \
				"checkMinReplicas", "checkExpReplicas", "checkEvictionCycle", "checkBalanceNode"]

		# set up the compile and runtime parameters for Spin and pan
		self.pan_runtime = ["-" + o.strip() for o in args.pan_runtime.split(",")]
		self.pan_compile = ['-o', 'pan', 'pan.c']
		self.pan_compile.extend(["-" + o.strip() for o in args.pan_compile.split(",")])
		if args.loop:
			self.pan_compile.append("-DNP")
			self.pan_runtime.append("-l")
		if args.random:
			if "-DT_RAND" not in self.pan_compile:
				self.pan_compile.append("-DT_RAND")
			if "-DP_RAND" not in self.pan_compile:
				self.pan_compile.append("-DP_RAND")
		logger.debug("pan_runtime:" + str(self.pan_runtime))
		logger.debug("pan_compile:" + str(self.pan_compile))
		logger.debug(args)

		# initialize intent group if there are multiple intents that needs to verify seperately. 
		self.add_default_intents(self.json_config)
		self.intent_group_list = self.analyze_divide_intents(json_config)

		self.failures = []

	def operator(self):
		if not args.original:
			all_setup, json_config_template = finding_smallest_scale(self.json_config, self.pml_base_path)

			# TODO: the following can be improved as using multi-core
			for s in all_setup:
				new_json_config, num_node, num_pod = generate_case_json(json_config_template, s)

				logger.critical("===========================")
				logger.critical("Working on setup: " + str_setup(s))

				new_failures = self.verify_one_setup(new_json_config)

				if len(new_failures) > 0:
					logger.critical("Failure found at scale " + str_setup(s))
					self.failures.extend(new_failures)
					if not args.all_violation:
						break

		else:
			new_failures = self.verify_one_setup(self.json_config)

			if len(new_failures) > 0:
				logger.info(str(len(new_failures)) + " failure found!")
				for failure in new_failures:
					failure_type = failure[0]
					if failure_type is not None:
						logger.info("\nError message: "+str(failure_type) + "\ntotal memory usage: " + str(failure[-2]) + "MB\nelapsed time: " + str(failure[-1])+"s\n")
						

				self.failures.extend(new_failures)

	def verify_one_setup(self,json_config):
		if len(self.intent_group_list) == 0:
			logger.critical("No intent defiend!")
			return []

		for intents in self.intent_group_list:
			# TODO: may need to process loop seperately. 
			cur_json_config = deepcopy(json_config)
			cur_json_config["intents"] = intents

			intents_str = ""
			for intent in intents:
				intents_str += intent["name"]+" "
			logger.critical("Working on the intents: "+intents_str)

			new_failures = self.verify_one_topology(cur_json_config, queue_size)
			if len(new_failures) > 0:
				logger.info("Failure found at intent " + str(intents))

			if not args.all_violation and len(new_failures) > 0:
				break

		return new_failures

	# TODO: add pan -a into the pipeline
	# TODO: keep stream the output from the ./pan, and if see "max search depth too small", we could just stop the execuation and adjust the running configs for pan
	def verify_one_topology(self,cur_json_config, queue_size):
		main_filename = model_generator(cur_json_config, self.pml_base_path, self.file_base + "/kivi/templates", queue_size_default=queue_size)

		success, stdout, stderr = run_script([self.file_base + '/libs/Spin/Src/spin', '-a', self.pml_base_path + "/" + main_filename], True)
		myprint(stdout, logger.debug)

		timeout = args.timeout if args.timeout is not None else default_timeout

		while True:
			success, stdout, stderr = run_script(['gcc'] + self.pan_compile, True)
			if args.timeout:
				success, stdout, stderr = run_script(['./pan']+self.pan_runtime, False, args.timeout)
			else:
				if args.random:
					success, stdout, stderr = run_script(['./pan']+self.pan_runtime, False, timeout)
				else:
					success, stdout, stderr = run_script(['./pan']+self.pan_runtime, False)

			# if args.file_debug > 0:
			# 	with open(self.result_base_path + "/raw_data/exec_" + self.case_name + "_" + str(queue_size), "w") as fr:
			# 		fr.write(stdout.decode())

			failure_type, failure_details, error_trail_name, total_mem, elapsed_time = parse_pan_output(stdout.decode())

			# if args.file_debug > 0:
			# 	with open(self.result_base_path + "/" + self.case_name + "_" + str(queue_size), "w") as fw:
			# 		fw.write(str(failure_type) + " " + str(total_mem) + " " + str(elapsed_time) + '\n')
			myprint(failure_details)

			result_log = ""
			if error_trail_name != None:
				success_error_trail, stdout, stderr = run_script(['./pan', '-r', error_trail_name], False)
				if args.file_debug > 0:
					with open(result_base_path + "/raw_data/error_" + case_name, "w") as fr:
						fr.write(stdout.decode())
				result_log, failure_details = parse_spin_error_trail(stdout.decode(), self.log_level, failure_type)
				myprint(result_log, logger.debug)
				if args.file_debug > 0:
					with open(result_base_path + "/" + case_name, "w") as fw:
						fw.write(result_log)

			if failure_type == "max search depth too small":
				for i in range(0, len(self.pan_runtime)):
					if "-m" in self.pan_runtime[i]:
						self.pan_runtime[i] = "-m" + str(int(self.pan_runtime[i][2:])*10)
						logger.critical("Adding more depth, now " + str(self.pan_runtime[i]))
						break

			elif failure_type == "VECTORSZ too small":
				for i in range(0, len(pan_compile)):
					if "DVECTORSZ" in pan_compile[i]:
						pan_compile[i] += "0"
						logger.critical("Adding more vector size, now "+str(self.pan_compile[i]))
						break

			elif len(failure_details.split("\n")) > 1 and "Queue is full!" in failure_details.split("\n")[1]:
				queue_size *= 2
				if queue_size > 500:
					logger.critical("Queue size exceed limit!")
					break

				logger.critical("trying queue size "+str(queue_size))
				main_filename = model_generator(cur_json_config, pml_base_path, file_base + "/kivi/templates", queue_size_default=queue_size)
				success, stdout, stderr = run_script([self.file_base + '/libs/Spin/Src/spin', '-a', self.pml_base_path + "/" + main_filename], True)
				myprint(stdout, logger.debug)

			elif (not success) and args.random:
				rand_count = 0
				if rand_count <= random_limit:
					rand = random.randint(1, 1000)
					rs_exist = False
					for i in range(0, len(self.pan_runtime)):
						if "-RS" in self.pan_runtime[i]:
							rs_exist = True
							self.pan_runtime[i] = "-RS"+str(rand)
					if not rs_exist:
						self.pan_runtime = self.pan_runtime + ['-RS'+str(rand)]
					rand_count += 1
				else:
					logger.critical("Too many tries on random. Timeout!!")
					break
			else:
				break

		new_failures = []

		if failure_type is not None:
			new_failures.append((failure_type, result_log, failure_details, total_mem, elapsed_time))

			#new_failures.append((failure_type, result_log, failure_details, total_mem, elapsed_time))

		return new_failures

	# intents can be seperated into subsets in this function.
	def analyze_divide_intents(self,json_config):
		new_intents = []

		all_intents = deepcopy(json_config["intents"])
		# first, the intents in different intent groups must be divided, as the are verified in different ways.
		group_to_intents = {}
		group_count = {}
		for k in self.intent_groups:
			group_count[k] = 0
		for intent in all_intents:
			# put all of the str into one group
			if isinstance(intent, str):
				if "str_group" not in group_to_intents:
					group_to_intents["str_group"] = []
				group_to_intents["str_group"].append(deepcopy(intent))
			else:
				for ig in self.intent_groups:
					if intent["name"] in self.intent_groups[ig]:
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

		return intent_group_list

	def compare_intents(self, i1, i2):
		if i1["name"] != i2["name"]:
			return False

		#not comparing para for now as default ones does not have it.
		return True

	def add_default_intents(self, json_config):
		for i in default_intents:
			exist = False
			if "intents" in json_config:
				for j_intent in json_config["intents"]:
					if self.compare_intents(i, j_intent):
						exist = True
				if exist:
					break
				json_config["intents"].append(deepcopy(i))
			else:
				json_config["intents"] = []
				json_config["intents"].append(deepcopy(i))

	def str_failures(self):
		msg = "========================\n"
		msg += str(len(self.failures)) + " failure(s) are found!\n"
		for i in range(0, len(self.failures)):
			msg += ("-----Failure #" + str(i+1) + "-----" + "\n")
			#msg += ("Issue: " + failures[i][0] + "\n")
			msg += ("Minimal example:" + "\n")
			msg += (self.failures[i][1] + "\n")

		return msg

	def failure_types(self):
		msg = ""
		for failure in self.failures:
			for intent in self.intents:
				if intent in failure[1]:
					msg += intent + " "
		return msg

