# This module implements the basic workflow of Kivi. 

import json
import math
import time

from util import *

from verifier_operator import VeriferOperator
from parser import parser
from cases.case_generator import case_generator
from model_generator import model_generator
from result_parser import parse_spin_error_trail
from small_scale_finder import template_generator

class Kivi():
	def __init__(self):
		pass
	
	def run(self):
		scale = args.scale
		# verify according to config files.
		if args.path:
			case_id = args.path.split("/")[-1]
			case_name = case_id

			# user_defined collects user's config for finding smallest example algorithm. 
			# If user does not define it, will return None and a default config will be given. 
			json_config, user_defined = parser(args.path)

			if not args.original:
				json_config = template_generator(json_config, user_defined)

		# verify against pre-defined use cases. 
		elif args.case:
			case_id = args.case
			case_name = case_id

			if args.original or args.simulation:	
				case_name = case_name + "_" + str(scale)
				json_config = case_generator(case_id, scale, filename=args.json_file_path)
			else:
				# it will include a special field -- userCommand, defines the upper and lower bound.
				json_config = case_generator(case_id, scale, from_template=True)

		else:
			logger.error("Unknown type of verifier!")

		file_base = sys_path
		pml_base_path, result_base_path = generate_dir(file_base, case_id, scale)
		
		if args.file_debug > 0:
			if args.original:
				with open(pml_base_path + "/" + case_id + ".json",'w') as f:
					json.dump(json_config, f, indent=4)
			else:
				with open(pml_base_path + "/" + case_id + "_template.json",'w') as f:
					json.dump(json_config, f, indent=4)

		if args.simulation:
			traces = self.simulation(json_config, file_base, pml_base_path)

		else:
			start = time.time()
			verifier_operator = VeriferOperator(json_config, file_base, result_base_path, pml_base_path, case_name)
			verifier_operator.operator()
			end = time.time()

			result_str = "Summary:\n"
			if len(verifier_operator.failures) == 0:
				result_str += "    No failure is found!\n"
			else:
				logger.critical(verifier_operator.str_failures())
				result_str += "    " + str(len(verifier_operator.failures)) + " failure(s) found!\n    Violating intent(s): " + verifier_operator.failure_types() + "\n"
			
			result_str += "    Elapsed time: " + str(round(end-start,2)) + " seconds\n"

			logger.critical(result_str)

	def simulation(self, json_config, file_base, pml_base_path):
		main_filename = model_generator(json_config, pml_base_path, file_base + "/kivi/templates")

		success, stdout, stderr = run_script([file_base + '/libs/Spin/Src/spin', pml_base_path + "/" + main_filename], True)
		#myprint(stdout, logger.debug)

		result_log, failure_details = parse_spin_error_trail(stdout.decode(), args.verbose_level)
		logger.critical("Simulation result:")
		myprint(result_log, logger.critical)
