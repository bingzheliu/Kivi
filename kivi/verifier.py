import json
import math

from util import *

from verifier_operators import verifier_operator
from parser import parser
from cases.case_generator import case_generator
from small_scale_finder import template_generator, get_case_temeplate


def verifier():
	scale = 0
	if args.path:
		case_id = args.path.split("/")[-1]
		case_name = case_id

		# user_defined collects user's config for finding smallest example algorithm. 
		# If user does not define it, will return None and a default config will be given. 
		json_config, user_defined = parser(args.path)

		if not args.original:
			json_config = template_generator(json_config, user_defined)

	elif args.case:
		case_id = args.case
		case_name = case_id

		if args.original:
			scale = args.scale		
			case_name = case_name + "_" + scale	
			json_config = case_generator(case_id, scale, args)
		else:
			json_config = get_case_temeplate(case_id)

	else:
		logger.critical("Unknown type of verifier!")

	file_base = sys_path
	pml_base_path, result_base_path = generate_dir(file_base, case_id, scale)
	
	if args.original:
		with open(pml_base_path + "/" + case_id + ".json",'w') as f:
			json.dump(json_config, f, indent=4)
	else:
		with open(pml_base_path + "/" + case_id + "_template.json",'w') as f:
			json.dump(json_config, f, indent=4)

	failures = verifier_operator(json_config, case_name, file_base, result_base_path, pml_base_path)

	msg = str(len(failures)) + " failure(s) are found!\n"
	for i in range(0, len(failures)):
		msg += ("-----Failure #" + str(i+1) + "-----" + "\n")
		#msg += ("Issue: " + failures[i][0] + "\n")
		msg += ("Minimal example:" + "\n")
		msg += (failures[i][1] + "\n")

	logger.critical(msg)

# temp/case_id stores the pml and json file. For cases with different scale, a seperate dir will be generate for each scale
# temp/case_id/min_exp stores the json file for each scale that are tested. 
# result/case_id stores the runtime result. 
def generate_dir(file_base, case_id, scale):
	my_mkdir(file_base+"/temp/"+ str(case_id))
	if scale == 0:
		pml_base_path = file_base + "/temp/" + str(case_id) 
	else:
		pml_base_path = file_base + "/temp/" + str(case_id) + "/" + str(scale)
	my_mkdir(pml_base_path)
	my_mkdir(pml_base_path+"/min_exp")

	result_base_path = file_base + "/results/" + str(case_id)
	my_mkdir(file_base + "/results")
	my_mkdir(result_base_path)
	my_mkdir(result_base_path + "/raw_data")
	
	return pml_base_path, result_base_path

# if __name__ == '__main__':
# 	verifier()

