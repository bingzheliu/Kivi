import json
from processing_default import *
from case_generator import *

index_starts_at_one = {"pods", "nodes", "d", "podTemplates"}

def generate_init_auto(cur_prefix, cur_json, s_init):
	if isinstance(cur_json, int) or isinstance(cur_json, str):
		s_init += (cur_prefix + " = " + str(cur_json) + "; \n")
		return s_init

	if cur_prefix != "":
		cur_prefix = cur_prefix + "."
	
	for e in cur_json:
		if isinstance(cur_json[e], int) or isinstance(cur_json[e], str):
			s_init += (cur_prefix + str(e) + " = " + str(cur_json[e]) + "; \n")
		else:
			if isinstance(cur_json[e], list):
				i = 0
				for i in range(0, len(cur_json[e])):
					index = i
					if e in index_starts_at_one:
						index = i + 1
						
					next_prefix = cur_prefix + e + "[" + str(index) + "]"
					s_init = generate_init_auto(next_prefix, cur_json[e][i], s_init)
			elif isinstance(cur_json[e], dict):
				next_prefix = cur_prefix + e
				s_init = generate_init_auto(next_prefix, cur_json[e], s_init)

			else:
				print("Unknown types of data structure!")

	return s_init

def generate_init(json_config, s_init):
	s_init = generate_init_auto("", json_config, s_init)

	return s_init, len(json_config["pods"]), len(json_config["nodes"]), len(json_config["d"]), len(json_config["podTemplates"])

def generate_controllers_events(json_config, s_proc):
	if "controllers" in json_config:
		for c in json_config["controllers"]:
			if c not in default_controllers:
				s_proc += ("run " + c + "();\n")

	if "events" in json_config:
		for c in json_config["events"]:
			c_para = ""
			for para in default_parameter_order[c]:
				#print(c, para, c_para)
				c_para += (str(json_config["events"][c][para]) + ",")
			c_para = c_para[0:-1]
			#print(c_para)
			s_proc += ("run " + c + "(" + c_para + ");\n")

	return s_proc

def generate_user_command(json_config, s_user_command):
	if "userCommand" in json_config:
		for c in json_config["userCommand"]:
			s_user_command += ("run " + str(c) + "(" + str(json_config["userCommand"][c]) + ");\n")
			
	return s_user_command

def generate_model(json_config, pml_config, pml_main):
	check_for_completion_add_default(json_config)

	s_init = ""
	s_init, pod_num, node_num, deployment_num, pt_num = generate_init(json_config["setup"], s_init)

	s_proc = ""
	s_proc = generate_controllers_events(json_config, s_proc)

	s_user_command = ""
	s_user_command = generate_user_command(json_config, s_user_command)

	#print(s_proc, s_user_command)
	
	pml_main = pml_main.replace("[$INIT_SETUP]", s_init) \
					   .replace("[$CONTROLLERS]", s_proc) \
					   .replace("[$USER_COMMAND]", s_user_command)

	pml_config = pml_config.replace("[$MAX_POD]", str(pod_num+3)) \
						   .replace("[$NODE_NUM]", str(node_num)) \
						   .replace("[$POD_NUM]", str(pod_num)) \
						   .replace("[$MAX_NODE]", str(node_num+3)) \
						   .replace("[$MAX_DEPLOYMENT]", str(deployment_num+3)) \
						   .replace("[$DEP_NUM]", str(deployment_num)) \
						   .replace("[$POD_TEMPLATE_NUM]", str(pt_num+2)) 

	return pml_config, pml_main


if __name__ == '__main__':
	file_base = sys.argv[1]
	case_id = sys.argv[2]
	scale = sys.argv[3]

	filename = file_base + "/temp/configs/" + str(sys.argv[2]) + "_" + str(sys.argv[3]) + ".json"
	case_generator(filename, case_id, scale)

	with open(filename) as f:
		json_config = json.load(f)

	with open(file_base + "/templates/config.pml") as f:
		pml_config = f.read()

	with open(file_base + "/templates/main.pml") as f:
		pml_main = f.read()

	pml_config, pml_main = generate_model(json_config, pml_config, pml_main)

	with open(file_base + "/temp/config.pml", "w") as f:
		f.write(pml_config)

	with open(file_base + "/temp/main.pml", "w") as f:
		f.write(pml_main)


