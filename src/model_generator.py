#
#	1. The field in the json file passed into generate_model must be all numbers except labels field (labels, topologyKey), which will be translated into numbers in process_labels. 
# 	   TODO: later if we pass yaml file, will add a gloabl translator, to translate all the string into unique number.
#
#

import json
from processing_default import *
from case_generator import *
import sys

index_starts_at_one = {"pods", "nodes", "d", "podTemplates", "deploymentTemplates"}

def find_index(key_to_value, l, v):
	for i in range(0, len(key_to_value)):
		if l in key_to_value[i]:
			for j in range(0, len(key_to_value[i][1])):
				if v == key_to_value[i][1][j]:
					print("[******] Converted: {" + str(l) + ", " + str(v) + "} : " + str(i) + ", " +str(j))
					return i, j

def find_key(key_to_value, l):
	for i in range(0, len(key_to_value)):
		if l in key_to_value[i]:
			return i


def replacing_labels(json_config, key_to_value):
	json_config["labelKeyValue"] = [-1 for i in range(len(key_to_value))]

	print("[****] Initilized labelKeyValue: ", json_config["labelKeyValue"])

	print("[****] Original labels:", json_config["labels"])
	for l in json_config["labels"]:
		cur_k, cur_v = find_index(key_to_value, l, json_config["labels"][l])
		json_config["labelKeyValue"][cur_k] = cur_v
	del json_config["labels"]
	print("[****] Replcaed labels:",json_config["labelKeyValue"])

# A pre-processor to process all the labels, converting each keys (including built-ins) into unique number, and all values for each key 
# would be assign a unique numbers (but don't need to be unique across keys). For now, we assume we our json file already got this post-processing result.
# Note that some labels can be shared across all objects (i.e. nodes, pods), some are only used for a particular object. 
# In our context, the labelKeyValue will consider all the labels, no matter it's shared across object or not. If some labels aren't defined in some objects, we will just give it a 0.
def process_labels(json_config):
	key_to_value = {}

	# Need to process three things: 1. labels in nodes, 2. labels in podTemplates for pods, 3. topologyKey and labels in topoSpreadConstraints
	for o in [json_config["setup"]["nodes"], json_config["setup"]["podTemplates"]]:
		for e in o:
			for l in e["labels"]:
				if l not in key_to_value:
					key_to_value[l] = set()
				key_to_value[l].add(e["labels"][l])

			if "numTopoSpreadConstraints" in e:
				for i in range(0, int(e["numTopoSpreadConstraints"])):
					topo_key = e["topoSpreadConstraints"][i]["topologyKey"]
					if topo_key not in key_to_value:
						key_to_value[topo_key] = set()
					cur_topo = e["topoSpreadConstraints"][i]
					for l in cur_topo["labels"]:
						if l not in key_to_value:
							key_to_value[l] = set()
						key_to_value[l].add(cur_topo["labels"][l])

	print("[****]", key_to_value)
	for k in key_to_value:
		key_to_value[k] = list(key_to_value[k])
	key_to_value = list(key_to_value.items())
	print("[****]", key_to_value)

	for o in json_config["setup"]["nodes"]:
		replacing_labels(o, key_to_value)

	for o in json_config["setup"]["podTemplates"]:
		replacing_labels(o, key_to_value)

		if "numTopoSpreadConstraints" in e:
			# processing this in a differnt way, because the label keys could be the same
			for i in range(0, int(o["numTopoSpreadConstraints"])):
				cur_topo = o["topoSpreadConstraints"][i]
				print("[*****] Original topo:", cur_topo)
				cur_topo["topologyKey"] = find_key(key_to_value, cur_topo["topologyKey"])
				cur_topo["numMatchedLabel"] = len(cur_topo["labels"])
				cur_topo["labelKey"] = []
				cur_topo["labelValue"] = []
				for l in cur_topo["labels"]:
					cur_k, cur_v = find_index(key_to_value, l, cur_topo["labels"][l])
					cur_topo["labelKey"].append(cur_k)
					cur_topo["labelValue"].append(cur_v)
				del cur_topo["labels"]
				print("[*****] Modified topo:", cur_topo)

	#print(json_config["setup"]["nodes"])
	#print(json_config["setup"]["podTemplates"])
	

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

	return s_init, len(json_config["pods"]), len(json_config["nodes"]), len(json_config["d"]), len(json_config["podTemplates"]), len(json_config["deploymentTemplates"])

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
			s_user_command += ("run " + c + "(" + str(json_config["userCommand"][c]) + ");\n")
			
	return s_user_command

def generate_model(json_config, pml_config, pml_main):
	userDefinedConstraints = check_for_completion_add_default(json_config)
	process_labels(json_config)

	s_init = ""
	s_init, pod_num, node_num, deployment_num, pt_num, dt_num = generate_init(json_config["setup"], s_init)

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
						   .replace("[$POD_TEMPLATE_NUM]", str(pt_num+2)) \
						   .replace("[$DEP_TEMPLATE_NUM]", str(dt_num+1)) \
						   .replace("[$userDefinedConstraints]", str(userDefinedConstraints))

	return pml_config, pml_main


def model_generator(file_base, case_id, scale):
	filename = file_base + "/temp/configs/" + case_id + "_" + scale + ".json"
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

if __name__ == '__main__':
	model_generator(sys.argv[1], sys.argv[2], sys.argv[3])


