#
#	1. The field in the json file passed into generate_model must be all numbers except labels field (labels, topologyKey), which will be translated into numbers in process_labels. 
# 	   TODO: later if we pass yaml file, will add a gloabl translator, to translate all the string into unique number.
#
#

import json
from processing_default import *
from case_generator import *
import sys

from util import *


index_starts_at_one = {"pods", "nodes", "d", "podTemplates", "deploymentTemplates"}

def find_index(key_to_value, l, v):
	for i in range(0, len(key_to_value)):
		if l in key_to_value[i]:
			for j in range(0, len(key_to_value[i][1])):
				if v == key_to_value[i][1][j]:
					model_logger.debug("Converted: {" + str(l) + ", " + str(v) + "} : " + str(i) + ", " +str(j))
					return i, j

def find_key(key_to_value, l):
	for i in range(0, len(key_to_value)):
		if l in key_to_value[i]:
			return i


def replacing_labels(json_config, key_to_value):
	json_config["labelKeyValue"] = [-1 for i in range(len(key_to_value))]

	model_logger.debug("Initilized labelKeyValue: ")
	model_logger.debug(json_config["labelKeyValue"])

	model_logger.debug("Original labels:")
	model_logger.debug(json_config["labels"])
	for l in json_config["labels"]:
		cur_k, cur_v = find_index(key_to_value, l, json_config["labels"][l])
		json_config["labelKeyValue"][cur_k] = cur_v
	del json_config["labels"]
	model_logger.debug("Replcaed labels:")
	model_logger.debug(json_config["labelKeyValue"])

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

	model_logger.debug(key_to_value)
	max_label = len(key_to_value)
	max_value = 0
	for k in key_to_value:
		if len(key_to_value[k]) > max_value:
			max_value = len(key_to_value[k])

	#print(max_label, max_value, key_to_value)

	for k in key_to_value:
		key_to_value[k] = list(key_to_value[k])
	key_to_value = list(key_to_value.items())
	model_logger.debug(key_to_value)

	for o in json_config["setup"]["nodes"]:
		replacing_labels(o, key_to_value)

	for o in json_config["setup"]["podTemplates"]:
		replacing_labels(o, key_to_value)

		if "numTopoSpreadConstraints" in e:
			# processing this in a differnt way, because the label keys could be the same
			for i in range(0, int(o["numTopoSpreadConstraints"])):
				cur_topo = o["topoSpreadConstraints"][i]
				model_logger.debug("Original topo:", cur_topo)
				cur_topo["topologyKey"] = find_key(key_to_value, cur_topo["topologyKey"])
				cur_topo["numMatchedLabel"] = len(cur_topo["labels"])
				cur_topo["labelKey"] = []
				cur_topo["labelValue"] = []
				for l in cur_topo["labels"]:
					cur_k, cur_v = find_index(key_to_value, l, cur_topo["labels"][l])
					cur_topo["labelKey"].append(cur_k)
					cur_topo["labelValue"].append(cur_v)
				del cur_topo["labels"]
				model_logger.debug("Modified topo:", cur_topo)

	#print(json_config["setup"]["nodes"])
	#print(json_config["setup"]["podTemplates"])

	return max_label, max_value
	

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
				model_logger.critical("Unknown types of data structure!")

	return s_init

def generate_init(json_config, s_init):
	s_init = generate_init_auto("", json_config, s_init)

	return s_init, len(json_config["pods"]), len(json_config["nodes"]), len(json_config["d"]), len(json_config["podTemplates"]), len(json_config["deploymentTemplates"])

def generate_controllers_events(json_config, s_proc):
	# TODO: the json may contains the configs of these controllers that can override the default configs. Need to process them.
	if "controllers" in json_config:
		for c in json_config["controllers"]:
			if c not in default_controllers:
				s_proc += ("run " + c + "();\n")

	if "events" in json_config:
		for c in json_config["events"]:
			if c in event_default_str:
				s_proc += event_default_str[c]
			else:
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

def generate_intent(json_config, s_intentscheck_intent, s_main_intent):
	if "intents" in json_config:
		for intent in json_config["intents"]:
			if "run" in intent:
				s_main_intent += (intent + "\n")
			else:
				s_intentscheck_intent += (intent + "\n")

	return s_intentscheck_intent, s_main_intent

def generate_other_event(json_config, s_main_event, pml_event):
	# Processing pod CPU change pattern
	s_cpu_change = ""
	s_cpu_change_stmt = "      ::  pods[[$i]].status == 1 && pods[[$i]].curCpuIndex < podTemplates[pods[[$i]].podTemplateId].maxCpuChange -> \n       podCpuChangeWithPatternExec([$i])\n"
	for tp in json_config["setup"]["podTemplates"]:
		if tp["maxCpuChange"] > 0:
			# Becuase some pods may be up/changed later, so we need to put every pod onto the check...
			for i in range(1, len(json_config["setup"]["pods"])+1):
				s_cpu_change += s_cpu_change_stmt.replace("[$i]", str(i))
			break
	if len(s_cpu_change) > 0:
		pml_event = pml_event.replace("[$podCpuChangeWithPattern]", s_cpu_change)
		s_main_event += ("run podCpuChangeWithPattern()\n")
	else:
		pml_event = pml_event.replace("[$podCpuChangeWithPattern]", ":: true->break")


	return s_main_event, pml_event

# TODO: following two functions can be more generalized
def get_max_num_metrics(json_config):
	max_num_metrics = 1
	for d in json_config["setup"]["d"]:
		if "hpaSpec" in d:
			if d["hpaSpec"]["numMetrics"] > max_num_metrics:
				max_num_metrics = d["hpaSpec"]["numMetrics"]
	return max_num_metrics

def get_max_pod_template(json_config):
	max_no_schedule_node = 1
	max_no_prefer_schedule_node = 1
	max_affinity_rules = 1
	max_matched_node = 1
	max_topo_con = 1
	max_cpu_pattern = 1
	for pt in json_config["setup"]["podTemplates"]:
		if pt["numRules"] > max_affinity_rules:
			max_affinity_rules = pt["numRules"]
		if pt["numNoScheduleNode"] > max_no_schedule_node:
			max_no_schedule_node = pt["numNoScheduleNode"]
		if pt["numPreferNoScheduleNode"] > max_no_prefer_schedule_node:
			max_no_prefer_schedule_node = pt["numPreferNoScheduleNode"]
		if int(pt["numRules"]) > 0:
			for ar in pt["affinityRules"]:
				if ar["numMatchedNode"] > max_matched_node:
					max_matched_node = ar["numMatchedNode"]
		if pt["numTopoSpreadConstraints"] > max_topo_con:
			max_topo_con = pt["numTopoSpreadConstraints"]
		if pt["maxCpuChange"] > max_cpu_pattern:
			max_cpu_pattern = pt["maxCpuChange"]

	return max_no_schedule_node, max_no_prefer_schedule_node, max_affinity_rules, max_matched_node, max_topo_con, max_cpu_pattern

def generate_model(json_config, pml_config, pml_main, pml_intent, pml_event, config_filename, intent_filename, event_filename, file_base):
	userDefinedConstraints = check_for_completion_add_default(json_config)
	max_label, max_value = process_labels(json_config)

	s_init = ""
	s_init, pod_num, node_num, deployment_num, pt_num, dt_num = generate_init(json_config["setup"], s_init)

	s_proc = ""
	s_proc = generate_controllers_events(json_config, s_proc)

	s_user_command = ""
	s_user_command = generate_user_command(json_config, s_user_command)

	s_intentscheck_intent = ""
	s_main_intent = ""
	s_intentscheck_intent, s_main_intent = generate_intent(json_config, s_intentscheck_intent, s_main_intent)

	s_main_event = ""
	s_main_event, pml_event = generate_other_event(json_config, s_main_event, pml_event)

	#print(s_proc, s_user_command)
	
	pml_main = pml_main.replace("[$INIT_SETUP]", s_init) \
					   .replace("[$CONTROLLERS]", s_proc) \
					   .replace("[$USER_COMMAND]", s_user_command) \
					   .replace("[$CONFIG_FILENAME]", str(config_filename)) \
					   .replace("[$INTENT_FILENAME]", str(intent_filename)) \
					   .replace("[$EVENT_FILENAME]", str(event_filename)) \
					   .replace("[$EVENT]", str(s_main_event)) \
					   .replace("[$FILE_BASE]", str(file_base)) \
					   .replace("[$INTENTS]", str(s_main_intent)) 

	max_no_schedule_node, max_no_prefer_schedule_node, max_affinity_rules, max_matched_node, max_topo_con, max_cpu_pattern = get_max_pod_template(json_config)

	pml_config = pml_config.replace("[$NODE_NUM]", str(node_num)) \
						   .replace("[$POD_NUM]", str(pod_num)) \
						   .replace("[$DEP_NUM]", str(deployment_num)) \
						   .replace("[$POD_TEMPLATE_NUM]", str(pt_num)) \
						   .replace("[$DEP_TEMPLATE_NUM]", str(dt_num)) \
						   .replace("[$userDefinedConstraints]", str(userDefinedConstraints)) \
					   	   .replace("[$MAX_LABEL]", str(max_label+1)) \
					   	   .replace("[$MAX_VALUE]", str(max_value+1)) \
					   	   .replace("[$DEP_QUEUE]", str(deployment_num*2)) \
					   	   .replace("[$POD_QUEUE]", str(pod_num*2)) \
					   	   .replace("[$NODE_QUEUE]", str(node_num*2)) \
					   	   .replace("[$MAX_NUM_METRICS]", str(get_max_num_metrics(json_config))) \
					   	   .replace("[$MAX_NO_SCHEDULE_NODE]", str(max_no_schedule_node)) \
					   	   .replace("[$MAX_PEFER_NO_CHEDULE_NODE]", str(max_no_prefer_schedule_node)) \
					   	   .replace("[$MAX_AFFINITY_RULE]", str(max_affinity_rules)) \
					   	   .replace("[$MAX_MATCHED_NODE]", str(max_matched_node)) \
					   	   .replace("[$MAX_TOPO_CON]", str(max_topo_con)) \
					   	   .replace("[$MAX_CPU_PATTERN]", str(max_cpu_pattern)) 


						   #.replace("[$MAX_POD]", str(pod_num+3)) \
						   #.replace("[$MAX_NODE]", str(node_num+3)) \
						   #.replace("[$MAX_DEPLOYMENT]", str(deployment_num+3)) \

	pml_intent += s_intentscheck_intent
						   

	return pml_config, pml_main, pml_intent, pml_event


def model_generator(pml_base_path, file_base, case_id, scale):
	config_filename = pml_base_path + "/configs/" + case_id + "_" + scale + ".json"
	case_generator(config_filename, case_id, scale)

	with open(config_filename) as f:
		json_config = json.load(f)

	with open(file_base + "/templates/config.pml") as f:
		pml_config = f.read()

	with open(file_base + "/templates/main.pml") as f:
		pml_main = f.read()

	with open(file_base + "/templates/intentsCheck.pml") as f:
		pml_intent = f.read()

	with open(file_base + "/templates/eventGenerate.pml") as f:
		pml_event = f.read()

	config_filename = "config_" + case_id + "_" + scale + ".pml"
	intent_filename = "intentsCheck_" + case_id + "_" + scale + ".pml"
	event_filename = "event_" + case_id + "_" + scale + ".pml"
	pml_config, pml_main, pml_intent, pml_event = generate_model(json_config, pml_config, pml_main, pml_intent, pml_event, config_filename, intent_filename, event_filename, file_base)
	
	with open(pml_base_path + "/" + config_filename, "w") as f:
		f.write(pml_config)

	main_filename = "main_" + case_id + "_" + scale + ".pml"
	with open(pml_base_path + "/" +  main_filename, "w") as f:
		f.write(pml_main)

	with open(pml_base_path + "/" +  intent_filename, "w") as f:
		f.write(pml_intent)

	with open(pml_base_path + "/" +  event_filename, "w") as f:
		f.write(pml_event)

	return main_filename

if __name__ == '__main__':
	model_generator(sys.argv[1], sys.argv[2], sys.argv[3])


