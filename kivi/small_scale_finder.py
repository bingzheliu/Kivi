#	This module implements part of the scaling algorithm. It finds all the scaled setup that need to verify for the given cluster setup.
# 	finding_smallest_scale is called by the verifier operator to generate all the setup. 
#	generate_case_json is called by the verifier operator to generate the json file from a setup, which will be sent to model generator to generate the model.
#	template_generator is used to generate template from an existing k8s logs

import math
import json
from copy import deepcopy

from util import *
from config import resource_difference_tolerance

# This is not currently used for our cases, only for extracting from cluster logs.
# minHPAReplicas is used to adjust the HPA maxReplicas in the propotion mode
user_defined_default = {"nodes_default" : {"maxSize":10, "minSize":1, "ScaleType":"proportion"}, \
						"d_default" : {"maxSize":10, "minSize":2, "ScaleType":"proportion", "minHPAReplicas":6}}

equal_templates = {"nodes":["cpu", "memory", "cpuLeft", "memLeft", "status", "labels", "taint"], "d":["podTemplateId", "hpaSpec"]}

# definition of userDefined
# {
#   // a list of different types of nodes;
#   // different types: total resources, left resources after deduct related pods, labels, status  	
# 	"nodeTypes": [{"templates":..,
#				   "minSize":..,         // the min number of nodes for this type
#				   "maxSize":..,			// the max number of nodes for this type
#				   "propotion":..,		    // the relative proprotion against other type of nodes		
#				 },..
#			     ]  
#	"nodeScaleType": "propotion" or "free"  // Define scale up behavior. "propotion": scale up propotionally to each other; "free": ignore its relativeness
#	
#	// a list of different types of deployments;
#	// different types: podTemplateId, hpaSpec
# 	"dTypes": 	 [{"templates":..,			// podTemplateId, hpaSpec, status, name
#				   "minSize":..,         // the min number of pods for this type
#				   "maxSize":..,			// the max number of pods for this type
#				   "propotion":..,		    // the relative proprotion against other type of deployments, may not be very useful if deployments are very different	
#				   "proportionHPA":.., 		// total_nodes*proportionHPA + setup_basic_d_number is the max_replicas for HPAspec, maxReplicas may not be the same as the specReplicas, typicially larger.
#				   "propotionNodes":..,     // the relative proprotion against total nodes, so the upper bound of deployments per setup can be bounded by the number of nodes.
#				  },..
#			     ]  		
#   "dScaleType": "proportion" or "free"	?
# }

def finding_smallest_scale(json_config, pml_base_path, sort_favor="nodes"):
	all_setup = generate_list_setup(json_config)
#	print(all_setup)
	if sort_favor == "nodes":
		all_setup.sort(key = sort_setup_node)
	if sort_favor == "all":
		all_setup.sort(key = sort_setup_all)
	#print(all_setup)

	if args.file_debug > 2:
		count = 0
		for s in all_setup:
			new_json_config, num_node, num_pod = generate_case_json(json_config, s)
			config_template_filename = pml_base_path + "/min_exp/" + str(count) + "_" + str(num_node) + "_" + str(num_pod) + ".json"
			count += 1

			with open(config_template_filename,'w') as f:
				json.dump(new_json_config, f, indent=4)

	return all_setup, json_config

# Generating templates from a running cluster log, which does not have types defined:
# In this mode, user can't define the upper bound and lower bound of their types, as they don't know this in advance. 
# Instead, they can give us a default bound for all nodes, and a default for all deployments.
# Anything defined in the maxReplicas and minReplicas in HPA or sepcReplicas will only be used as a proptional factor when scale up propotionally
# If user choose the propotion, the propotion will be set according the current proption of node and pods
def template_generator(json_config, user_defined=None):
	#print(json.dumps(json_config, indent=2))
	if user_defined is None:
		user_defined = user_defined_default

	json_config["userDefined"] = {}

	json_config = deduct_cpu_nodes(json_config)

	for t in ["nodes", "d"]:
		type_setup = []
		count = []
		max_count_replicas = []
		min_count_replicas = []
		spec_replicas = []
		for n in json_config["setup"][t]:
			new_flag = True
			# if t == "d":
			# 	cur_max = find_max_replicas_d(n)

			for i in range(0, len(type_setup)):
				if compare_template(n, type_setup[i]["template"], equal_templates[t]):
					count[i] += 1
					new_flag = False
					if t == "d":
						if "hpaSpec" in n: 
							max_count_replicas[i] = max(n["hpaSpec"]["maxReplicas"], max_count_replicas[i])
							min_count_replicas[i] = min(n["hpaSpec"]["minReplicas"], min_count_replicas[i])
						else:
							max_count_replicas[i] = max(n["specReplicas"], max_count_replicas[i])
							min_count_replicas[i] = min(n["specReplicas"], min_count_replicas[i])
						spec_replicas[i] = max(n["specReplicas"], spec_replicas[i])
					break

			if new_flag:
				new_type = {}
				new_type["template"] = {}
				assign_template(n, new_type["template"], equal_templates[t])
				if t == "nodes":
					# new_type["template"]["cpuLeft"] = n["cpu"]
					# new_type["template"]["memLeft"] = n["memory"]
					new_type["template"]["numPod"] = 0
				if t == "d":
					new_type["template"]["status"] = 0
					if "hpaSpec" in n:
						max_count_replicas.append(n["hpaSpec"]["maxReplicas"])
						min_count_replicas.append(n["hpaSpec"]["minReplicas"])
					else:
						max_count_replicas.append(n["specReplicas"])
						min_count_replicas.append(n["specReplicas"])
					spec_replicas.append(n["specReplicas"])
				new_type["template"]["name"] = n["name"]
				# Now all types have the same number of upper and lower if extract from cluster log; but it can actually be anything if user directly define the templates 
				new_type["minSize"] = user_defined[t+"_default"]["minSize"]
				new_type["maxSize"] = user_defined[t+"_default"]["maxSize"]
				if "minHPAReplicas" in user_defined[t+"_default"]:
					new_type["minHPAReplicas"] = user_defined[t+"_default"]["minHPAReplicas"]
					max_count_replicas[-1] = max(new_type["minHPAReplicas"], max_count_replicas[-1])
				if "HPAfactor" in user_defined[t+"_default"]:
					new_type["HPAfactor"] = user_defined[t+"_default"]["HPAfactor"]
				# propotion == 0 if nodeScaleType is free
				new_type["proportion"] = 0
				type_setup.append(new_type)
				count.append(1)

		propotion = get_propotion(count)
		for i in range(0, len(type_setup)):
			if user_defined[t+"_default"]["ScaleType"] == "proportion":
				type_setup[i]["proportion"] = propotion[i]
				if t == "d":
					#type_setup[i]["proportionHPA"] = user_defined[t+"_default"]["proportionHPA"]
					if "hpaSpec" in type_setup[i]["template"]:
						type_setup[i]["proportionNodeMin"] = min_count_replicas[i]*1.0/len(json_config["setup"]["nodes"])
						type_setup[i]["proportionNodeMax"] = max_count_replicas[i]*1.0/len(json_config["setup"]["nodes"])
					type_setup[i]["proportionNodeSpec"] = spec_replicas[i]*1.0/len(json_config["setup"]["nodes"])
					#type_setup[i]["maxSize"] = max_count_replicas[i]

			if user_defined[t+"_default"]["ScaleType"] == "free":
				# User can define their own alpha
				if t == "d" and "maxSizeNode" in user_defined[t+"_default"] :
					type_setup[i]["maxSizeNode"] = user_defined[t+"_default"]["maxSizeNode"]
			# if t == "nodes":
			# 	type_setup[i]["maxSize"] = count[i]

		json_config["userDefined"][t+"Types"] = deepcopy(type_setup)
		json_config["userDefined"][t+"ScaleType"] = user_defined[t+"_default"]["ScaleType"]

	if "max_pod_per_node" in user_defined:
		json_config["userDefined"]["max_pod_per_node"] = user_defined["max_pod_per_node"]

	json_config["setup"].pop("d")
	json_config["setup"].pop("pods")
	json_config["setup"].pop("nodes")

	logger.debug(json.dumps(json_config, indent=2))

	return json_config

def generate_case_json(json_config, cur_setup):
	new_json_config = deepcopy(json_config)
	new_json_config.pop("userDefined")

	total_nodes = 0
	cur_id = 0
	new_json_config["setup"]["nodes"] = []
	for i in range(0, len(json_config["userDefined"]["nodesTypes"])):
		for j in range(0, cur_setup["nodes"][i]):
			cur_node = deepcopy(json_config["userDefined"]["nodesTypes"][i]["template"])
			cur_node["id"] = cur_id
			#if "name" not in cur_node:
			cur_node["name"] = cur_id
			cur_id += 1

			new_json_config["setup"]["nodes"].append(cur_node)
			total_nodes += 1

	new_json_config["setup"]["d"] = []
	new_json_config["setup"]["pods"] = []
	if "userCommand" not in new_json_config:
		new_json_config["userCommand"] = []

	cur_d_id = 1
	for i in range(0, len(json_config["userDefined"]["dTypes"])):		
		cur_d_json = json_config["userDefined"]["dTypes"][i]
		d = deepcopy(json_config["userDefined"]["dTypes"][i]["template"])
		if json_config["userDefined"]["dScaleType"] == "propotion":
			cur_spec = adjust_replicas(min(cur_setup["d"][i], math.ceil(total_nodes*cur_d_json["proportionNodeSpec"])), cur_d_json)
		else:
			cur_spec = adjust_replicas(cur_setup["d"][i], cur_d_json)
			# eliminate the trivial failure cases.
			if "max_pod_per_node" in json_config["userDefined"]:
				cur_spec = min(cur_spec, json_config["userDefined"]["max_pod_per_node"]*total_nodes)
			
		d["id"] = cur_id
		if "name" not in d:
			d["name"] = cur_id
		cur_id += 1

		d["curVersion"] = 0
		d["replicaSets"] = []

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = cur_d_id
		rp["replicas"] = 0
		rp["specReplicas"] = cur_spec
		rp["version"] = 0
		rp["podIds"] = []
		d["replicaSets"].append(rp)

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = cur_d_id
		d["replicaSets"].append(rp)

		d["specReplicas"] = cur_spec
		d["replicas"] = 0

		max_replicas = d["specReplicas"]
		if "hpaSpec" in d:
			if d["hpaSpec"]["isEnabled"] == 1:
				if json_config["userDefined"]["dScaleType"] == "propotion":
					d["hpaSpec"]["minReplicas"] = adjust_replicas(min(math.ceil(total_nodes*cur_d_json["proportionNodeMin"]), math.floor(cur_setup["d"][i]*1.0*cur_d_json["proportionNodeMin"]/cur_d_json["proportionNodeSpec"])), cur_d_json)
					d["hpaSpec"]["maxReplicas"] = adjust_replicas(max(cur_d_json["minHPAReplicas"], min(math.ceil(total_nodes*cur_d_json["proportionNodeMax"]), math.ceil(cur_setup["d"][i]*1.0*cur_d_json["proportionNodeMax"]/cur_d_json["proportionNodeSpec"]))), cur_d_json)
				else:
					# TBC after clear about heatmap
					d["hpaSpec"]["minReplicas"] = cur_spec
					# This defines to set the HPA max propotional to the specReplicas, and it must exist for free style for now.
					d["hpaSpec"]["maxReplicas"] = cur_spec*cur_d_json["HPAfactor"]
					if "max_pod_per_node" in json_config["userDefined"]:
						d["hpaSpec"]["maxReplicas"] = min(d["hpaSpec"]["maxReplicas"], json_config["userDefined"]["max_pod_per_node"]*total_nodes)
				max_replicas = max(max_replicas, d["hpaSpec"]["maxReplicas"])
		new_json_config["setup"]["d"].append(d)

		cur_json_uc = {}
		cur_json_uc["name"] = "createTargetDeployment"
		cur_json_uc["para"] = cur_d_id
		cur_json_uc["first"] = 1
		new_json_config["userCommand"].append(cur_json_uc)

		cur_d_id += 1

		for j in range(0, max_replicas):
			cur_pod = {}
			cur_pod["id"] = cur_id
			cur_id += 1
			
			cur_pod["status"] = 0
			new_json_config["setup"]["pods"].append(cur_pod)

	#print(json.dumps(new_json_config, indent=2))

	return new_json_config, len(new_json_config["setup"]["nodes"]), len(new_json_config["setup"]["pods"]) 

# TODO
# 1. may need to process deploymentTemplates deploymentTemplates.
# 2. merge the applyDeployment related events
def compare_field(t1, t2, field):
	if field in ["cpu", "memory", "memLeft", "cpuLeft"]:
		return math.abs(t1-t2) <= resource_difference_tolerance

	return t1 == t2

def compare_template(t1, t2, field):
	for f in field:
		if f in t1:
			if isinstance(t1[f], dict):
				for e in t1[f]:
					if not compare_field(t1[f][e], t2[f][e], field):
						return False

			else:
				if f not in t2 or (not compare_field(t1[f], t2[f], field)):
					return False
		else:
			if f in t2:
				return False
		
	return True

#t2 = t1
def assign_template(t1, t2, field):
	for f in field:
		if f in t1:
			if isinstance(t1[f], dict):
				t2[f] = {}
				for e in t1[f]:
					t2[f][e] = t1[f][e]
			else:
				t2[f] = t1[f]

def get_propotion(count):
	min_count = count[0]
	propotion = [0]*len(count)

	for i in range(0, len(count)):
		if count[i] < min_count:
			min_count = count[i]

	for i in range(0, len(count)):
		propotion[i] = count[i]*1.0/min_count

	return propotion

def find_max_replicas_d(d):
	max_replicas = 0
	if d["specReplicas"] > max_replicas:
		max_replicas = d["specReplicas"]
	if d["replicas"] > max_replicas:
		max_replicas = d["replicas"]
	if "hpaSpec" in d and d["hpaSpec"]["maxReplicas"] > max_replicas:
		max_replicas = d["hpaSpec"]["maxReplicas"]

	return max_replicas

# remove all the pod cpu and memory usage from the nodes, so that nodes show its origional resources without the deployments
def deduct_cpu_nodes(json_config):
	for p in json_config["setup"]["pods"]:
		if "loc" in p and p["status"] != 0 and p["loc"] > 0:
			n = json_config["setup"]["nodes"][p["loc"]-1]
			n["cpuLeft"] = n["cpuLeft"]+p["cpu"]
			n["memLeft"] = n["memLeft"]+p["memory"]
			n["numPod"] -= 1

	return json_config

def adjust_replicas(replicas, json_config_cur):
	if replicas > json_config_cur["maxSize"]:
		replicas = json_config_cur["maxSize"]
	elif replicas < json_config_cur["minSize"]:
		replicas = json_config_cur["minSize"]

	return replicas

# Need to smartly set the boundary, otherwise it can take longer time. Now 7 is extracted the maxium number of pods that cause the problem
def get_next_num(j):
	if args.fast_find == 1:
		if j < 7:
			j += 1
		else:
			j = j+2
	else:
		j += 1

	return j

def check_duplicate(all_setup, cur_setup):
	for setup in all_setup:
		flag = True
		for t in setup:
			for n in setup[t]:
				if cur_setup[t][n] != setup[t][n]:
					flag = False 
					break
			if not flag:
				break
		if flag:
			return True

	return False

def generate_list_setup_dfs(json_config, i, cur_type, cur_setup, all_setup, count, cur_base=None):
	if cur_type == "nodes" and i == len(json_config["userDefined"]["nodesTypes"]):
		if count["nodes"] == 0:
			return 
		generate_list_setup_dfs(json_config, 0, "d", cur_setup, all_setup, count, cur_base)
		return
	if cur_type == "d" and i == len(json_config["userDefined"]["dTypes"]):
		if count["nodes"] == 0 or count["d"] == 0:
			return 
		if not check_duplicate(all_setup, cur_setup):
			all_setup.append(deepcopy(cur_setup))
		#generate_case_json(cur_setup, json_config)
		return

	cur_json_config = json_config["userDefined"][cur_type+"Types"][i]
	if json_config["userDefined"][cur_type+"ScaleType"] == "proportion":
		j = math.ceil(cur_base[cur_type] * cur_json_config["proportion"])
		if j < cur_json_config["minSize"]:
			j = cur_json_config["minSize"]
		if j > cur_json_config["maxSize"]:
			j = cur_json_config["maxSize"]

		cur_setup[cur_type][i] = j
		count[cur_type] += j
		generate_list_setup_dfs(json_config, i+1, cur_type, cur_setup, all_setup, count, cur_base)

	elif json_config["userDefined"][cur_type+"ScaleType"] == "free":
		j = cur_json_config["minSize"]
		while (j <= cur_json_config["maxSize"]):
			if (cur_type == "d" and (j > (confident_pod_size_factor*count["nodes"]) or j > json_config["userDefined"]["max_pod_per_node"]*count["nodes"])):
				break
			#print(cur_type, j, confident_node_size)
			if (cur_type == "nodes" and j  > confident_node_size):
				break
			# if (cur_type == "d" and j > (count["nodes"] * cur_json_config["proportionNode"])):
			# 	break
			cur_setup[cur_type][i] = j
			count[cur_type] += j
			generate_list_setup_dfs(json_config, i+1, cur_type, cur_setup, all_setup, count, cur_base)
			count[cur_type] -= j
			j = get_next_num(j)

	else:
		logger.critical("Unknown scaling type for " + cur_type + "!")
		return None

def get_max_base_propotions(json_config, cur_type):
	cur_max = 0
	for n in json_config["userDefined"][cur_type+"Types"]:
		cur_max = max(cur_max, math.ceil(n["maxSize"]*1.0 / n["proportion"]))

	return cur_max

def exceed_node_proportion(count, j, json_config):
	for d in json_config["userDefined"]["dTypes"]:
		if j * d["proportion"] > math.ceil(count["nodes"] * d["proportionNodeSpec"]):
			return True

	return False

def find_propotionNode_base(count, json_config):
	max_j = 0
	for d in json_config["userDefined"]["dTypes"]:
		max_j = max(max_j, (count["nodes"] * d["proportionNodeSpec"] * 1.0) / d["proportion"])

	return max_j

# To improve, just generate the next setup...
def generate_list_setup(json_config):
	all_setup = []
	cur_setup = {"nodes" : {}, "d" : {}}

	max_node = 0
	max_dep = 0
	if json_config["userDefined"]["nodesScaleType"] == "proportion":
		max_node = get_max_base_propotions(json_config, "nodes")
	
	if json_config["userDefined"]["dScaleType"] == "proportion":
		max_dep = get_max_base_propotions(json_config, "d")

	step = 1
	if args.fast_find == 1:
		step = 2
		logger.info("Entering fast find model, scale up in a scale of 2")

	if max_node > 0 and max_dep > 0:
		for i in range(1, max_node+1):
			break_flag = False
			if args.fast_find == 2:
				# first run a round of generate_list to gather the node number, and then get the max_j number. 
				temp_setup = []
				j = 1
				count = {"nodes":0, "d":0}
				generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, temp_setup, count, cur_base={"nodes": i, "d" : j})

				j = find_propotionNode_base(count, json_config)
				#print(j, max_dep, max_node, i)
				count = {"nodes":0, "d":0}
				generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, count, cur_base={"nodes": i, "d" : j})
				if count["nodes"] > confident_node_size:
					break_flag = True

			else:
				j = 1
				while j <= max_dep:
					count = {"nodes":0, "d":0}
					generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, count, cur_base={"nodes": i, "d" : j})
					if count["nodes"] > confident_node_size:
						break_flag = True
					j = get_next_num(j)
					if exceed_node_proportion(count, j, json_config):
						break

			if break_flag:
				break

	elif max_node > 0:
		for i in range(1, max_node+1, step):
			count = {"nodes":0, "d":0}
			generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, count, cur_base={"nodes": i, "d" : 0})
	elif max_dep > 0:
		for j in range(1, max_dep+1, step):
			count = {"nodes":0, "d":0}
			generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, count, cur_base={"nodes": 0, "d" : j})
	else:
		count = {"nodes":0, "d":0}
		logger.info("Enetering free mode!")
		generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, count)

	logger.info("Total setup is "+str(len(all_setup)))

	return all_setup

def sort_setup_node(element):
	count = 0
	for i in element["nodes"]:
		count += element["nodes"][i] 
	for i in element["d"]:
		count += (element["d"][i]*1.0/1000)
	
	return count

def sort_setup_all(element):
	count = 0
	for i in element["nodes"]:
		count += element["nodes"][i]
	for i in element["d"]:
		count += element["d"][i]
	
	return count

def str_setup(setup):
	s = "{"
	for n in setup["nodes"]:
		s += "node type " + str(n) + ": " + str(setup["nodes"][n]) + ", "
	for d in setup["d"]:
		s += "deployment type " + str(d) + ": " + str(setup["d"][d]) +', '
	s = s[:-2]
	s += "}"

		# s += (t + ": ")
		# for n in setup[t]:
		# 	s += "{Type " + str(n) + ": " + str(setup[t][n]) + "}, "
	# total_nodes*json_config["userDefined"]["deploymentTypes"][i]["proportionHPA"] + cur_setup["deployment"][i]

	return s

# # Used to generate templates for pre-defined cases. 
# def get_case_temeplate(case_id, scale):
# 	#config_template_filename = pml_base_path + "/min_exp/template.json"
# 	json_config = case_generator(case_id, scale, from_template=True)
# 	user_defined = get_case_user_defined(case_id, scale)

# 	# with open(config_template_filename,'w') as f:
# 	# 	json.dump(json_config, f, indent=4)

# 	return json_config
		

