
# 
#	1. Node type: can be mapped to the node groups in k8s cluster autoscaling. It is suggested by AWS 
#	   that "Configure a smaller number of node groups with a larger number of nodes because the opposite configuration can negatively affect scalability."
#	   https://docs.aws.amazon.com/eks/latest/userguide/autoscaling.html

from copy import deepcopy
import json
import sys
from case_generator import *
import math

def compare_template(t1, t2, field):
	for f in field:
		if f in t1:
			if isinstance(t1[f], dict):
				for e in t1[f]:
					if t1[f][e] != t2[f][e]:
						return False

			else:
				if f not in t2 or t1[f] != t2[f]:
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

	for i in range(0, len(count)):
		if count[i] < min_count:
			min_count = count[i]

	for i in range(0, len(count)):
		count[i] = int(count[i]*1.0/min_count)

	return count

def template_generator(json_config, user_defined):
	json_config["userDefined"] = {}

	templates = {"nodes":["cpu", "memory", "status", "labels"], "d":["status", "podTemplateId", "hpaSpec"]}

	for t in ["nodes", "d"]:
		type_setup = []
		count = []
		for n in json_config["setup"][t]:
			new_flag = True
			for i in range(0, len(type_setup)):
				if compare_template(n, type_setup[i]["template"], templates[t]):
					count[i] += 1
					new_flag = False
					break

			if new_flag:
				new_type = {}
				new_type["template"] = {}
				assign_template(n, new_type["template"], templates[t])
				if t == "nodes":
					new_type["template"]["cpuLeft"] = n["cpu"]
					new_type["template"]["memLeft"] = n["memory"]
					new_type["template"]["numPod"] = 0
				new_type["upperBound"] = user_defined[t+"_default"]["upperBound"]
				new_type["lowerBound"] = user_defined[t+"_default"]["lowerBound"]
				# propotion == 0 if nodeScaleType is free
				new_type["proportion"] = 0
				type_setup.append(new_type)
				count.append(1)


		propotion = get_propotion(count)
		for i in range(0, len(type_setup)):
			if user_defined[t+"_default"]["ScaleType"] == "proportion":
				type_setup[i]["proportion"] = propotion[i]
			if t == "d":
				type_setup[i]["proportionHPA"] = user_defined[t+"_default"]["proportionHPA"]
				

		json_config["userDefined"][t+"Types"] = deepcopy(type_setup)
		json_config["userDefined"][t+"ScaleType"] = user_defined[t+"_default"]["ScaleType"]

	json_config["setup"].pop("d")
	json_config["setup"].pop("pods")
	json_config["setup"].pop("nodes")

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
			cur_node["name"] = cur_id
			cur_id += 1

			new_json_config["setup"]["nodes"].append(cur_node)
			total_nodes += 1

	new_json_config["setup"]["d"] = []
	new_json_config["setup"]["pods"] = []
	if "userCommand" not in new_json_config:
		new_json_config["userCommand"] = {}
	if "createTargetDeployment" not in new_json_config["userCommand"]:
		new_json_config["userCommand"]["createTargetDeployment"] = []
	cur_d_id = 1
	for i in range(0, len(json_config["userDefined"]["dTypes"])):		
		max_replicas = total_nodes*json_config["userDefined"]["dTypes"][i]["proportionHPA"] + cur_setup["d"][i]
		if max_replicas > json_config["userDefined"]["dTypes"][i]["upperBound"]:
			max_replicas = json_config["userDefined"]["dTypes"][i]["upperBound"]

		d = deepcopy(json_config["userDefined"]["dTypes"][i]["template"])
		d["id"] = cur_id
		d["name"] = cur_id
		cur_id += 1

		d["curVersion"] = 0
		d["replicaSets"] = []

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = cur_d_id
		rp["replicas"] = 0
		rp["specReplicas"] = cur_setup["d"][i]
		rp["version"] = 0
		rp["podIds"] = []
		d["replicaSets"].append(rp)

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = cur_d_id
		d["replicaSets"].append(rp)

		d["specReplicas"] = cur_setup["d"][i]
		d["replicas"] = 0

		if "hpaSpec" in d:
			if d["hpaSpec"]["isEnabled"] == 1:
				d["hpaSpec"]["minReplicas"] = cur_setup["d"][i]
				d["hpaSpec"]["maxReplicas"] = max_replicas

		new_json_config["setup"]["d"].append(d)
		new_json_config["userCommand"]["createTargetDeployment"].append(cur_d_id)

		cur_d_id += 1

		for j in range(0, max_replicas):
			cur_pod = {}
			cur_pod["id"] = cur_id
			cur_id += 1
			
			cur_pod["status"] = 0
			new_json_config["setup"]["pods"].append(cur_pod)

	return new_json_config, len(new_json_config["setup"]["nodes"]), len(new_json_config["setup"]["pods"]) 

def get_next_num(j):
	if j < 4:
		j += 1
	else:
		j = j*2

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

def generate_list_setup_dfs(json_config, i, cur_type, cur_setup, all_setup, cur_base=None):
	if cur_type == "nodes" and i == len(json_config["userDefined"]["nodesTypes"]):
		generate_list_setup_dfs(json_config, 0, "d", cur_setup, all_setup, cur_base)
		return
	if cur_type == "d" and i == len(json_config["userDefined"]["dTypes"]):
		if not check_duplicate(all_setup, cur_setup):
			all_setup.append(deepcopy(cur_setup))
		#generate_case_json(cur_setup, json_config)
		return

	cur_json_config = json_config["userDefined"][cur_type+"Types"][i]
	if json_config["userDefined"][cur_type+"ScaleType"] == "proportion":
		j = cur_base[cur_type] * cur_json_config["proportion"]
		if j < cur_json_config["lowerBound"]:
			j = cur_json_config["lowerBound"]
		if j > cur_json_config["upperBound"]:
			j = cur_json_config["upperBound"]

		cur_setup[cur_type][i] = j
		generate_list_setup_dfs(json_config, i+1, cur_type, cur_setup, all_setup, cur_base)

	elif json_config["userDefined"][cur_type+"ScaleType"] == "free":
		j = cur_json_config["lowerBound"]
		while j <= cur_json_config["upperBound"]:
			cur_setup[cur_type][i] = j
			generate_list_setup_dfs(json_config, i+1, cur_type, cur_setup, all_setup, cur_base)
			j = get_next_num(j)

	else:
		logger.critical("Unknown scaling type for " + cur_type + "!")
		return None

def get_max_base_propotions(json_config, cur_type):
	cur_max = 0
	for n in json_config["userDefined"][cur_type+"Types"]:
		cur_max = cur_max if math.ceil(n["upperBound"]*1.0 / n["proportion"]) < cur_max else math.ceil(n["upperBound"]*1.0 / n["proportion"])

	return cur_max

def generate_list_setup(json_config):
	all_setup = []
	cur_setup = {"nodes" : {}, "d" : {}}

	max_node = 0
	max_dep = 0
	if json_config["userDefined"]["nodesScaleType"] == "proportion":
		max_node = get_max_base_propotions(json_config, "nodes")
	
	if json_config["userDefined"]["dScaleType"] == "proportion":
		max_dep = get_max_base_propotions(json_config, "d")

	print(max_node, max_dep)

	if max_node > 0 and max_dep > 0:
		for i in range(1, max_node+1):
			for j in range(1, max_dep+1):
				generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, cur_base={"nodes": i, "d" : j})
	elif max_node > 0:
		for i in range(1, max_node+1):
			generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, cur_base={"nodes": i, "d" : 0})
	elif max_dep > 0:
		for j in range(1, max_dep+1):
			generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup, cur_base={"nodes": 0, "d" : j})
	else:
		generate_list_setup_dfs(json_config, 0, "nodes", cur_setup, all_setup)

	return all_setup

def sort_setup_node(element):
	count = 0
	for i in element["nodes"]:
		count += element["nodes"][i] 
	for i in element["d"]:
		count += (element["d"][i]*1.0/10)
	
	return count

def sort_setup_all(element):
	count = 0
	for i in element["nodes"]:
		count += element["nodes"][i]
	for i in element["d"]:
		count += element["d"][i]
	
	return count

def str_setup(setup):
	s = ""
	for t in setup:
		s += (t + ": ")
		for n in setup[t]:
			s += "{Type " + str(n) + ": " + str(setup[t][n]) + "}, "
	# total_nodes*json_config["userDefined"]["deploymentTypes"][i]["proportionHPA"] + cur_setup["deployment"][i]

	return s

def get_case_temeplate(file_base, case_id):
	config_template_filename = file_base + "/temp/" + case_id + "/configs/template.json"
	json_config = case_generator(case_id, 0)

	if json_config == None:
		json_config = case_generator(case_id, 3)
		user_defined = get_case_user_defined(case_id)
		json_config = template_generator(json_config, user_defined)

	with open(config_template_filename,'w') as f:
		json.dump(json_config, f, indent=4)

	return json_config
		
def finding_smallest_scale(json_config, pml_base_path, file_base, case_id, sort_favor="nodes"):
	all_setup = generate_list_setup(json_config)
	print(all_setup)
	if sort_favor == "nodes":
		all_setup.sort(key = sort_setup_node)
	if sort_favor == "all":
		all_setup.sort(key = sort_setup_all)
	print(all_setup)

	count = 0
	for s in all_setup:
		new_json_config, num_node, num_pod = generate_case_json(json_config, s)
		config_template_filename = file_base + "/temp/" + case_id + "/configs/" + str(count) + "_" + str(num_node) + "_" + str(num_pod) + ".json"
		count += 1

		with open(config_template_filename,'w') as f:
			json.dump(new_json_config, f, indent=4)

	return all_setup, json_config

if __name__ == '__main__':
	case_id = sys.argv[1]

	file_base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
	if len(sys.argv) > 3:
		file_base = os.path.abspath(sys.argv[3])

	result_base_path = file_base + "/results/" + str(case_id)
	pml_base_path = file_base + "/temp/" + str(case_id)  

	json_config = get_case_temeplate(file_base, case_id)
	print(json_config)
	all_setup = finding_smallest_scale(json_config, pml_base_path, file_base, case_id)

	

