import yaml
import os
import json

from util import *

# Parser can parse three types of files: 
# 1. yaml files that describe deployments, in yaml/. File must have the suffix of yaml
# 2. current setup of the cluster from kubelet describe all, in setup/. File must contain keyword "describe_all"
# 3. Other assumptions about the environment and intents, e.g. CPU change pattern, in user_input/

# TBD: 
# Parse user's intent: may need to design a front end for user to input their intents, as well as easier way for inputing the environment.

def parser(f_dir):
	dir_list = os.listdir(f_dir)

	json_config = {}

	if "yaml" not in dir_list:
		logger.critical("Yaml files not found!")
		exit()
	else:
		json_config = parse_yamls(json_config, f_dir+"/yaml", os.listdir(f_dir + "/yaml"))

	if "setup" not in dir_list:
		logger.critical("Setup files not found!")
		exit()
	else:
		json_config = parse_setup(json_config, f_dir+"/setup", os.listdir(f_dir + "/setup"))

	if "user_input" not in dir_list:
		logger.critical("User input not found!")
		exit()
	else:
		json_config, user_defined_fss = parse_user_input(json_config, f_dir+"/user_input", os.listdir(f_dir + "/user_input"))

	return json_config, user_defined_fss

def parse_yamls(json_config, f_dir, files):
	if "setup" not in json_config:
		json_config["setup"] = {}

	if "podTemplates" not in json_config["setup"]:
		json_config["setup"]["podTemplates"] = []

	if "deploymentTemplates" not in json_config["setup"]:
		json_config["setup"]["deploymentTemplates"] = []

	for f in files:
		if f[-5:] != ".yaml":
			continue
		try:
			with open(f_dir + "/" + f, 'r') as file:
				f_yaml = yaml.safe_load(file)

		except:
			logger.critical("Error in load yaml files!")
			exit()

		json_config = parse_yaml(f_yaml, json_config)

	return json_config


included_objects = ["nodes", "d", "pods"]
status_map = {"Ready":1, "Unhealthy":2}

def parse_setup(json_config, f_dir, files):
	if "setup" not in json_config:
		json_config["setup"] = {}

	for o in included_objects:
		if o not in json_config["setup"]:
			json_config["setup"][o] = []

	for f in files:
		if "describe_all" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_describe_all(json_config, file.read())

		if "describe_node" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_describe_nodes(json_config, file.read())

	return json_config

def parse_describe_all(json_config, f_str):
	for o in f_str.split("\n\nName:"):
		lines = o.split("\n")
		for l in lines:
			if l.startswith("Namespace:"):
				if "kube-system" in l:
					break

	return json_config

# TODO: instead of parsing manually, parse it into a map.
def parse_describe_nodes(json_config, f_str):
	for n in f_str.split("\n\nName:"):
		node = {}

		# process name
		raw_name = n.split("\n")[0]
		node["name"] = raw_name.split("Name:")[1].strip() if "Name:" in raw_name else raw_name.strip()

		# process labels
		# TODO: the default labels may not need the prefix like kubernetes.io
		labels = n.split("Labels:")[1].split("Annotations:")[0].split("\n")
		node["labels"] = {}
		for l in labels:
			if len(l) == 0:
				continue
			key = l.strip().split("=")[0]
			value = l.strip().split("=")[1]

			if len(value) == 0:
				continue
			node["labels"][key] = value

		# process Taint TBD

		# process Condition
		status_list = n.split("Conditions:")[1].split("Addresses:")[0].split("\n")
		for i in range(1, len(status_list)):
			if len(status_list[-i]) > 0:
				status = status_list[-i]
				break
		status = status.strip().split()[0].strip()
		if status in status_map:
			node["status"] = status_map[status]
		else:
			logger.debug("Unknown type of status " + status + ", storing 0!")
			node["status"] = 0

		# process resource. we store it in terms of m (for CPU) and mi (for memory). That's how user normally define their resource requests.
		# TODO: the actual avaiable resource capacity can vary for different type of resource. We have not considered this now. 
		resource = n.split("Capacity:")[1].split("Allocatable:")[0].split("\n")
		for r in resource:
			if "cpu" in r:
				node["cpu"] = cpu_converter(r.split("cpu:")[1].strip())

			if "memory" in r:
				node["memory"] = memory_converter(r.split("memory:")[1].strip())
		allocated_resource = n.split("Allocated resources:")[1].split("Events:")[0].split("\n")
		for r in allocated_resource:
			if "cpu" in r:
				node["cpuLeft"] = node["cpu"] - cpu_converter(r.strip().split()[1].strip())

			if "memory" in r:
				node["memLeft"] = node["memory"] - memory_converter(r.strip().split()[1].strip())

		# process Non-terminated Pods, only store non-kube-system pods. 
		pods = n.split("Non-terminated Pods:")[1].split("Allocated resources:")[0].split("\n")
		pod_count = 0
		for i in range(3, len(pods)):
			cur_pod = pods[i].strip()
			if len(cur_pod) == 0:
				continue
			if cur_pod.startswith("kube-system") or cur_pod.startswith("local-path-storage"):
				continue
			else:
				pod_count += 1
		node["numPod"] = pod_count

		json_config["setup"]["nodes"].append(node)

	return json_config

# by default converting into Mi
# https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/#resource-units-in-kubernetes
def memory_converter(s):
	if "Ki" in s:
		return int(int(s.strip()[:-2])/1024.0)
	elif "Mi" in s:
		return int(s.strip()[:-2])
	else:
		logger.critical("Unknown types of resources " + s + "!")
		exit()

# by default converting into m
def cpu_converter(s):
	if "m" in s:
		return int(s[:-1])
	else:
		return int(s)*1000

def parse_user_input(json_config, f_dir, files):
	return json_config, None 

def parse_yaml(f_yaml, json_config):
	if f_yaml["kind"] == "Deployment":
		json_deploymentTemplate, json_podTemplate = parse_deployment_yaml(f_yaml)
		json_config['setup']["podTemplates"].append(json_podTemplate)
		json_deploymentTemplate['podTemplateId'] = len(json_config['setup']["podTemplates"])
		json_config['setup']['deploymentTemplates'].append(json_deploymentTemplate)

	elif f_yaml["kind"] == "Pod":
		json_podTemplate = parse_pod_yaml(f_yaml)
		json_config['setup']["podTemplates"].append(json_podTemplate)

	else:
		logger.critical("Yaml kind has not been defined! Now only support Deployment and Pod.")
		exit()

	return json_config

def parse_deployment_yaml(f_yaml):
	json_deploymentTemplate = {}

	json_deploymentTemplate['name'] = f_yaml['metadata']['name']
	json_deploymentTemplate['specReplicas'] = f_yaml['spec']['replicas']
	# TODO: parse maxSurge, etc.

	pod_templates = f_yaml['spec']['template']
	json_podTemplate = parse_pod_yaml(pod_templates)

	return json_deploymentTemplate, json_podTemplate

def parse_pod_yaml(f_yaml):
	json_podTemplate = {}

	json_podTemplate['labels'] = deepcopy(f_yaml['metadata']['labels'])

	# Note: now only support one container pod. 
	for container in f_yaml['spec']['containers']:
		if 'resources' in container and 'requests' in container['resources']:
			# we only support define in "m" for CPU. TODO: support more types of definiation. 
			json_podTemplate['cpuRequested'] = container['resources']['requests']['cpu']
			json_podTemplate['memRequested'] = memory_converter(container['resources']['requests']['memory'])

	# TODO: process pod affinity/name
	topologySpreadConstraints_keys = ['maxSkew', 'minDomains', 'topologyKey', 'whenUnsatisfiable']
	if 'topologySpreadConstraints' in f_yaml['spec']:
		json_podTemplate['topoSpreadConstraints'] = []
		for constraint in f_yaml['spec']['topologySpreadConstraints']:
			json_pod_topologySpreadConstraints = {} 
			for e in constraint:
				if e in topologySpreadConstraints_keys:
					json_pod_topologySpreadConstraints[e] = constraint[e]

				if e == 'labelSelector':
					json_pod_topologySpreadConstraints['labels'] = constraint[e]["matchLabels"]
			json_podTemplate['topoSpreadConstraints'].append(json_pod_topologySpreadConstraints)

		json_podTemplate['numTopoSpreadConstraints'] = len(json_podTemplate['topoSpreadConstraints'])

	return json_podTemplate


if __name__ == '__main__':
	json_config, user_defined_fss = parser(args.path)

	json_str = json.dumps(json_config, indent=4)

	print(json_str)

