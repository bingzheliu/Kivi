# This module parses the config yamls and runtime logs and generates a uniformed format JSON.

import yaml
import os
import json

from util import *
from math import ceil

# Parser can parse three types of files: 
# 1. yaml files that describe deployments, in yaml/. File must have the suffix of yaml. Will be saved as pod and deployment templates.
# 2. current setup of the cluster from kubelet describe all, in setup/. File must contain keyword "describe_all"
# 3. Other assumptions about the environment and intents, e.g. CPU change pattern, in user_input/

# TBD: 
# 1. Parse user's intent: may need to design a front end for user to input their intents, as well as easier way for inputing the environment.
# 3. Now we can't process if a pod is in pending when it collect the log
# 4. Now we don't process replicaset. Instead, each deployment will generate one replicaset. 
# 5. Now we only support one container pod.
# 6. Improve the transformation between natural language and number. Now it happens during parsing each element, and we could process them all in one place to improve resilience to future changes.


# Note:
# 1. The metric server may have delays -- the CPU/memory usage of the pods/nodes may not be consistent with the actual usage. 
# 2. About labels: the getpod does not have the labels information for pod template. So we won't store it if creating podTemplate from getpod. The getdeployment on the other hand does have labels for podTemplate. 
#    When comparing difference between pod template, this will be considered and hence we may find one deployment have multiple pod template, which does not affect the result.

# Left:
# - 1. connect Deployment with replicasets and pods
# - 2. translate the str into numbers for all the names
# - 3. reprocess labels -- labels need to be go with pods rather than podTemplate; need to take a loop at how deployment-level labels work
# 4. Process usercommand
# 5. Connect parser with model_generator

def parser(f_dir):
	dir_list = os.listdir(f_dir)

	json_config = {}

	if "yaml" not in dir_list:
		logger.critical("Yaml files not found!")
	else:
		json_config = parse_yamls(json_config, f_dir+"/yaml", os.listdir(f_dir + "/yaml"))

	if "setup" not in dir_list:
		logger.critical("Setup files not found!")
	else:
		json_config = parse_setup(json_config, f_dir+"/setup", os.listdir(f_dir + "/setup"))

	if "user_input" not in dir_list:
		logger.critical("User input not found!")
	else:
		json_config, user_defined_fss = parse_user_input(json_config, f_dir+"/user_input", os.listdir(f_dir + "/user_input"))

	# We need to add spare objects to the setup in order for the model to add new pods and nodes.
	json_config = add_spare_resource(json_config)

	json_config = convert_all_to_number(json_config)

	#print(json_readable_str(json_config))

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

	# parse hpa after we have got all the deployment
	for f in files:
		if f[-5:] != ".yaml":
			continue
		try:
			with open(f_dir + "/" + f, 'r') as file:
				f_yaml = yaml.safe_load(file)

		except:
			logger.critical("Error in load yaml files!")
			exit()

		if f_yaml["kind"] == "HorizontalPodAutoscaler":
			json_config = parse_hpayaml(json_config, f_yaml)

	return json_config


included_objects = ["nodes", "d", "pods", "podTemplates", "deploymentTemplates"]
status_map = {"node": {"Ready":1, "Unhealthy":2}, "pod" : {"Running" : 1, "Pending" : 2, "Terminating" : 3}}
kind_map = {"ReplicaSet" : 1}
whenunsatisfiable_map = {"DoNotSchedule" : 0, "ScheduleAnyway" : 1}

def parse_setup(json_config, f_dir, files):
	if "setup" not in json_config:
		json_config["setup"] = {}

	for o in included_objects:
		if o not in json_config["setup"]:
			json_config["setup"][o] = []

	for f in files:
		if "getpod" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_getpod(json_config, file.read())

		if "describenode" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_describe_nodes(json_config, file.read())

		if "getdeployment" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_getdeployment(json_config, file.read())

	for f in files:
		if "toppod" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_toppod(json_config, file.read())

		if "gethpa" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_gethpa(json_config, file.read())

	json_config = link_deployment_pod(json_config)

	return json_config

# TODO: this may need to be done by verifier incrementally. 
def add_spare_resource(json_config):
	for d in json_config["setup"]["d"]:
		if "hpaSpec" in d:
			max_replicas = d["hpaSpec"]["maxReplicas"]
			if max_replicas > d["replicas"]:
				for i in range(0, max_replicas - d["replicas"] + 3):
					json_config["setup"]["pods"].append({"status" : 0})

	# Will need to add user-defined numebr of pods here.

	return json_config

def convert_all_to_number(json_config):
	# The label process is left for model_generator, as the label is specially treated to improve model efficiency. 
	# So if some phrase is the same for both labels and names, they won't be treated the same, which does not affect verification correctness

	# process location
	for p in json_config["setup"]["pods"]:
		for i in range(0, len(json_config["setup"]["nodes"])):
			n_name = json_config["setup"]["nodes"][i]["name"]
			if "loc" in p and n_name == p["loc"]:
				p["loc"] = i+1
				break

	# process names
	all_names = set()
	for o in included_objects:
		for e in json_config["setup"][o]:
			if "name" in e:
				all_names.add(e["name"])
	all_names = list(all_names)
	all_names = {all_names[index] : index for index in range(0, len(all_names)) }
	for o in included_objects:
		for e in json_config["setup"][o]:
			if "name" in e:
				e["name"] = all_names[e["name"]]

	logger.debug("Mapping between names and number:")
	logger.debug(all_names) 

	return json_config

# TBD: this can be changed to connect it through linking the deployment -> replicaset -> pods
def link_deployment_pod(json_config):
	for i in range(0, len(json_config["setup"]["d"])):
		d = json_config["setup"]["d"][i]
		count = 0
		replicaSets = {}
		replicaSets["deploymentId"] = i+1
		replicaSets["podIds"] = []
		for j in range(0, len(json_config["setup"]["pods"])):
			p = json_config["setup"]["pods"][j]
			if p["name"].startswith(d["name"]):
				if "workloadId" in p:
					logger.critical("A pod is related to two deployment!")
					continue
				
				p["workloadId"] = i+1
				count += 1
				replicaSets["podIds"].append(j+1)

		if count != d["replicas"]:
			logger.critical("Number of pods are not equal to the replicas status in deployment!")

		# We now assume replicas spec is the same as the spec in deployment
		replicaSets["replicas"] = count
		replicaSets["specReplicas"] = d["specReplicas"]
		replicaSets["version"] = 0

		d["curVersion"] = 0
		d["replicaSets"] = []
		d["replicaSets"].append(deepcopy(replicaSets))
		d["replicaSets"].append({"deploymentId":i+1})

	return json_config

def parse_toppod(json_config, f_str):
	pods = f_str.split("\n")[1:]
	for p in pods:
		p_name = p.split(",")[0].strip()

		for p_json in json_config["setup"]["pods"]:
			if p_json["name"] == p_name:
				p_json["cpu"] = cpu_converter(p.split(",")[1].strip())
				p_json["memory"] = memory_converter(p.split(",")[2].strip())

	return json_config


def parse_gethpa(json_config, f_str):
	# Now the HPA connects with the deployment through having the same name
	hpas = f_str.split("\n")[1:]
	for hpa in hpas:
		if "Deployment" in hpa:
			hpa_name = hpa.split(",")[0].strip()
			for d in json_config["setup"]["d"]:
				if d["name"] == hpa_name:
					hpa_spec = {}
					hpa_spec["isEnabled"] = 1
					# We now only support one target, but can be easily changed to support several targets. 
					hpa_spec["numMetrics"] = 1
					# TBD: may be better to parse the describe hpa that has more information; we now just process it for CPU utlization
					hpa_spec["metricTypes"] = [1]
					hpa_spec["metricNames"] = [0]
					hpa_spec["metricTargets"] = [int(hpa.split(",")[2].split("/")[1].strip()[:-1])]
					hpa_spec["minReplicas"] = int(hpa.split(",")[3])
					hpa_spec["maxReplicas"] = int(hpa.split(",")[4])
					d["hpaSpec"] = deepcopy(hpa_spec)

		else:
			logger.critical("Unknown types of HPA resource:" + hpa + ". Skipping...")

	return json_config

def parse_podTemplate(p):
	podTemplate = {}

	if len(p["containers"]) > 1: 
		logger.critical("Only support 1 container per pod! Storing the first one...")
	if "requests" in p["containers"][0]["resources"]:
		cr = p["containers"][0]["resources"]["requests"]
		if "cpu" in cr:
			podTemplate["cpuRequested"] = cpu_converter(cr["cpu"])
		if "memory" in cr:
			podTemplate["cpuRequested"] = memory_converter(cr["memory"])

	# TODO: process affinity, nodeName and tolerance

	# process topologySpreadConstraints
	if "topologySpreadConstraints" in p and len(p["topologySpreadConstraints"]) > 0:
		tps = p["topologySpreadConstraints"]
		podTemplate["topoSpreadConstraints"] = []
		for tp in tps:
			tpc = {}
			# only support "matchLabels" now
			tpc["labels"] = tp["labelSelector"]["matchLabels"]
			tpc["maxSkew"] = tp["maxSkew"]
			tpc["topologyKey"] = tp["topologyKey"]
			tpc["whenUnsatisfiable"] = whenunsatisfiable_map[tp["whenUnsatisfiable"]]
			podTemplate["topoSpreadConstraints"].append(deepcopy(tpc))
		podTemplate["numTopoSpreadConstraints"] = len(p["topologySpreadConstraints"])

	return podTemplate

# We don't compare between different template for now. 
# Hence the config we got in the yaml and the getdeployment will be treated different.
def parse_getdeployment(json_config, json_input):
	json_input = json.loads(json_input)

	for d in json_input["items"]:
		if d["metadata"]["namespace"] == "kube-system" or d["metadata"]["namespace"] == "local-path-storage":
			continue

		deployment = {}
		deployment["name"] = d["metadata"]["name"]

		deployment["specReplicas"] = d["spec"]["replicas"]
		# Rolling update TBD
		# if d["spec"]["strategy"]["type"] == "RollingUpdate":
		# 	deployment["maxSurge"] = int(d["spec"]["strategy"]["rollingUpdate"]["maxSurge"][:-1])
		# 	deployment["maxUnavailable"] = int(d["spec"]["strategy"]["rollingUpdate"]["maxUnavailable"][:-1])
		# 	deployment["strategy"] = 1
		# else:
		# 	deployment["strategy"] = 0
		deployment["strategy"] = 0

		deployment["replicas"] = d["status"]["availableReplicas"]

		podTemplate = parse_podTemplate(d["spec"]["template"]["spec"])
		# The pod template defined in deployment has the labels
		podTemplate["labels"] = d["spec"]["template"]["metadata"]["labels"]
		index, json_config = add_podTemplate(podTemplate, json_config)
		deployment["podTemplateId"] = index

		json_config["setup"]["d"].append(deepcopy(deployment))

	return json_config

# If every field of the podTemplate are the same to an existing one, we won't create a new template
def compare_podTemplate(pt1, pt2):
	return pt1 == pt2

def add_podTemplate(podTemplate, json_config):
	for i in range(0, len(json_config["setup"]["podTemplates"])):
		pt = json_config["setup"]["podTemplates"][i]
		if compare_podTemplate(podTemplate, pt):
			return i+1, json_config

	json_config["setup"]["podTemplates"].append(deepcopy(podTemplate))
	return len(json_config["setup"]["podTemplates"]), json_config

def parse_getpod(json_config, json_input):
	json_input = json.loads(json_input)
	for p in json_input["items"]:
		if p["metadata"]["namespace"] == "kube-system" or p["metadata"]["namespace"] == "local-path-storage":
			continue

		pod = {}
		pod["name"] = p["metadata"]["name"]

		for k in p["metadata"]["ownerReferences"]:
			if k["kind"] in kind_map:
				if "workloadType" in pod:
					logger.critical("Multiple types of pod owner!")
					logger.critical(p["metadata"]["ownerReferences"])
					break
				if k["kind"] in kind_map:
					pod["workloadType"] = kind_map[k["kind"]]
				else:
					logger.critical("Unknown type of pod owner: " + str())

		status = p["status"]["phase"]
		if status in status_map["pod"]:
			pod["status"] = status_map["pod"][status]
		else:
			logger.critical("Unknown type of status " + status + ", storing 0!")
			pod["status"] = 0

		# Need to convert it into number later
		# it will be automated assign with 0 in the processing_default if it's not scheduled. 
		if "nodeName" in p["spec"]:
			pod["loc"] = p["spec"]["nodeName"]

		podTemplate = parse_podTemplate(p["spec"])
		index, json_config = add_podTemplate(podTemplate, json_config)
		pod["podTemplateId"] = index

		# process labels
		pod["labels"] = deepcopy(p["metadata"]["labels"])

		json_config["setup"]["pods"].append(deepcopy(pod))

	return json_config


# Though we have getnodes in json, it lacks many information (e.g. # of pods, allocated resources). 
# Hence parse describe node instead. 
def parse_describe_nodes(json_config, f_str):
	for n in f_str.split("\n\nName:"):
		node = {}

		# process name
		raw_name = n.split("\n")[0]
		node["name"] = raw_name.split("Name:")[1].strip() if "Name:" in raw_name else raw_name.strip()
		if "control-plane" in node["name"]:
			continue

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
		if status in status_map["node"]:
			node["status"] = status_map["node"][status]
		else:
			logger.critical("Unknown type of status " + status + ", storing 0!")
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

		json_config["setup"]["nodes"].append(deepcopy(node))

	return json_config

# by default converting into Mi
# https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/#resource-units-in-kubernetes
# Now we approximate the memory using Gi as 1 unit. If it's less than 1 unit, we count as 1.
def memory_converter(s):
	if "Ki" in s:
		return ceil(int(s.strip()[:-2])/(1024.0*1024.0))
	elif "Mi" in s:
		return ceil(int(s.strip()[:-2])/1024.0)
	else:
		logger.critical("Unknown types of resources " + s + "!")
		exit()

# by default converting into m
def cpu_converter(s):
	if "m" in s:
		return int(s[:-1])
	else:
		return int(s)*1000

# TODO: parse various intents, and also the command for defining the bundary for smallest scale algorithm
def parse_user_input(json_config, f_dir, files):
	for f in files:
		if "intent" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_user_intents(json_config, file.read())

		if "user_command" in f:
			with open(f_dir + "/" + f, "r") as file:
				json_config = parse_user_command(json_config, file.read())

	return json_config, None 

def parse_user_intents(json_config, f_dir):
	return json_config

def parse_user_command(json_config, f_dir):
	return json_config


def parse_yaml(f_yaml, json_config):
	if f_yaml["kind"] == "Deployment":
		json_deploymentTemplate, json_podTemplate = parse_deployment_yaml(f_yaml)
		json_config['setup']["podTemplates"].append(deepcopy(json_podTemplate))
		json_deploymentTemplate['podTemplateId'] = len(json_config['setup']["podTemplates"])
		json_config['setup']['deploymentTemplates'].append(deepcopy(json_deploymentTemplate))

	elif f_yaml["kind"] == "Pod":
		json_podTemplate = parse_pod_yaml(f_yaml)
		json_config['setup']["podTemplates"].append(deepcopy(json_podTemplate))

	elif f_yaml["kind"] == "HorizontalPodAutoscaler":
		pass
		# parse if after parse all the deployment

	else:
		logger.critical("Yaml kind has not been defined! Now only support Deployment and Pod.")

	return json_config

hpa_mapping = {"metricNames":{"cpu":0, "memory":1}, "metricTypes":{"Utilization":1, "Value":0}}

def parse_hpayaml_hpaspec(f_yaml):
	hpa_spec = {}
	hpa_spec["isEnabled"] = 1

	hpa_spec["metricTypes"] = []
	hpa_spec["metricNames"] = []
	hpa_spec["metricTargets"] = []
	for metric in f_yaml["spec"]["metrics"]:
		metric = metric["resource"]
		try:
			hpa_spec["metricNames"].append(hpa_mapping["metricNames"][metric["name"]])
			hpa_spec["metricTypes"].append(hpa_mapping["metricTypes"][metric["target"]["type"]])
			if hpa_spec["metricTypes"][-1] == 1:
				hpa_spec["metricTargets"].append(int(metric["target"]["averageUtilization"]))
			else:
				if hpa_spec["metricNames"][-1] == 0:
					hpa_spec["metricTargets"].append(cpu_converter(metric["target"]["averageValue"]))
				else:
					hpa_spec["metricTargets"].append(memory_converter(metric["target"]["averageValue"]))
		except:
			logger.critical("Unsupported kind of HPA metrics!")
			logger.critical(metric)
			exit()

	hpa_spec["numMetrics"] = len(hpa_spec["metricTypes"])
	hpa_spec["maxReplicas"] = int(f_yaml["spec"]["maxReplicas"])
	hpa_spec["minReplicas"] = int(f_yaml["spec"]["minReplicas"])

	return hpa_spec

def parse_hpayaml(json_config, f_yaml):
	if f_yaml["spec"]["scaleTargetRef"]["kind"] != "Deployment":
		logger.critical("We currently don't support "+ f["spec"]["scaleTargetRef"]["kind"])

	target_dep = f_yaml["spec"]["scaleTargetRef"]["name"]

	if "d" in json_config["setup"]:
		for d in json_config["setup"]["d"]:
			if d["name"] == target_dep:
				hpa_spec = parse_hpayaml_hpaspec(f_yaml)
				d["hpaSpec"] = deepcopy(hpa_spec)

		else:
			logger.critical("Unknown target for HPA resource:" + hpa + ". Skipping...")

	if "deploymentTemplates" in json_config["setup"]:
		for d in json_config["setup"]["deploymentTemplates"]:
			if d["name"] == target_dep:
				hpa_spec = parse_hpayaml_hpaspec(f_yaml)
				d["hpaSpec"] = deepcopy(hpa_spec)

			else:
				logger.critical("Unknown target for HPA resource:" + hpa + ". Skipping...")

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
					if e == 'whenUnsatisfiable':
						json_pod_topologySpreadConstraints[e] = whenunsatisfiable_map[constraint[e]]
					else:
						json_pod_topologySpreadConstraints[e] = constraint[e]

				if e == 'labelSelector':
					json_pod_topologySpreadConstraints['labels'] = constraint[e]["matchLabels"]
			json_podTemplate['topoSpreadConstraints'].append(deepcopy(json_pod_topologySpreadConstraints))

		json_podTemplate['numTopoSpreadConstraints'] = len(json_podTemplate['topoSpreadConstraints'])

	return json_podTemplate

if __name__ == '__main__':
	json_config, user_defined_fss = parser(args.path)

	json_str = json.dumps(json_config, indent=4)

	print(json_str)

