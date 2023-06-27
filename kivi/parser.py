import yaml
import os

from util import *

# Parser can parse three types of files: 
# 1. yaml files that describe deployments, in yaml/
# 2. current setup of the cluster from kubelet describe all, in setup/
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
		json_config = parse_yamls(json_config, os.listdir(f_dir + "/yaml"))

	if "setup" not in dir_list:
		logger.critical("Setup files not found!")
		exit()
	else:
		json_config = parse_setup(json_config, os.listdir(f_dir + "/setup"))


	if "user_input" not in dir_list:
		logger.critical("User input not found!")
		exit()
	else:
		json_config, user_defined_fss = parse_user_input(json_config, os.listdir(f_dir + "/user_input"))

	return json_config, user_defined_fss

def parse_yamls(json_config, files):
	if "setup" not in json_config:
		json_config["setup"] = {}

	if "podTemplates" not in json_config["setup"]:
		json_config["setup"]["podTemplates"] = []

	if "deploymentTemplates" not in json_config["setup"]:
		json_config["setup"]["deploymentTemplates"] = []

	for f in files:
		try:
			f_yaml = yaml.safe_load(f)
			json_config = parse_yaml(f_yaml, json_config)

		except:
			logger.critical("Error in load yaml files!")
			exit()

	return json_config

def parse_setup(json_config, files):
	pass

def parse_user_input(json_config, files):
	pass 


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
		json_podTemplate['cpuRequested'] = container['resources']['requests']['cpu']
		json_podTemplate['memRequested'] = container['resources']['requests']['memory']

	# TODO: process pod affinity
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




