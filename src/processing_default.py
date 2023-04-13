import copy
import sys

from util import *


##### Pod Topo Spreading Plugins
# implement filterTopologySpreadConstraints and buildDefaultConstraints in common.go
# deal with enableMatchLabelKeysInPodTopologySpread
# deal with defaultValue for podSpreadPolicy


# required to define for the verification, not for the config from the user. 
# TODO: check if we need to init the score -- if this benefit verification perf or not
# TODO: putting all the default value definition into the same file (move the definiations in config.pml into this)

# A list of field in the typedef, need to be synced with dataType.pml. TODO: could auto-populate this.
# TODO: adding the process on affinityrules, noschedulenodes, etc.
elements_required = {"nodes" : ["id", "name", "cpu", "cpuLeft", "memory", "memLeft", "status", "numPod", "labels", "score", "curScore", "curAffinity", "curTaint", "maintained"], \
					 "pods" : ["id", "loc", "status", "cpu", "memory", "workloadType", "workloadId", "podTemplateId", "score", "important", "curCpuIndex"], \
					 "d" : ["id", "name", "status", "replicaSets", "curVersion", "specReplicas", "replicas",  "maxSurge", "maxUnavailable", "strategy", "podTemplateId", "hpaSpec"], \
					"podTemplates" : ["labels", "cpuRequested", "memRequested", "numRules", "nodeName", "numNoScheduleNode", "numPreferNoScheduleNode", "numTopoSpreadConstraints", \
									"topoSpreadConstraints", "maxCpuChange"],\
					"deploymentTemplates" : ["id", "name", "maxSurge", "maxUnavailable", "specReplicas"]}


default_values = { 
	"nodes" : {"score" : 0, "curScore" : 0, "curAffinity" : 0, "curTaint" : 0, "labels" : None, "maintained" : 0}, \
	"pods" : {"status" : 0, "important" : 0, "workloadType" : 0, "workloadId" : 0, "score" : 0, "cpu" : 0, "memory" : 0, "curCpuIndex" : 0}, \
	# maxReplicas must be defined by users
	"d": { "curVersion" : 0, "specReplicas" : 1, "maxSurge" : 25, "maxUnavailable" : 25, "strategy" : 1, "hpaSpec" : {"isEnabled" : 0, "numMetrics" : 0, "minReplicas" : 1}}, \
	# https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#internal-default-constraints
	# The definiation is in plugin.go, variable systemDefaultConstraints 
	# The default selector for topoSpreadConstraints should be the same as the pod labels in metadata.
	"podTemplates" : {"numRules" : 0, "nodeName" : 0,  "numNoScheduleNode" : 0, "numPreferNoScheduleNode" : 0, "topoSpreadSystemDefaulted": 1, "numTopoSpreadConstraints" : 2, \
					  "topoSpreadConstraints" : [{"maxSkew" : 3, "topologyKey" : "hostname", "whenUnsatisfiable" : 1, "labels" : None}, \
					  {"maxSkew" : 5, "topologyKey" : "zone", "whenUnsatisfiable" : 1, "labels" : None}], "maxCpuChange" : 0}, \
	"deploymentTemplates" : {"maxSurge" : -1, "maxUnavailable" : -1, "specReplicas" : -1}
}

# TODO: add default for nodeAffinityPolicy, and nodeTaintsPolicy
default_controllers = ["hpa", "scheduler", "deployment"]

default_configs = {"scheduler" : {"pod_spread": {"nodeInclusionPolicyInPodTopologySpread" : 1, "minDomainsInPodTopologySpread" : 0}}}


default_parameter_order = {
	"eventCpuChange" : ["targetDeployment"], "maintenance" : ["p"], "podCpuChangeWithPattern" : ["targetDeployment"]
}

event_default_str = {
	"kernelPanic" : "int i = 1; \n for (i : 1 .. NODE_NUM) { \n run kernelPanic(i);\n}\n"
}

# TODO: check on default labels
# TODO: now we assign the values of labels manually. Can be more automatic. 
default_labels = {
	"nodes": ["hostname", "zone"]
}

def labels_default(json_config):
	flag = 0
	for n in json_config["setup"]["nodes"]:
		if n["labels"] == None:
			n["labels"] = {}
		n["labels"]["hostname"] = n["name"]
		if "zone" in n["labels"]:
			flag = 1

	# We don't add zone label for now, as looks like if without cloud provider, the zone label will stay unset. 
	# for n in json_config["setup"]["nodes"]:
	# 	if "zone" not in n["labels"]:
	# 		if flag == 1:
	# 			sys.exit("[error] " + "Some nodes defined Zone, while some did not!")
	# 		else:
	# 			n["labels"]["zone"] = 1


# According to https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#spread-constraint-definition
def pod_template_default(json_config):
	#print(json_config)
	for pt in json_config["podTemplates"]:
		if pt["numTopoSpreadConstraints"] > 0:
			for ptcon in pt["topoSpreadConstraints"]:
				if "nodeAffinityPolicy" not in ptcon:
					ptcon["nodeAffinityPolicy"] = 1
				if "nodeTaintsPolicy" not in ptcon:
					ptcon["nodeTaintsPolicy"] = 0
				if "minDomains" not in ptcon:
					ptcon["minDomains"] = 1
				if ptcon["labels"] is None:
					ptcon["labels"] = copy.deepcopy(pt["labels"])

# TODO: check if the array size match with the number
# TODO: check if the values are valid: e.g. minDomains in the podSpreadingConstraints must be more than 0 when speicified. 
def check_for_completion_add_default(json_config):
	userDefinedConstraints = 1
	for resource in elements_required:
		if resource in json_config["setup"]:
			for e in elements_required[resource]:
				for r in json_config["setup"][resource]:
					if e not in r:
						if e == "topoSpreadConstraints":
							userDefinedConstraints = 0
						if e in default_values[resource]:
							r[e] = copy.deepcopy(default_values[resource][e])
							#print("Filling in default value for " + e, r[e])
						else:
							sys.exit("[error] " + e + " in " + resource + " has not been defined!")
		else:
			# It's OK to not define some resource, e.g. deployment Template. 
			logger.warning(resource + " is not defined! But may not affect the execution.")
			json_config["setup"][resource] = []

	labels_default(json_config)

	pod_template_default(json_config["setup"])

	return userDefinedConstraints


# TODO: in the future when writing a parser for an actual config, need to implement the following func:
# [Done] 1. generate default labels. 
