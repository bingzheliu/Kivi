##### Pod Topo Spreading Plugins
# implement filterTopologySpreadConstraints and buildDefaultConstraints in common.go
# deal with enableMatchLabelKeysInPodTopologySpread
# deal with defaultValue for podSpreadPolicy


# required to define for the verification, not for the config from the user. 
# TODO: check if we need to init the score -- if this benefit verification perf or not
# TODO: putting all the default value definition into the same file (move the definiations in config.pml into this)

from util import *
import sys, json

# This is the field that must be modified to compile even the intents is not defined.
default_intent_parameters = {"checkExpReplicas": {"[$expReplicas]":0}}
default_intent_ifdef = {"kernel_panic":"KERNEL_PANIC", "no_feasiable_node":"NO_FEASIABLE_NODE","checkEvictionCycle":"CHECK_EVICTION_CYCLE", "checkBalanceNode":"CHECK_BALANCE_NODE"}
# the para are default parameters, only enabled if it's not defined
default_intent_library = {"kernel_panic": {"flag":True, "run":False, "para":{}}, "no_feasiable_node": {"flag":True, "run": False, "para":{}}, \
						  "checkOscillation": {"flag":False, "run": True, "para":{"did":0}}, "checkMinReplicas": {"flag":False, "run": True, "para":{"did":0}}, \
						  "checkExpReplicas": {"flag":False, "run": True, "para":{"expReplicas":0}}, "checkEvictionCycle":{"flag":True, "run": True, "para":{"did":0}}, \
						  "checkBalanceNode": {"flag":True, "run": True, "para":{"maxSkew":2}}}

# A list of field in the typedef, need to be synced with dataType.pml. TODO: could auto-populate this.
# TODO: adding the process on affinityrules, noschedulenodes, etc.
elements_required = {"nodes" : ["id", "name", "cpu", "cpuLeft", "memory", "memLeft", "status", "numPod", "labels", "score", "curScore", "curAffinity", "curTaint", "maintained"], \
					 "pods" : ["id", "loc", "status", "cpu", "memory", "workloadType", "workloadId", "podTemplateId", "score", "important", "curCpuIndex", "startTime"], \
					 "d" : ["id", "name", "status", "replicaSets", "curVersion", "specReplicas", "replicas",  "maxSurge", "maxUnavailable", "strategy", "podTemplateId", "hpaSpec"], \
					"podTemplates" : ["cpuRequested", "memRequested", "numRules", "nodeName", "numNoScheduleNode", "numPreferNoScheduleNode", "numTopoSpreadConstraints", \
									"topoSpreadConstraints", "maxCpuChange"],\
					"deploymentTemplates" : ["name", "maxSurge", "maxUnavailable", "specReplicas", "strategy"]}

# according to https://github.com/kubernetes/kubernetes/blob/master/pkg/apis/apps/v1/defaults.go#L32, https://github.com/kubernetes/kubernetes/blob/master/pkg/apis/core/v1/defaults.go#L208
# All the id are now initilized with 0, as it's not quite been used in the model, but keeping this field for future usage. 
default_values = { 
	"nodes" : {"id": 0, "score" : 0, "curScore" : 0, "curAffinity" : 0, "curTaint" : 0, "labels" : None, "maintained" : 0}, \
	# curCpuIndex is set to 1 because the first value is always the initial CPU value and shouldn't be used for CPU change --- won't affect result but will affect performance.
	"pods" : {"id": 0, "status" : 0, "loc" : 0, "podTemplateId" : 0, "important" : 0, "workloadType" : 0, "workloadId" : 0, "score" : 0, "cpu" : 0, "memory" : 0, "curCpuIndex" : 1, "startTime" : 0}, \
	# maxReplicas must be defined by users
	"d": {"id": 0, "curVersion" : 0, "status" : 0, "specReplicas" : 1, "maxSurge" : 25, "maxUnavailable" : 25, "strategy" : 1, "hpaSpec" : {"isEnabled" : 0, "numMetrics" : 0, "minReplicas" : 1}}, \
	# https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#internal-default-constraints
	# The definiation is in plugin.go, variable systemDefaultConstraints 
	# The default selector for topoSpreadConstraints should be the same as the pod labels in metadata.
	"podTemplates" : {"numRules" : 0, "nodeName" : 0,  "numNoScheduleNode" : 0, "numPreferNoScheduleNode" : 0, "topoSpreadSystemDefaulted": 1, "numTopoSpreadConstraints" : 2, \
					  "cpuRequested": 0, "memRequested": 0, "topoSpreadConstraints" : [{"maxSkew" : 3, "topologyKey" : "hostname", "whenUnsatisfiable" : 1, "labels" : None}, \
					  {"maxSkew" : 5, "topologyKey" : "zone", "whenUnsatisfiable" : 1, "labels" : None}], "maxCpuChange" : 0}, \
	"deploymentTemplates" : {"maxSurge" : 25, "maxUnavailable" : 25, "specReplicas" : 1, "strategy" : 1}
}

# TODO: add default for nodeAffinityPolicy, and nodeTaintsPolicy
default_controllers = ["hpa", "scheduler", "deployment"]

#default_configs = {"scheduler" : {"pod_spread": {"nodeInclusionPolicyInPodTopologySpread" : 1, "minDomainsInPodTopologySpread" : 0}}}

# according to the plugins in this section: https://github.com/kubernetes-sigs/descheduler#example-policy. Only list things that we support.
# map each plugin to balance or deschedule, and a unique number in the pml
descheduler_plugins_maps = {"balance":{"RemoveDuplicates":1, "RemovePodsViolatingTopologySpreadConstraint":2}, "deschedule":{}}
descheduler_args_default = {"evictSystemCriticalPods" : 0, "constraintsTopologySpread" : 0}

# TODO: add default for descheduler
controller_para_default = {"descheduler" : {"configs": {"maxNoOfPodsToEvictPerNode" : 5000, "maxNoOfPodsToEvictPerNamespace" : 5000, "MAX_NUM_DESPLUGINS" : 1,\
											  "MAX_NUM_BALPLUGINS":1, "DES_PROFILE_NUM":1}}}

default_parameter_order = {
	"eventCpuChange" : ["targetDeployment"], "maintenance" : ["p"], "podCpuChangeWithPattern" : ["targetDeployment"]
}

event_uc_default_str = {
	"kernelPanic" : "for (i : 1 .. NODE_NUM) { \n run kernelPanic(i);\n}\n"
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
					ptcon["labels"] = deepcopy(pt["labels"])

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
							r[e] = deepcopy(default_values[resource][e])
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
