


##### Pod Topo Spreading Plugins
# implement filterTopologySpreadConstraints and buildDefaultConstraints in common.go
# deal with enableMatchLabelKeysInPodTopologySpread
# deal with defaultValue for podSpreadPolicy



# required to define for the verification, not for the config from the user. 
# TODO: deal with the labels
# TODO: check if we need to init the score -- if this benefit verification perf or not
# TODO: putting all the default value definition into the same file

# A list of field in the typedef, need to be synced with dataType.pml. TODO: could auto-populate this.
# TODO: adding the process on affinityrules, noschedulenodes, etc.
elements_required = {"nodes" : ["id", "name", "cpu", "cpuLeft", "memory", "memLeft", "status", "numPod", "labelKeyValue", "score", "curScore", "curAffinity", "curTaint"], \
					 "pods" : ["id", "loc", "status", "cpu", "memory", "workloadType", "workloadId", "podTemplateId", "score", "important"], \
					 "d" : ["id", "status", "replicaSets", "curVersion", "minReplicas", "maxReplicas", "specReplicas", \
					 					"replicas",  "maxSurge", "maxUnavailable", "strategy", "podTemplateId", "hpaSpec"],
					"podTemplates" : ["labelKeyValue", "cpuRequested", "memRequested", "numRules", "nodeName", "numNoScheduleNode", "numPreferNoScheduleNode", "numTopoSpreadConstraints", "topoSpreadConstraints"]}


default_values = { 
	"nodes" : {"score" : 0, "curScore" : 0, "curAffinity" : 0, "curTaint" : 0, "labelKeyValue" : [0, 0]}, \
	"pods" : {"status" : 0, "important" : 0, "workloadType" : 0, "workloadId" : 0, "score" : 0, "cpu" : 0, "memory" : 0, "labelKeyValue" : [0, 0]}, \
	"d": { "curVersion" : 0, "maxSurge" : 25, "maxUnavailable" : 25, "strategy" : 1, "hpaSpec" : {"isEnabled" : 0, "numMetrics" : 0}},
	# https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#internal-default-constraints
	# TODO: check if need to set the minDomains. 
	"podTemplates" : {"numRules" : 0, "nodeName" : 0,  "numNoScheduleNode" : 0, "numPreferNoScheduleNode" : 0, "numTopoSpreadConstraints" : 2, \
					  "topoSpreadConstraints" : [{"maxSkew" : 3, "topologyKey" : 0, "whenUnsatisfiable" : 1}, {"maxSkew" : 5, "topologyKey" : 2, "whenUnsatisfiable" : 1}]}
}

# TODO: add default for nodeAffinityPolicy, and nodeTaintsPolicy
default_controllers = ["hpa", "scheduler", "deployment"]

default_configs = {"scheduler" : {"pod_spread": {"nodeInclusionPolicyInPodTopologySpread" : 1, "minDomainsInPodTopologySpread" : 0}}}


default_parameter_order = {
	"eventCpuChange" : ["targetDeployment"]
}

def pod_pread_default(json_config):
	for pt in json_config["podTemplates"]:
		if pt["numTopoSpreadConstraints"] > 0:
			for ptcon in pt["topoSpreadConstraints"]:
				if "nodeAffinityPolicy" not in ptcon:
					ptcon["nodeAffinityPolicy"] = 1
				if "nodeTaintsPolicy" not in ptcon:
					ptcon["nodeTaintsPolicy"] = 0

# TODO: check if the array size match with the number
def check_for_completion_add_default(json_config):
	for resource in elements_required:
		for e in elements_required[resource]:
			for r in json_config[resource]:
				if e not in r:
					if e in default_values[resource]:
						r[e] = default_values[resource][e]
						#print("Filling in default value for " + e, r[e])
					else:
						print(e + " has not been defined!")

	pod_pread_default(json_config)



# TODO: in the future when writing a parser for an actual config, need to implement the following func:
# 1. generate default labels. 
