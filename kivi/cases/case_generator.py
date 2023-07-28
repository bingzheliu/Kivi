#	Author: Bingzhe Liu, 02/21/2023
# 	This program generate a json configuration for a cluster setup for verification, from many pre-defined failure cases. 
#	1. Will generate extra pods if these pods are needed in the failure cases. But won't generate more than predicted number. Those will be left for the model generator.
#   2. Will not generate default values. They are generated by model generator
from util import *

def generate_a_pod(case_config, cur_id, loc, cpu, memory, status, deployment_to_pod=None):
	cur_pod = {}
	cur_pod["id"] = cur_id
	cur_id += 1

	cur_pod["loc"] = loc
	 
	cur_pod["workloadType"] = 1
	cur_pod["workloadId"] = 1
	cur_pod["podTemplateId"] = 1

	cur_pod["status"] = status

	cur_pod["cpu"] = cpu
	cur_pod["memory"] = memory
	cur_pod["important"] = 0

	case_config["setup"]["pods"].append(cur_pod)

	if status == 1 and deployment_to_pod is not None:
		deployment_to_pod[1].append(len(case_config["setup"]["pods"]))

	return case_config, cur_id

def generate_S1(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	case_config["setup"] = {}

	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["labels"] = {"name" : "app"}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 8
	pt["maxCpuChange"] = 1
	pt["curCpuRequest"] = []
	pt["curCpuRequest"].append(8)
	pt["timeCpuRequest"] = []
	pt["timeCpuRequest"].append(0)

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	## Generate Nodes and pods
	## Three types of nodes, 1 pod (*3), 3 pods (*1), and 5 pods (*1)
	case_config["setup"]["nodes"] = []
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []
	num_pod = 0
	for i in range(0, int(num_node*3/5)):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 60
		cur_node["memLeft"] = 60
		cur_node["numPod"] = 1
		case_config, cur_id = generate_a_pod(case_config, cur_id, i+1, 8, 8, 1, deployment_to_pod)
		num_pod += 1

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)

	for i in range(0, int(num_node/5)):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 38
		cur_node["memLeft"] = 38
		cur_node["numPod"] = 3
		for j in range(0,3):
			case_config, cur_id = generate_a_pod(case_config, cur_id, i+int(num_node*3/5)+1, 8, 8, 1, deployment_to_pod)
		num_pod += 3

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)

	for i in range(0, int(num_node/5)):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 30
		cur_node["memLeft"] = 30
		cur_node["numPod"] = 4
		for j in range(0,4):
			case_config, cur_id = generate_a_pod(case_config, cur_id, i+int(num_node*4/5)+1, 8, 8, 1, deployment_to_pod)
		num_pod += 4

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)

	# genreate 3 spare pods
	for i in range(3):
		case_config, cur_id = generate_a_pod(case_config, cur_id, 0, 8, 8, 0)

	## Generate Deployment
	d_id = 0
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	d_id = cur_id
	cur_id += 1
	d["status"] = 1
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = num_pod
	rp["specReplicas"] = num_pod
	rp["version"] = 0
	rp["podIds"] = []
	for v in deployment_to_pod[1]:
		rp["podIds"].append(v)
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = num_pod
	d["replicas"] = num_pod

	d["podTemplateId"] = 1

	case_config["setup"]["d"].append(d)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}
	# enter descheduler plugin from here.
	case_config["controllers"]["descheduler"] = {"profiles" : [{"RemoveDuplicates":{}}]}

	case_config["events"] = []

	case_config["intents"] = []
	if not non_violation:
		case_config["intents"].append("run checkH1()\n")


	return case_config


## HPA + scheduler (pod spreading) + deployment controller + CPU change
def generate_S3_template(num_node):
	case_config = {}
	case_config["userDefined"] = {}

	## Generate Nodes
	case_config["userDefined"]["nodesScaleType"] = "proportion"
	case_config["userDefined"]["nodesTypes"] = []
	cur_node = {}
	cur_node["template"] = {}
	cur_node["template"]["cpu"] = 32
	cur_node["template"]["memory"] = 64
	cur_node["template"]["cpuLeft"] = 64
	cur_node["template"]["memLeft"] = 64
	cur_node["template"]["numPod"] = 0
	cur_node["template"]["status"] = 1
	cur_node["template"]["labels"] = {"zone" : 2}
	cur_node["upperBound"] = 5
	cur_node["lowerBound"] = 1
	# The propotion to other nodes 
	cur_node["proportion"] = 1
	case_config["userDefined"]["nodesTypes"].append(cur_node)

	cur_node = {}
	cur_node["template"] = {}
	cur_node["template"]["cpu"] = 32
	cur_node["template"]["memory"] = 64
	cur_node["template"]["cpuLeft"] = 64
	cur_node["template"]["memLeft"] = 64
	cur_node["template"]["numPod"] = 0
	cur_node["template"]["status"] = 1
	cur_node["template"]["labels"] = {"zone" : 1}
	cur_node["upperBound"] = 5
	cur_node["lowerBound"] = 1
	cur_node["proportion"] = 2
	case_config["userDefined"]["nodesTypes"].append(cur_node)

	## Generate Pods
	#### We don't have pod type seperately, and assume they belongs to a deployment for now

	## Generate Deployment
	#### We can't model when deployment have multiple versions. 
	case_config["userDefined"]["dScaleType"] = "proportion"
	case_config["userDefined"]["dTypes"] = []
	d = {}
	d["template"] = {}
	d["template"]["status"] = 0
	d["lowerBound"] = 1
	d["upperBound"] = 8
	# propotion to other deployments
	d["proportion"] = 1
	# propotioin to # of all nodes (scale)
	d["proportionHPA"] = 2

	d["template"]["podTemplateId"] = 1
	d["template"]["hpaSpec"] = {}
	d["template"]["hpaSpec"]["isEnabled"] = 1
	d["template"]["hpaSpec"]["numMetrics"] = 1
	d["template"]["hpaSpec"]["metricNames"] = []
	d["template"]["hpaSpec"]["metricNames"].append(0)
	d["template"]["hpaSpec"]["metricTargets"] = []
	d["template"]["hpaSpec"]["metricTargets"].append(100)
	d["template"]["hpaSpec"]["metricTypes"] = []
	d["template"]["hpaSpec"]["metricTypes"].append(1)

	case_config["userDefined"]["dTypes"].append(d)

	
	case_config["setup"] = {}
	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 16

	# default labels should be generated by model generator, saving the first 2 index for default
	pt["labels"] = {"name" : "app"}
	pt["numTopoSpreadConstraints"] = 2
	pt["topoSpreadConstraints"] = []
	ptcon = {}
	ptcon["maxSkew"] = 1
	ptcon["minDomains"] = 2
	# based on node name
	ptcon["topologyKey"] = "hostname"
	ptcon["whenUnsatisfiable"] = 0
	ptcon["numMatchedLabel"] = 1
	ptcon["labels"] = {"name" : "app"}

	pt["topoSpreadConstraints"].append(deepcopy(ptcon))
	# based on zone name
	ptcon["topologyKey"] = "zone"
	pt["topoSpreadConstraints"].append(deepcopy(ptcon))
	case_config["setup"]["podTemplates"].append(pt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	case_config["events"] = []
	case_config["events"].append({"name":"eventCpuChange", "after_stable":True, "para": {"targetDeployment":1}})

	return case_config

def generate_H1_template(num_node):
	case_config = {}
	case_config["userDefined"] = {}

	## Generate Nodes
	case_config["userDefined"]["nodesScaleType"] = "proportion"
	case_config["userDefined"]["nodesTypes"] = []
	cur_node = {}
	cur_node["template"] = {}
	cur_node["template"]["cpu"] = 64
	cur_node["template"]["memory"] = 64
	cur_node["template"]["cpuLeft"] = 64
	cur_node["template"]["memLeft"] = 64
	cur_node["template"]["numPod"] = 0
	cur_node["template"]["status"] = 1
	cur_node["upperBound"] = 3
	cur_node["lowerBound"] = 1
	# The propotion to other nodes 
	cur_node["proportion"] = 1
	case_config["userDefined"]["nodesTypes"].append(cur_node)

	# cur_node = {}
	# cur_node["template"] = {}
	# cur_node["template"]["cpu"] = 64
	# cur_node["template"]["memory"] = 64
	# cur_node["template"]["cpuLeft"] = 64
	# cur_node["template"]["memLeft"] = 64
	# cur_node["template"]["numPod"] = 0
	# cur_node["template"]["status"] = 1
	# cur_node["upperBound"] = 4
	# cur_node["lowerBound"] = 1
	# cur_node["proportion"] = 1
	# case_config["userDefined"]["nodeTypes"].append(cur_node)

	## Generate Pods
	#### We don't have pod type seperately, and assume they belongs to a deployment for now

	## Generate Deployment
	#### We can't model when deployment have multiple versions. 
	case_config["userDefined"]["dScaleType"] = "proportion"
	case_config["userDefined"]["dTypes"] = []
	d = {}
	d["template"] = {}
	d["template"]["status"] = 0
	d["lowerBound"] = 1
	d["upperBound"] = 5
	# propotion to other deployments
	d["proportion"] = 1
	# propotioin to # of all nodes (scale)
	d["proportionHPA"] = 2

	d["template"]["podTemplateId"] = 1
	d["template"]["hpaSpec"] = {}
	d["template"]["hpaSpec"]["isEnabled"] = 1
	d["template"]["hpaSpec"]["numMetrics"] = 1
	d["template"]["hpaSpec"]["metricNames"] = []
	d["template"]["hpaSpec"]["metricNames"].append(0)
	d["template"]["hpaSpec"]["metricTargets"] = []
	d["template"]["hpaSpec"]["metricTargets"].append(50)
	d["template"]["hpaSpec"]["metricTypes"] = []
	d["template"]["hpaSpec"]["metricTypes"].append(1)

	case_config["userDefined"]["dTypes"].append(d)

	# d = {}
	# d["template"] = {}
	# d["template"]["status"] = 0
	# d["lowerBound"] = 1
	# d["upperBound"] = 5
	# d["proportion"] = 3

	# d["template"]["podTemplateId"] = 1
	# d["template"]["hpaSpec"] = {}
	# d["template"]["hpaSpec"]["isEnabled"] = 1
	# d["template"]["hpaSpec"]["numMetrics"] = 1
	# d["template"]["hpaSpec"]["metricNames"] = []
	# d["template"]["hpaSpec"]["metricNames"].append(0)
	# d["template"]["hpaSpec"]["metricTargets"] = []
	# d["template"]["hpaSpec"]["metricTargets"].append(50)
	# d["template"]["hpaSpec"]["metricTypes"] = []
	# d["template"]["hpaSpec"]["metricTypes"].append(1)

	# case_config["userDefined"]["deploymentTypes"].append(d)

	# Generate podTemplate
	case_config["setup"] = {}
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["labels"] = {"name" : "app"}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 8
	pt["maxCpuChange"] = 2
	pt["curCpuRequest"] = []
	pt["curCpuRequest"].append(8)
	pt["curCpuRequest"].append(3)
	pt["timeCpuRequest"] = []
	pt["timeCpuRequest"].append(0)
	pt["timeCpuRequest"].append(60)

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	# case_config["userCommand"] = {}
	# case_config["userCommand"]["createTargetDeployment"] = 1

	case_config["events"] = []

	case_config["intents"] = []
	case_config["intents"].append("run checkH1()\n")

	return case_config

def generate_H1(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	case_config["setup"] = {}

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 64
		cur_node["memLeft"] = 64
		cur_node["numPod"] = 0

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)

	## Generate Pods
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []

	for i in range(0, num_node*2+5):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = 0
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		cur_pod["status"] = 0

		cur_pod["cpu"] = 8
		cur_pod["memory"] = 8
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	cur_id += 1
	d["status"] = 0
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = 0
	rp["specReplicas"] = 1 if num_node/5 < 1 else int(num_node/5)
	rp["version"] = 0
	rp["podIds"] = []
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	
	d["specReplicas"] = 1 if num_node/5 < 1 else int(num_node/5)
	d["replicas"] = 0
	d["podTemplateId"] = 1

	d["hpaSpec"] = {}
	d["hpaSpec"]["isEnabled"] = 1
	d["hpaSpec"]["numMetrics"] = 1
	d["hpaSpec"]["metricNames"] = []
	d["hpaSpec"]["metricNames"].append(0)
	d["hpaSpec"]["metricTargets"] = []
	d["hpaSpec"]["metricTargets"].append(50)
	d["hpaSpec"]["metricTypes"] = []
	d["hpaSpec"]["metricTypes"].append(1)
	d["hpaSpec"]["minReplicas"] =  1 if num_node/5 < 1 else int(num_node/5)
	d["hpaSpec"]["maxReplicas"] = num_node*2+4

	case_config["setup"]["d"].append(d)

	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["labels"] = {"name" : "app"}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 8
	pt["maxCpuChange"] = 2
	pt["curCpuRequest"] = []
	pt["curCpuRequest"].append(8)
	pt["curCpuRequest"].append(3)
	pt["timeCpuRequest"] = []
	pt["timeCpuRequest"].append(0)
	pt["timeCpuRequest"].append(60)

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	case_config["userCommand"] = []
	case_config["userCommand"].append({"name" : "createTargetDeployment", "para" : 1})

	case_config["events"] = []

	case_config["intents"] = []
	if not non_violation:
		case_config["intents"].append("run checkH1()\n")

	return case_config

def generate_S6(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	case_config["setup"] = {}

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 56
		cur_node["memLeft"] = 56
		cur_node["numPod"] = 1

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)
	
	## Generate Pods
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []

	for i in range(0, num_node+5):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = i+1
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		if i < num_node:
			cur_pod["status"] = 1
			deployment_to_pod[1].append(i+1)
		else:
			cur_pod["status"] = 0

		cur_pod["cpu"] = 8
		cur_pod["memory"] = 8
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	d_id = 0
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	d_id = cur_id
	cur_id += 1
	d["status"] = 1
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = num_node
	rp["specReplicas"] = num_node
	rp["version"] = 0
	rp["podIds"] = []
	for v in deployment_to_pod[1]:
		rp["podIds"].append(v)
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = num_node
	d["replicas"] = num_node

	d["podTemplateId"] = 1

	case_config["setup"]["d"].append(d)

	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 8
	pt["labels"] = {"name" : "app"}

	pt["numTopoSpreadConstraints"] = 1
	pt["topoSpreadConstraints"] = []
	ptcon = {}
	ptcon["maxSkew"] = 1
	ptcon["minDomains"] = 2
	# based on node name
	ptcon["topologyKey"] = "hostname"
	ptcon["whenUnsatisfiable"] = 1
	ptcon["numMatchedLabel"] = 1
	ptcon["labels"] = {"name" : "app"}

	pt["topoSpreadConstraints"].append(deepcopy(ptcon))

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	## Generate Deployment template
	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	p = 1 if num_node/5 < 1 else int(num_node/5)
	#p = 1
	case_config["events"] = []
	case_config["events"].append({"name":"maintenance", "para": {"p":p}, "after_stable":True})

	case_config["intents"] = []
	# TODO: have a more general list of user intents
	#case_config["intents"].append("\nnever \n{\n do\n  :: init_status == 1 && d[1].replicas == d[1].specReplicas -> \n if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  " -> break\n  fi\n   :: else\nod;\n}\n")
	if not non_violation:
		#case_config["intents"].append("run checkS6()\n")
		# TODO: check why never not work
		#case_config["intents"].append("\nnever \n{\n do\n  :: init_status == 1 && d[1].replicas == d[1].specReplicas -> \n if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  " -> break\n  fi\n   :: else\nod;\n}\n")
		case_config["intents"].append("\nactive proctype checkS6() \n{\nendCS61: if\n  		:: init_status == 1 && d[1].replicas == d[1].specReplicas -> \nendCS62:   		if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  ' -> printf("[*] Replicas below expatation!\\n")\n assert(false)\n    		fi\n     fi;\n}\n')


	return case_config


def generate_S6_model_fidelity(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	case_config["setup"] = {}

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 64
		cur_node["memLeft"] = 64
		cur_node["numPod"] = 0

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)
	
	## Generate Pods
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []

	for i in range(0, num_node+5):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = 0
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		cur_pod["status"] = 0

		cur_pod["cpu"] = 8
		cur_pod["memory"] = 8
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	d_id = 0
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	d_id = cur_id
	cur_id += 1
	d["status"] = 1
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = 0
	rp["specReplicas"] = num_node
	rp["version"] = 0
	rp["podIds"] = []
	for v in deployment_to_pod[1]:
		rp["podIds"].append(v)
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = num_node
	d["replicas"] = 0

	d["podTemplateId"] = 1

	case_config["setup"]["d"].append(d)

	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 8
	pt["labels"] = {"name" : "app"}

	pt["numTopoSpreadConstraints"] = 1
	pt["topoSpreadConstraints"] = []
	ptcon = {}
	ptcon["maxSkew"] = 1
	ptcon["minDomains"] = 2
	# based on node name
	ptcon["topologyKey"] = "hostname"
	ptcon["whenUnsatisfiable"] = 1
	ptcon["numMatchedLabel"] = 1
	ptcon["labels"] = {"name" : "app"}

	pt["topoSpreadConstraints"].append(deepcopy(ptcon))

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	## Generate Deployment template
	case_config["setup"]["deploymentTemplates"] = []
	dt = {}
	dt["id"] = cur_id
	dt["name"] = d_id
	dt["specReplicas"] = num_node
	cur_id += 1
	case_config["setup"]["deploymentTemplates"].append(dt)

	## Generate Deployment template
	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	p = 1 if num_node/5 < 1 else int(num_node/5)
	#p = 1
	case_config["events"] = []
	case_config["events"].append({"name":"maintenance", "para": {"p":p}, "after_stable":True})

	case_config["intents"] = []
	# TODO: have a more general list of user intents
	#case_config["intents"].append("\nnever \n{\n do\n  :: init_status == 1 && d[1].replicas == d[1].specReplicas -> \n if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  " -> break\n  fi\n   :: else\nod;\n}\n")
	if not non_violation:
		#case_config["intents"].append("run checkS6()\n")
		# TODO: check why never not work
		#case_config["intents"].append("\nnever \n{\n do\n  :: init_status == 1 && d[1].replicas == d[1].specReplicas -> \n if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  " -> break\n  fi\n   :: else\nod;\n}\n")
		case_config["intents"].append("\nactive proctype checkS6() \n{\nendCS61: if\n  		:: init_status == 1 && d[1].replicas == d[1].specReplicas -> \nendCS62:   		if\n :: d[1].replicas < d[1].specReplicas - " + str(p) +  ' -> printf("[*] Replicas below expatation!\\n")\n assert(false)\n    		fi\n     fi;\n}\n')

	case_config["userCommand"] = []
	# this is the id for the index of deploymentTemplates, not the deployment name
	case_config["userCommand"].append({"name" : "applyDeployment", "para" : 1, "priority" : 20, "after_stable":False})

	return case_config


def generate_H2(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	case_config["setup"] = {}

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 48
		cur_node["memLeft"] = 48
		cur_node["numPod"] = 1

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)
		cur_node["labels"] = {}
		cur_node["labels"]["zone"] = 1


	## Generate Pods
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []

	for i in range(0, num_node+3):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = i+1
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		if i < num_node:
			cur_pod["status"] = 1
			deployment_to_pod[1].append(i+1)
		else:
			cur_pod["status"] = 0

		cur_pod["cpu"] = 16
		cur_pod["memory"] = 16
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	d_id = 0
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	d_id = cur_id
	cur_id += 1
	d["status"] = 1
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = num_node
	rp["specReplicas"] = num_node
	rp["version"] = 0
	rp["podIds"] = []
	for v in deployment_to_pod[1]:
		rp["podIds"].append(v)
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = num_node
	d["replicas"] = num_node

	d["podTemplateId"] = 1

	d["hpaSpec"] = {}
	d["hpaSpec"]["isEnabled"] = 1
	d["hpaSpec"]["numMetrics"] = 1
	d["hpaSpec"]["metricNames"] = []
	d["hpaSpec"]["metricNames"].append(0)
	d["hpaSpec"]["metricTargets"] = []
	d["hpaSpec"]["metricTargets"].append(50)
	d["hpaSpec"]["metricTypes"] = []
	d["hpaSpec"]["metricTypes"].append(1)
	d["hpaSpec"]["minReplicas"] = num_node
	d["hpaSpec"]["maxReplicas"] = num_node+2

	case_config["setup"]["d"].append(d)

	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 16
	pt["memRequested"] = 16
	pt["labels"] = {"name" : "app"}

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	## Generate Deployment template
	case_config["setup"]["deploymentTemplates"] = []
	dt = {}
	dt["id"] = cur_id
	dt["name"] = d_id
	#dt["specReplicas"] = num_node
	cur_id += 1
	case_config["setup"]["deploymentTemplates"].append(dt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	case_config["userCommand"] = []
	# this is the id for the index of deploymentTemplates, not the deployment name
	case_config["userCommand"].append({"name" : "applyDeployment", "para" : 1, "priority" : 0, "after_stable":True})

	case_config["events"] = []

	case_config["intents"] = []
	#case_config["intents"].append( "never {\n do \n:: d[1].replicas < d[1].hpaSpec.minReplicas -> break\n :: else\n od;\n}")
	if not non_violation:
		case_config["intents"].append("run checkH2()\n")
	return case_config

def generate_S4(num_node, non_violation=False):
	case_config = {}
	cur_id = 1

	case_config["setup"] = {}

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 64
		cur_node["memory"] = 64
	
		cur_node["cpuLeft"] = 64
		cur_node["memLeft"] = 64
		cur_node["numPod"] = 0

		cur_node["status"] = 1
		case_config["setup"]["nodes"].append(cur_node)

	## Generate Pods
	total_pod = 2*num_node+2
	if non_violation:
		total_pod = 2*num_node

	case_config["setup"]["pods"] = []
	for i in range(0, total_pod):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = 0
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		cur_pod["status"] = 0
	
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	cur_id += 1
	d["status"] = 0
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = 0
	rp["specReplicas"] = num_node*2+1 
	rp["version"] = 0
	rp["podIds"] = []
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	
	d["specReplicas"] = num_node*2+1
	d["replicas"] = 0
	d["podTemplateId"] = 1

	#d["hpaSpec"] = {}
	# d["hpaSpec"]["isEnabled"] = 1
	# d["hpaSpec"]["numMetrics"] = 1
	# d["hpaSpec"]["metricNames"] = []
	# d["hpaSpec"]["metricNames"].append(0)
	# d["hpaSpec"]["metricTargets"] = []
	# d["hpaSpec"]["metricTargets"].append(100)
	# d["hpaSpec"]["metricTypes"] = []
	# d["hpaSpec"]["metricTypes"].append(1)
	#d["hpaSpec"]["minReplicas"] = num_node*2+1 
	#d["hpaSpec"]["maxReplicas"] = num_node*2 + 4

	case_config["setup"]["d"].append(d)

	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["labels"] = {"name" : "app"}
	pt["cpuRequested"] = 21
	pt["memRequested"] = 21

	#pt["numTopoSpreadConstraints"] = 0
	case_config["setup"]["podTemplates"].append(pt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	case_config["userCommand"] = []
	case_config["userCommand"].append({"name" : "createTargetDeployment", "para" : 1})

	case_config["events"] = []
	case_config["events"].append({"name" : "kernelPanic"})
	return case_config

## HPA + scheduler (pod spreading) + deployment controller + CPU change
def generate_S3_woCPU(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	
	case_config["setup"] = {}

	# this case, num_node needs to be odd
	num_node = int(num_node/2)
	num_node = num_node*2 + 1

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 32
		cur_node["memory"] = 64
		cur_node["cpuLeft"] = 32
		cur_node["memLeft"] = 64
		cur_node["numPod"] = 0

		cur_node["status"] = 1

		if i > num_node/2:
			cur_node["labels"] = {"zone" : 2}
		else:
			cur_node["labels"] = {"zone" : 1}
 
		case_config["setup"]["nodes"].append(cur_node)

	## Generate Pods
	case_config["setup"]["pods"] = []
	for i in range(0, num_node*2):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = 0
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		cur_pod["status"] = 0

		cur_pod["cpu"] = 8
		cur_pod["memory"] = 16
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	d_id = 0
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	d_id = cur_id
	cur_id += 1
	d["status"] = 0
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = 0
	rp["specReplicas"] = 0
	rp["version"] = 0
	rp["podIds"] = []
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = 0
	d["replicas"] = 0

	d["podTemplateId"] = 1

	d["hpaSpec"] = {}
	d["hpaSpec"]["isEnabled"] = 1
	d["hpaSpec"]["numMetrics"] = 1
	d["hpaSpec"]["metricNames"] = []
	d["hpaSpec"]["metricNames"].append(0)
	d["hpaSpec"]["metricTargets"] = []
	d["hpaSpec"]["metricTargets"].append(50)
	d["hpaSpec"]["metricTypes"] = []
	d["hpaSpec"]["metricTypes"].append(1)
	d["hpaSpec"]["minReplicas"] = 1
	d["hpaSpec"]["maxReplicas"] = num_node*2

	case_config["setup"]["d"].append(d)

	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 16

	# default labels should be generated by model generator, saving the first 2 index for default
	pt["labels"] = {"name" : "app"}
	pt["topoSpreadConstraints"] = []
	ptcon = {}
	ptcon["maxSkew"] = 1
	ptcon["minDomains"] = 2
	# based on node name
	ptcon["topologyKey"] = "hostname"
	ptcon["whenUnsatisfiable"] = 0
	ptcon["numMatchedLabel"] = 1
	ptcon["labels"] = {"name" : "app"}

	pt["topoSpreadConstraints"].append(deepcopy(ptcon))
	# based on zone name
	ptcon["topologyKey"] = "zone"
	if not non_violation:
		pt["topoSpreadConstraints"].append(deepcopy(ptcon))
		pt["numTopoSpreadConstraints"] = 2
	else:
		pt["numTopoSpreadConstraints"] = 1
	case_config["setup"]["podTemplates"].append(pt)

	## Generate Deployment template
	case_config["setup"]["deploymentTemplates"] = []
	dt = {}
	dt["id"] = cur_id
	dt["name"] = d_id
	dt["specReplicas"] = 1
	cur_id += 1
	case_config["setup"]["deploymentTemplates"].append(dt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	# case_config["events"] = []
	# case_config["events"].append({"name":"eventCpuChange", "after_stable": True, "para" : {"targetDeployment" : 1}})

	case_config["userCommand"] = []
	# this is the id for the index of deploymentTemplates, not the deployment name
	case_config["userCommand"].append({"name" : "applyDeployment", "para" : 1, "priority" : 0, "after_stable":True})

	return case_config

## HPA + scheduler (pod spreading) + deployment controller + CPU change
def generate_S3(num_node, non_violation=False):
	case_config = {}
	cur_id = 1
	
	case_config["setup"] = {}

	# this case, num_node needs to be odd
	num_node = int(num_node/2)
	num_node = num_node*2 + 1

	## Generate Nodes
	case_config["setup"]["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_id += 1
		
		cur_node["cpu"] = 32
		cur_node["memory"] = 64
		if i == int(num_node/2):
			cur_node["cpuLeft"] = 24
			cur_node["memLeft"] = 48
			cur_node["numPod"] = 1
		else:
			cur_node["cpuLeft"] = 16
			cur_node["memLeft"] = 32
			cur_node["numPod"] = 2

		cur_node["status"] = 1

		if i > num_node/2:
			cur_node["labels"] = {"zone" : 2}
		else:
			cur_node["labels"] = {"zone" : 1}
 
		case_config["setup"]["nodes"].append(cur_node)

	## Generate Pods
	deployment_to_pod = {}
	deployment_to_pod[1] = []
	case_config["setup"]["pods"] = []
	loc = 1
	count = 0
	for i in range(0, num_node*2):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		if loc == int(num_node/2) + 1:
			cur_pod["loc"] = loc
			count = 0
			loc += 1
		else:
			cur_pod["loc"] = loc
			count += 1
			if count == 2:
				loc += 1
				count = 0
		 
		cur_pod["workloadType"] = 1
		cur_pod["workloadId"] = 1
		cur_pod["podTemplateId"] = 1

		if i < num_node*2-1:
			cur_pod["status"] = 1
			cur_pod["labels"] = {"name" : "app"}
			deployment_to_pod[1].append(i+1)
		else:
			cur_pod["status"] = 0

		cur_pod["cpu"] = 8
		cur_pod["memory"] = 16
		cur_pod["important"] = 0
		case_config["setup"]["pods"].append(cur_pod)

	## Generate Deployment
	case_config["setup"]["d"] = []
	d = {}
	d["id"] = cur_id
	d["name"] = cur_id
	cur_id += 1
	d["status"] = 1
	d["curVersion"] = 0
	d["replicaSets"] = []

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	rp["replicas"] = num_node*2 - 1
	rp["specReplicas"] = num_node*2 - 1
	rp["version"] = 0
	rp["podIds"] = []
	for v in deployment_to_pod[1]:
		rp["podIds"].append(v)
	d["replicaSets"].append(rp)

	rp = {}
	rp["id"] = cur_id
	cur_id += 1
	rp["deploymentId"] = 1
	d["replicaSets"].append(rp)

	d["specReplicas"] = num_node*2 - 1
	d["replicas"] = num_node*2 - 1

	d["podTemplateId"] = 1

	d["hpaSpec"] = {}
	d["hpaSpec"]["isEnabled"] = 1
	d["hpaSpec"]["numMetrics"] = 1
	d["hpaSpec"]["metricNames"] = []
	d["hpaSpec"]["metricNames"].append(0)
	d["hpaSpec"]["metricTargets"] = []
	d["hpaSpec"]["metricTargets"].append(91)
	d["hpaSpec"]["metricTypes"] = []
	d["hpaSpec"]["metricTypes"].append(1)
	d["hpaSpec"]["minReplicas"] = num_node*2 - 1
	d["hpaSpec"]["maxReplicas"] = num_node*4

	case_config["setup"]["d"].append(d)

	# Generate podTemplate
	case_config["setup"]["podTemplates"] = []
	pt = {}
	pt["cpuRequested"] = 8
	pt["memRequested"] = 16

	# default labels should be generated by model generator, saving the first 2 index for default
	pt["topoSpreadConstraints"] = []
	ptcon = {}
	ptcon["maxSkew"] = 1
	ptcon["minDomains"] = 2
	# based on node name
	ptcon["topologyKey"] = "hostname"
	ptcon["whenUnsatisfiable"] = 0
	ptcon["numMatchedLabel"] = 1
	ptcon["labels"] = {"name" : "app"}

	pt["topoSpreadConstraints"].append(deepcopy(ptcon))
	# based on zone name
	ptcon["topologyKey"] = "zone"
	if not non_violation:
		pt["topoSpreadConstraints"].append(deepcopy(ptcon))
		pt["numTopoSpreadConstraints"] = 2
	else:
		pt["numTopoSpreadConstraints"] = 1
	case_config["setup"]["podTemplates"].append(pt)

	case_config["controllers"] = {}
	case_config["controllers"]["scheduler"] = {}
	case_config["controllers"]["hpa"] = {}
	case_config["controllers"]["deployment"] = {}

	case_config["events"] = []
	case_config["events"].append({"name":"eventCpuChange", "after_stable": True, "para" : {"targetDeployment" : 1}})

	return case_config

def case_generator(case_id, scale, filename=None):
	from_template = False
	if int(scale) == 0:
		from_template = True
	case_fun = {False: {"s4": generate_S4, "s3" : generate_S3, "h2": generate_H2, "s6" : generate_S6, "h1" : generate_H1, "s1" : generate_S1}, \
				True: {"h1": generate_H1_template, "s3":generate_S3_template}}

	json_config = None
	if case_id in case_fun[from_template]:
		if args.case_non_violation:
			json_config = case_fun[from_template][case_id](int(scale), non_violation=True)
		else:
			json_config = case_fun[from_template][case_id](int(scale))

		if filename != None:
			with open(filename,'w') as f:
				json.dump(json_config, f, indent=4)
	else:
		if not from_template:
			logger.critical("Unkown case ID, re-try with all lower cases.")

	return json_config

def get_case_user_defined(case_id):
	user_defined_all = {"default" : {"nodes_default" : {"upperBound":10, "lowerBound":2, "ScaleType":"proportion"}, \
									"d_default" : {"upperBound":10, "lowerBound":2, "ScaleType":"proportion", "proportionHPA" : 2}}, \
						"h2" : {"nodes_default" : {"upperBound":10, "lowerBound":1, "ScaleType":"proportion"}, \
									"d_default" : {"upperBound":10, "lowerBound":1, "ScaleType":"proportion", "proportionHPA" : 2}} \
					 }
	if case_id not in user_defined_all:
		return user_defined_all["default"]
	else:
		return user_defined_all[case_id]

