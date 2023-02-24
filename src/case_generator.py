#	Author: Bingzhe Liu, 02/21/2023
# 	This program generate a json configuration for a cluster setup for verification, from many pre-defined failure cases. 
#

import json

# HPA + scheduler + deployment controller + CPU change
def generate_case1(num_node):
	case1_config = {}
	cur_id = 1

	case1_config["nodes"] = []
	for i in range(0, num_node):
		cur_node = {}
		cur_node["id"] = cur_id
		cur_node["name"] = cur_id
		cur_node["zone"] = 1
		cur_id += 1

		if i == num_node:
			cur_node["status"] = 0

		elif i < num_node-2:
			cur_node["status"] = 1
			# each pod takes 5 CPU and 10 Memory, 3 from deployment 1, 2 from deployment 2
			cur_node["cpu"] = 32
			cur_node["cpuLeft"] = 7
			cur_node["memory"] = 64
			cur_node["memLeft"] = 14
			cur_node["numPod"] = 5

		else:
			cur_node["status"] = 1
			# each pod takes 5 CPU and 10 Memory, 3 from deployment 1
			cur_node["cpu"] = 32
			cur_node["cpuLeft"] = 17
			cur_node["memory"] = 64
			cur_node["memLeft"] = 34
			cur_node["numPod"] = 3

		case1_config["nodes"].append(cur_node)

	deployment_to_pod = {}
	deployment_to_pod[1] = []
	deployment_to_pod[2] = []
	case1_config["pods"] = []
	for i in range(0, num_node*5):
		cur_pod = {}
		cur_pod["id"] = cur_id
		cur_id += 1

		cur_pod["loc"] = int(i/5)+1
		cur_did = 1 if i%5 < 3  else 2
		cur_pod["deploymentId"] = cur_did

		if cur_did == 2 and i > (num_node-2)*5:
			cur_pod["status"] = 0
		else:
			cur_pod["status"] = 1
			deployment_to_pod[cur_did].append(i+1)

		cur_pod["cpu"] = 5
		cur_pod["memory"] = 10

		cur_pod["important"] = 0
 
		case1_config["pods"].append(cur_pod)


	case1_config["d"] = []
	for i in range(0,2):
		d = {}
		d["id"] = cur_id
		cur_id += 1
		d["status"] = 1

		d["curVersion"] = 0
		d["replicaSets"] = []

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = i+1
		if i == 0:
			rp["replicas"] = num_node*3
			rp["specReplicas"] = num_node*3
		else:
			rp["replicas"] = (num_node - 2)*2
			rp["specReplicas"] = (num_node - 2)*2
		rp["version"] = 0
		rp["podIds"] = []
		for v in deployment_to_pod[i+1]:
			rp["podIds"].append(v)
		d["replicaSets"].append(rp)

		rp = {}
		rp["id"] = cur_id
		cur_id += 1
		rp["deploymentId"] = i+1
		d["replicaSets"].append(rp)

		if i == 0:
			d["minReplicas"] = num_node*3
			d["specReplicas"] = num_node*3
			d["replicas"] = num_node*3

		else:
			d["minReplicas"] = (num_node - 2)*2
			d["specReplicas"] = (num_node - 2)*2
			d["replicas"] = (num_node - 2)*2

		d["maxReplicas"] = num_node*4

		d["cpuRequested"] = 5
		d["memRequested"] = 10

		if i == 1:
			d["numNoScheduleNode"] = 2
			d["noScheduleNode"] = []
			d["noScheduleNode"].append(num_node-1)
			d["noScheduleNode"].append(num_node)

		d["hpaSpec"] = {}
		d["hpaSpec"]["isEnabled"] = 1
		d["hpaSpec"]["numMetrics"] = 1
		d["hpaSpec"]["metricNames"] = []
		d["hpaSpec"]["metricNames"].append(0)
		d["hpaSpec"]["metricTargets"] = []
		d["hpaSpec"]["metricTargets"].append(100)
		d["hpaSpec"]["metricTypes"] = []
		d["hpaSpec"]["metricTypes"].append(1)

		case1_config["d"].append(d)

	case1_config["controllers"] = {}
	case1_config["controllers"]["scheduler"] = {}
	case1_config["controllers"]["hpa"] = {}
	case1_config["controllers"]["deployment"] = {}

	case1_config["events"] = {}
	case1_config["events"]["eventCpuChange"] = {}
	case1_config["events"]["eventCpuChange"]["targetDeployment"] = 2

	with open('configs/case1.json','w') as f:
		json.dump(case1_config, f, indent=4)

def case_generator():
	generate_case1(4)


if __name__ == '__main__':
	case_generator()
