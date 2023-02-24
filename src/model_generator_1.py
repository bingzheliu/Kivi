
import json

# required to define for the verification, not for the config from the user. 

elements_required = {"nodes" : ["id", "name", "zone", "cpu", "cpuLeft", "memory", "memLeft", "status", "numPod"], \
					 "pods" : ["id", "loc", "status", "deploymentId", "cpu", "memory", "important"], \
					 "d" : ["id", "status", "replicaSets", "curVersion", "minReplicas", "maxReplicas", "specReplicas", \
					 					"replicas", "cpuRequested", "memRequested", "maxSurge", "maxUnavailable", "strategy", \
										"numRules", "nodeName", "numNoScheduleNode", "numPreferNoScheduleNode", "hpaSpec"]}

default_values = { 
	"nodes" : {}, \
	"pods" : {"status" : 0, "important" : 0}, \
	"d": { "curVersion" : 0, "maxSurge" : 25, "maxUnavailable" : 25, "strategy" : 1, "numRules" : 0, "nodeName" : 0,  \
					"numNoScheduleNode" : 0, "numPreferNoScheduleNode" : 0, "hpaSpec" : {"isEnabled" : 0, "numMetrics" : 0}},
}

default_controllers = ["hpa", "scheduler", "deployment"]

def check_for_completion(json_config):
	for resource in elements_required:
		for e in elements_required[resource]:
			for r in json_config[resource]:
				if e not in r:
					if e in default_values[resource]:
						r[e] = default_values[resource][e]
						print("Filling in default value for " + e, r[e])
					else:
						print(e + " has not been defined!")

def generate_deployment_init(s_init):
	i = 1
	other_type = ["replicaSets", "hpaSpec", "affinityRules", "noScheduleNode", "preferNoScheduleNode"]
	for d in json_config["d"]:
		for e in d:
			if e not in other_type:
				s_init += ("d[" + str(i) + "]." + e + " = " + str(d[e]) + "\n" )

		# assuming the first one is the default version
		for e in d["replicaSets"][0]:
			if e == "podIds":
				k = 0
				# TODO: may need to fill 0 into the rest of the array if that affect the performance
				for p in d["replicaSets"][0][e]:
					s_init += ("d[" + str(i) + "].replicaSets[0].podIds[" + str(k) + "] = " + str(p) + "\n" )
					k += 1
				s_init += ("d[" + str(i) + "].replicaSets[0].podIds[" + str(k) + "] = " + str(0) + "\n" )
			else:
				s_init += ("d[" + str(i) + "].replicaSets[0]." + e + " = " + str(d["replicaSets"][0][e]) + "\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].id" + " = " + str(d["replicaSets"][1]["id"]) + "\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].deploymentId" + " = " + str(i) + "\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].replicas = 0\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].specReplicas = 0\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].version = 0\n" )
		s_init += ("d[" + str(i) + "].replicaSets[1].podIds[0] = 0\n" )

		s_init += ("d[" + str(i) + "].hpaSpec.isEnabled = " + str(d["hpaSpec"]["isEnabled"]) + "\n" )
		s_init += ("d[" + str(i) + "].hpaSpec.numMetrics = " + str(d["hpaSpec"]["numMetrics"]) + "\n" )
		if d["hpaSpec"]["isEnabled"] == 1:
			k = 0
			for j in d["hpaSpec"]["metricNames"]:
				s_init += ("d[" + str(i) + "].hpaSpec.metricNames[" + str(k) + "] = " + str(j) + "\n" )
				k += 1

			k = 0
			for j in d["hpaSpec"]["metricTargets"]:
				s_init += ("d[" + str(i) + "].hpaSpec.metricTargets[" + str(k) + "] = " + str(j) + "\n" )
				k += 1

			k = 0
			for j in d["hpaSpec"]["metricTypes"]:
				s_init += ("d[" + str(i) + "].hpaSpec.metricTypes[" + str(k) + "] = " + str(j) + "\n" )
				k += 1

		if d["numRules"] > 0:
			k = 0
			for a in d["affinityRules"]:
				s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].isRequired = " + str(a["isRequired"]) + "\n" )
				s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].weight = " + str(a["weight"]) + "\n" )
				s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].numMatchedNode = " + str(a["numMatchedNode"]) + "\n" )
				j = 0
				for mn in a["matchedNode"]:
					s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].matchedNode[" + str(j) +  "] = " + str(mn) + "\n" )
					j += 1
				s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].matchedNode[" + str(j) +  "] = " + str(0) + "\n" )
				k += 1

		for e in ["noScheduleNode", "preferNoScheduleNode"]:
			if e in d:
				k = 0
				for n in d[e]:
					s_init += ("d[" + str(i) + "]." + e + "[" + str(k) + "] = " + str(n) + "\n" )
					k += 1
				s_init += ("d[" + str(i) + "]." + e + "[" + str(k) + "] = " + str(0) + "\n" )

		i += 1

	return s_init, i-1

def generate_node_init(s_init):
	i = 1
	for node in json_config["nodes"]:
		for e in node:
			s_init += ("nodes[" + str(i) + "]." + e + " = " + str(node[e]) + "\n")
		s_init += ("nodes[" + str(i) + "].score = 0\n")
		s_init += ("nodes[" + str(i) + "].curScore = 0\n")
		i += 1

	return s_init, i-1

def generate_pod_init(s_init):
	i = 1 
	for pod in json_config["pods"]:
		for e in pod:
			s_init += ("pods[" + str(i) + "]." + e + " = " + str(pod[e]) + "\n")
		s_init += ("pods[" + str(i) + "].score = 0\n")
		i += 1

	return s_init, i-1

default_parameter_order = {
	"eventCpuChange" : ["targetDeployment"]
}
def generate_controllers_events(s_proc):
	for c in json_config["controllers"]:
		if c not in default_controllers:
			s_proc += ("run " + c + "();\n")

	for c in json_config["events"]:
		c_para = ""
		for para in default_parameter_order[c]:
			#print(c, para, c_para)
			c_para += (str(json_config["events"][c][para]) + ",")
		c_para = c_para[0:-1]
		#print(c_para)
		s_proc += ("run " + c + "(" + c_para + ");\n")

	return s_proc

def generate_model(json_config, pml_config, pml_main):
	check_for_completion(json_config)

	s_init = ""
	s_init, node_num = generate_node_init(s_init)
	s_init, pod_num = generate_pod_init(s_init)
	s_init, deployment_num = generate_deployment_init(s_init)
	
	print(s_init, node_num, pod_num, deployment_num)

	s_proc = ""
	s_proc = generate_controllers_events(s_proc)

	print(s_proc)
	
	pml_main = pml_main.replace("[$INIT_SETUP]", s_init) \
					   .replace("[$CONTROLLERS]", s_proc)

	pml_config = pml_config.replace("[$MAX_POD]", str(pod_num+3)) \
						   .replace("[$NODE_NUM]", str(node_num)) \
						   .replace("[$POD_NUM]", str(pod_num)) \
						   .replace("[$MAX_NODE]", str(node_num+3)) \
						   .replace("[$MAX_DEPLOYMENT]", str(deployment_num+3))

	return pml_config, pml_main

	# with open("templete.pml", "r") as f:
	# 	pml = f.read()
	# 	pml = pml.replace("[$NODE_NUM]", str(len(hosts))) \
	# 			 .replace("[$EDGE_NUM]", str(len(G.edges()))) \
	# 			 .replace("[$LINK_FAILURE]", str(link_failure)) \
	# 			 .replace("[$MIN_NODE]", str(2)) \
	# 			 .replace("[$ASSERT1]", assert_rechiable_node) \
	# 			 .replace("[$EDGE_CAN_FAIL_INIT]", "")

	# 	fw = open("update_rollout_controller_fattree"+str(k)+".pml", "w")
	# 	fw.write(pml)

if __name__ == '__main__':
	with open('configs/case1.json') as f:
		json_config = json.load(f)

	with open("templates/config.pml") as f:
		pml_config =f.read()

	with open("templates/main.pml") as f:
		pml_main =f.read()

	pml_config, pml_main = generate_model(json_config, pml_config, pml_main)

	with open("temp/config.pml", "w") as f:
		f.write(pml_config)

	with open("temp/main.pml", "w") as f:
		f.write(pml_main)


