import json
from processing_default import *
from case_generator import *

# TODO: generator can be smarter, by recognizing the types, and process them iterative. 
def array_generate(dic, key, dic_str, index, s_init):
	if key in dic:
		k = 0
		for n in dic[key]:
			s_init += (dic_str + "[" + str(index) + "]." + key + "[" + str(k) + "] = " + str(n) + "\n" )
			k += 1
		s_init += (dic_str + "[" + str(index) + "]." + key + "[" + str(k) + "] = " + str(0) + "\n" )

	return s_init

def generate_pod_template_init(json_config, s_init):
	i = 1
	other_type = ["affinityRules", "noScheduleNode", "preferNoScheduleNode", "labelKeyValue", "topoSpreadConstraints"]
	for pt in json_config["podTemplates"]:
		for e in pt:
			if e not in other_type:
				s_init += ("podTemplates[" + str(i) + "]." + e + " = " + str(pt[e]) + "\n" )

		for e in ["noScheduleNode", "preferNoScheduleNode", "labelKeyValue"]:
			s_init = array_generate(pt, e, "podTemplates", i, s_init)

		if pt["numRules"] > 0:
			k = 0
			for a in pt["affinityRules"]:
				s_init += ("podTemplates[" + str(i) + "].affinityRules[" + str(k) + "].isRequired = " + str(a["isRequired"]) + "\n" )
				s_init += ("podTemplates[" + str(i) + "].affinityRules[" + str(k) + "].weight = " + str(a["weight"]) + "\n" )
				s_init += ("podTemplates[" + str(i) + "].affinityRules[" + str(k) + "].numMatchedNode = " + str(a["numMatchedNode"]) + "\n" )
				j = 0
				for mn in a["matchedNode"]:
					s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].matchedNode[" + str(j) +  "] = " + str(mn) + "\n" )
					j += 1
				s_init += ("d[" + str(i) + "].affinityRules[" + str(k) + "].matchedNode[" + str(j) +  "] = " + str(0) + "\n" )
				k += 1

		if pt["numTopoSpreadConstraints"] > 0:
			j = 0
			other_type_pt = ["labelKey", "labelValue"]
			for tcon in pt["topoSpreadConstraints"]:
				for e in tcon:
					if e not in other_type_pt:
						s_init += ("podTemplates[" + str(i) + "].topoSpreadConstraints[" + str(j) + "]." + e + " = " + str(tcon[e]) + "\n" )

					else: 
						k = 0
						for n in tcon[e]:
							s_init += ("podTemplates[" + str(i) + "].topoSpreadConstraints[" + str(j) + "]." + e + "[" + str(k) + "] = " + str(n) + "\n" )
							k += 1
						s_init += ("podTemplates[" + str(i) + "].topoSpreadConstraints[" + str(j) + "]." + e + "[" + str(k) + "] = " + str(0) + "\n" )

				j += 1


		i += 1

	return s_init, i-1


def generate_deployment_init(json_config, s_init):
	i = 1
	other_type = ["replicaSets", "hpaSpec"]
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

		i += 1

	return s_init, i-1

def generate_node_init(json_config, s_init):
	i = 1
	for node in json_config["nodes"]:
		for e in node:
			# TODO: instead of getting an array from json, get the actual label processed here instead. 
			if e == "labelKeyValue":
				for l in range(0, len(node[e])):
					s_init += ("nodes[" + str(i) + "].labelKeyValue[" + str(l) + "] = " + str(node[e][l]) + "\n")
			else:
				s_init += ("nodes[" + str(i) + "]." + e + " = " + str(node[e]) + "\n")

		i += 1


	return s_init, i-1

def generate_pod_init(json_config, s_init):
	i = 1 
	for pod in json_config["pods"]:
		for e in pod:
			s_init += ("pods[" + str(i) + "]." + e + " = " + str(pod[e]) + "\n")
		i += 1

	return s_init, i-1


def generate_controllers_events(s_proc):
	if "controllers" in json_config:
		for c in json_config["controllers"]:
			if c not in default_controllers:
				s_proc += ("run " + c + "();\n")

	if "events" in json_config:
		for c in json_config["events"]:
			c_para = ""
			for para in default_parameter_order[c]:
				#print(c, para, c_para)
				c_para += (str(json_config["events"][c][para]) + ",")
			c_para = c_para[0:-1]
			#print(c_para)
			s_proc += ("run " + c + "(" + c_para + ");\n")

	return s_proc

def generate_user_command(s_user_command):
	if "userCommand" in json_config:
		for c in json_config["userCommand"]:
			s_user_command += ("run " + str(c) + "(" + str(json_config["userCommand"][c]) + ");\n")
			
	return s_user_command

def generate_model(json_config, pml_config, pml_main):
	check_for_completion_add_default(json_config)

	s_init = ""
	s_init, node_num = generate_node_init(json_config, s_init)
	s_init, pod_num = generate_pod_init(json_config, s_init)
	s_init, deployment_num = generate_deployment_init(json_config, s_init)
	s_init, pt_num = generate_pod_template_init(json_config, s_init)
	
	#print(s_init, node_num, pod_num, deployment_num, pt_num)

	s_proc = ""
	s_proc = generate_controllers_events(s_proc)

	s_user_command = ""
	s_user_command = generate_user_command(s_user_command)

	#print(s_proc, s_user_command)
	
	pml_main = pml_main.replace("[$INIT_SETUP]", s_init) \
					   .replace("[$CONTROLLERS]", s_proc) \
					   .replace("[$USER_COMMAND]", s_user_command)

	pml_config = pml_config.replace("[$MAX_POD]", str(pod_num+3)) \
						   .replace("[$NODE_NUM]", str(node_num)) \
						   .replace("[$POD_NUM]", str(pod_num)) \
						   .replace("[$MAX_NODE]", str(node_num+3)) \
						   .replace("[$MAX_DEPLOYMENT]", str(deployment_num+3)) \
						   .replace("[$DEP_NUM]", str(deployment_num)) \
						   .replace("[$POD_TEMPLATE_NUM]", str(pt_num+2)) 

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
	file_base = sys.argv[1]
	case_id = sys.argv[2]
	scale = sys.argv[3]

	filename = file_base + "/configs/" + str(sys.argv[2]) + "_" + str(sys.argv[3]) + ".json"
	case_generator(filename, case_id, scale)

	with open(filename) as f:
		json_config = json.load(f)

	with open(file_base + "/templates/config.pml") as f:
		pml_config =f.read()

	with open(file_base + "/templates/main.pml") as f:
		pml_main =f.read()

	pml_config, pml_main = generate_model(json_config, pml_config, pml_main)

	with open(file_base + "/temp/config.pml", "w") as f:
		f.write(pml_config)

	with open(file_base + "/temp/main.pml", "w") as f:
		f.write(pml_main)


