import os
import json
from datetime import datetime
import sys
from math import *
from itertools import permutations
from copy import deepcopy

sys_path = os.path.abspath(sys.argv[3])

sys.path.insert(0, sys_path+"/src")

from util import *


class Action():
	def __init__(self, name, objs, _str):
		self.name = name
		self.objs = objs
		self.str = _str
		self.objs_type = ["pod", "node"]

	def __eq__(self, other):
		if not isinstance(other, self.__class__):
			#print(isinstance(other, self.__class__), other.__class__, self.__class__)
			return False

		if self.objs != other.objs:
			return False

		return self.name == other.name 

	def __str__(self):
		s = self.__class__.__name__ + " "  + self.name 
		for obj in self.objs:
			s += (" " + obj)
		return s

	def compare_dep_name(self, d1, d2):
		d1_s = d1.split("-")
		d2_s = d2.split("-")
		
		if d1_s[:-1] == d2_s or d1_s == d2_s[:-1] or d1_s == d2_s:
			return True
		return False

class CPU_Change(Action):
	# objs is the pod name
	# name: cpu_change
	def __init__(self, name, objs, _str, direction):
		super().__init__(name, objs, _str)
		self.direction = direction
		self.objs_type = ["pod"]

	def __str__(self):
		s = self.__class__.__name__ + " " + self.name + " " + self.direction
		for obj in self.objs:
			s += (" " + obj)
		return s

	def __eq__(self, other):
		if not isinstance(other, self.__class__):
			#print(isinstance(other, self.__class__),  other.__class__, self.__class__)
			return False

		if self.objs != other.objs:
			return False
			
		return self.name == other.name and self.direction == other.direction

class Scheduler(Action):
	# objs: schdule objs[0] on objs[1]; None if failed
	# name: schedule
	def __init__(self, name, objs, _str):
		super().__init__(name, objs, _str)


class HPA(Action):
	# objs: deployment name
	# name: scale
	def __init__(self, name, objs, _str, direction, value):
		super().__init__(name, objs, _str)
		self.direction = direction
		self.value = value
		self.objs_type = ["dep"]

	def __str__(self):
		s = self.__class__.__name__ + " " + self.name + " " + self.direction + " " + self.value
		for obj in self.objs:
			s += (" " + obj)
		return s

	def __eq__(self, other):
		if not isinstance(other, self.__class__):
			#print(isinstance(other, self.__class__),  other.__class__, self.__class__)
			return False

		if not self.compare_dep_name(self.objs[0], other.objs[0]):
			#print(self.objs[0], other.objs[0])
			return False
			
		return self.name == other.name and self.direction == other.direction

class Maintenance(Action):
	# objs: node name
	# name: start, end
	def __init__(self, name, objs, _str):
		super().__init__(name, objs, _str)
		self.objs_type = ["node"]

	def __str__(self):
		s = self.__class__.__name__ + " " + self.name 
		for obj in self.objs:
			s += (" " + obj)
		return s

	def __eq__(self, other):
		if not isinstance(other, self.__class__):
			#print(isinstance(other, self.__class__),other.__class__, self.__class__)
			return False

		if not self.compare_dep_name(self.objs[0], other.objs[0]):
			print(self.objs[0], other.objs[0])
			return False
			
		return self.name == other.name 


class Deployment(Action):
	# objs: deployment name
	# name: scale, create
	def __init__(self, name, objs, _str, direction=None, value=None):
		super().__init__(name, objs, _str)
		self.direction = direction
		self.value = value
		self.objs_type = ["dep"]

	def __str__(self):
		s = self.__class__.__name__ + " " + self.name 
		if self.direction is not None:
			s += (" " + self.direction + " " + self.value)
		for obj in self.objs:
			s += (" " + obj)
		return s

	def __eq__(self, other):
		if not isinstance(other, self.__class__):
			#print(isinstance(other, self.__class__),other.__class__, self.__class__)
			return False

		if not self.compare_dep_name(self.objs[0], other.objs[0]):
			print(self.objs[0], other.objs[0])
			return False
			
		return self.name == other.name and self.direction == other.direction


class Kubelet(Action):
	# objs: place pod objs[0] on node objs[1]
	# name: start_container
	def __init__(self, name, objs, _str):
		super().__init__(name, objs, _str)

class Apply_Dep(Action):
	# objs: deployment
	# name: apply_dep
	def __init__(self, name, objs, _str):
		super().__init__(name, objs, _str)
		self.objs_type = ["dep"]

class Model_Fidelity:
	cpu_threshold = 10
	related_t = ["firstTimestamp", "lastTimestamp", "creationTimestamp"]
	ignored_event = {"kubelet":["Pulled", "Created"], "horizontal-pod-autoscaler":[], "deployment-controller" : [], "default-scheduler" : []}

	def __init__(self, path):
		dir_list = os.listdir(path)
		for fn in dir_list:
			if "start_end_time" in fn:
				with open(path+"/"+fn) as f:
					self.stime = f.read()
					#print(self.stime)
				for l in self.stime.split("\n"):
					if l.startswith("start_time"):
						self.st = l.split(",")[2] + "Z"
					if l.startswith("end_time"):
						self.et = l.split(",")[2] + "Z"

			if "events" in fn:
				with open(path+"/"+fn) as f:
					self.sevents = json.load(f)
				#print(self.sevents)


			if "toppod" in fn:
				with open(path+"/"+fn) as f:
					self.spod_cpu = f.read()

			if "command" in fn:
				with open(path+"/"+fn) as f:
					self.scommand = f.read()

	def check_model_fidelity(self, veri_logs):
		log_events = self.log_parser()
		self.print_events(log_events)

		veri_events = self.convert_verification_logs(veri_logs)
		self.print_veri_events(veri_events)

		return self.compare_events(log_events, veri_events)

	def compare_events(self, log_events, veri_events):
		log_name = self.get_names_mapping(log_events)
		veri_name = self.get_names_mapping(veri_events)

		print("Starting the comparision...")
		print(log_name, veri_name)

		type_list = list(log_name.keys())
		type_perm = {}
		for t in type_list:
			log_name[t] = list(log_name[t])
			veri_name[t] = list(veri_name[t])
			if len(log_name[t]) < len(veri_name[t]):
				log_name[t].extend([-1 for i in range(0, len(veri_name[t]) - len(log_name[t]))])

			perm = list(permutations([*range(0,len(log_name[t]))], len(veri_name[t])))
			type_perm[t] = perm

		max_rate = 0
		index = 0
		progress = 0
		total = len(type_perm["dep"]) * len(type_perm["node"]) * len(type_perm["pod"])
		for dep_perm in type_perm["dep"]:
			for node_perm in type_perm["node"]:
				for pod_perm in type_perm["pod"]:
					cur_perm = {"dep" : dep_perm, "node" : node_perm, "pod" : pod_perm}
					cur_veri_events = deepcopy(veri_events)
					for e in cur_veri_events:
						event = e[1]
						for i in range(0, len(event.objs)):
							cur_objs_type = event.objs_type[i]
							for value_index in range(0, len(veri_name[cur_objs_type])):
								if veri_name[cur_objs_type][value_index] == event.objs[i]:
									#print(event.objs[i], value_index, log_name[cur_objs_type][cur_perm[cur_objs_type][value_index]])
									cur_value = log_name[cur_objs_type][cur_perm[cur_objs_type][value_index]]
									if cur_value != -1:
										event.objs[i] = log_name[cur_objs_type][cur_perm[cur_objs_type][value_index]]

					cur_rate = self.compare_matching_rate(log_events, cur_veri_events)
					max_rate = max_rate if cur_rate < max_rate else cur_rate
					if  index == (total/10) or index == (total/5):
						print(index, total, cur_rate, max_rate)
					index += 1

		print(max_rate)

		#print(self.compare_matching_rate(log_events, veri_events, {}))

	def compare_matching_rate(self, log_events, veri_events):
		count = 0
		# for i in range(0, min(len(log_events), len(veri_events))):
		# 	if log_events[i][1] == veri_events[i][1]:
		# 		count += 1

		j = 0
		last_index = 0
		i = 0
		unmatched_i = 0
		unmatched_j = 0
		matched = [0 for i in range(0, len(log_events))]
		#print(matched)

		# self.print_veri_events(veri_events)
		# self.print_events(log_events)
		
		while(i < len(veri_events)):
			j = last_index
			log_event = log_events[j][1]
			veri_event = veri_events[i][1]
			logger.debug("*************")
			logger.debug(veri_event)

			while (log_event != veri_event or matched[j] == 1):
				j += 1
				if j == len(log_events):
					break
				log_event = log_events[j][1]

			logger.debug(str(last_index) + " " + str(j) + " " + str(i) + " " + str(unmatched_i) + " " + str(unmatched_j))
			if j == len(log_events):
				unmatched_i += 1
				i += 1
				continue

			logger.debug(str(last_index) + " " + str(j) + " " + str(i) + " " + str(unmatched_i) + " " + str(unmatched_j))

			matched[j] = 1
			k = last_index
			for k in range(last_index, j+1):
				# give 1 sec delays...
				if log_events[k][0][0] < log_events[j][0][0]:
					if matched[k] == 0:
						unmatched_j += 1
				else:
					break
			last_index = k

			if last_index == len(log_events):
				unmatched_i += (len(veri_events) - i)
				break

			i += 1

			logger.debug(str(last_index) + " " + str(j) + " " + str(i) + " " + str(unmatched_i) + " " + str(unmatched_j))

		all_events = last_index + len(veri_events)
		logger.debug("&&&&&&&&&&")
		logger.debug(all_events)

		return (all_events - unmatched_i - unmatched_j)*1.0/all_events
			

	def get_names_mapping(self, events):
		names = {"dep": set(), "node": set(), "pod": set()}
		for e in events:
			event = e[1]
			if type(event) == Scheduler or type(event) == Kubelet:
				names["pod"].add(event.objs[0])
				names["node"].add(event.objs[1])
			

			elif type(event) == CPU_Change:
				names["pod"].add(event.objs[0])
	
			else:
				flag = True
				for d in names["dep"]:
					if event.compare_dep_name(event.objs[0], d):
						flag = False
						break
				if flag:
					names["dep"].add(event.objs[0])

		return names

	def convert_verification_logs(self, veri_logs):
		veri_events = []
		count = 0
		for log in veri_logs.split("\n"):
			items = log.split(";")
			log_main_info = items[0]
			pre_count = len(veri_events)

			if "HPA" in log_main_info:
				if "rescale" in log_main_info:
					cur = items[2].strip()
					exp = items[3].strip()
					direction = "increase" if int(cur) - int(exp) < 0 else "decrease"
					veri_events.append((count, HPA("rescale", [items[1].strip()],\
					 			items[-1].strip(), direction, exp)))
			elif "Deployment" in log_main_info:
				if "scale" in log_main_info:
					veri_events.append((count, Deployment("scale", [items[1].strip()], items[-1].strip(), items[2].strip(), items[3].strip())))
				elif "create" in log_main_info:
					veri_events.append((count, Deployment("create", [items[1].strip()], items[-1].strip())))

			elif "Scheduler" in log_main_info:
				if "scheduled" in log_main_info:
					veri_events.append((count, Scheduler("scheduled", [items[1].strip(), items[2].strip()], items[-1].strip())))
			
			elif "Kubelet" in log_main_info:
				if "start" in log_main_info:
					veri_events.append((count, Kubelet("start", [items[1].strip(), items[2].strip()], items[-1].strip())))
				elif "delete" in log_main_info:
					veri_events.append((count, Deployment("delete", [items[1].strip()], items[-1].strip())))

			elif "applyDeployment" in log_main_info:
				veri_events.append((count, Apply_Dep("apply_dep", [items[1].strip()], items[-1].strip())))

			elif "CPU Change" in log_main_info:
				direction = "increase" if int(items[2]) > 0 else "decrease"
				veri_events.append((count, CPU_Change("cpu_change", [items[1].strip()], items[-1].strip(), direction)))

			elif "maintenanceNode" in log_main_info:
				veri_events((count, Maintenance()))
			

			if pre_count + 1 == len(veri_events):
				count += 1
			else:
				if pre_count + 1 < len(veri_events):
					logger.critical("More than one events are added: " + log)
				else:
					logger.critical("Unknown verificaiont logs, ignored:" + log)

		return veri_events

	def log_parser(self):
		# The data format is ISO 8601-formatted date
		events = []
		events = self.parse_event_log(events)
		events = self.parse_pod_cpu(events)
		events = self.parse_command(events)

		events.sort(key=self.event_sort)

		return events

	def event_sort(self, event):
		if len(event[0]) > 1:
			return event[0][-1]

		return event[0][0]

	def process_unrelated_event(self, component, event, event_str):
		if component not in self.ignored_event:
			logger.critical("Unknown type of component " + component + ", ignored: " +event_str)
		else:
			if "all" in self.ignored_event[component]:
				logger.info("Ingnoring all events in component " + component + ": "+ event_str)
			else:
				if event["reason"] not in self.ignored_event[component]:
					logger.critical("Unknown type events of " + component +", ignored: " + event_str)
				else:
					logger.info("Ingnoring unrelated events in " + component + ": " + event_str)
		return None

	def convert_event_class(self, event):
		#print(json.dumps(item, indent = 1))
		component = ""
		host = ""
		if len(event["reportingComponent"]) > 0:
			component = (event["reportingComponent"])
		if len(event["source"]) > 0:
			component = (event["source"]["component"])
			if "host" in event["source"]:
				host = event["source"]["host"]

		event_str = "[" + component + "] " + event["reason"] + "; " + event["message"] + "; object: "+event["involvedObject"]["name"]
		#print(event_str)
		# HPA rescale; Deployment scale, create; Scheuder scheduled; kubelet start
		if component == "horizontal-pod-autoscaler":
			if event["reason"] == "SuccessfulRescale":
				value = event["message"].split("New size:")[1].split(";")[0].strip()
				if "above" in event["message"]:
					direction = "increase" 
				elif "below" in event["message"]:
					direction = "decrease"
				else:
					logger.critical("Unknown message type in HPA, ignored: " + event_str)
					return None
				return HPA("rescale", [event["involvedObject"]["name"]], event_str, direction, value)
			else:
				return self.process_unrelated_event(component, event, event_str)

		elif component == "deployment-controller":
			if event["reason"] == "ScalingReplicaSet":
				value = event["message"].split(" to ")[-1].strip()
				if "Scaled up" in event["message"]:
					direction = "increase"
				elif "Scaled down" in event["message"]:
					direction = "decrease"
				else:
					logger.critical("Unknown message type in deployment controller, ignored: " + event_str)
					return None
				return Deployment("scale", [event["involvedObject"]["name"]], event_str, direction, value)
			else:
				return self.process_unrelated_event(component, event, event_str)

		elif component == "replicaset-controller":
			if event["reason"] == "SuccessfulCreate":
				return Deployment("create", [event["involvedObject"]["name"]], event_str)
			elif event["reason"] == "SuccessfulDelete":
				return Deployment("delete", [event["involvedObject"]["name"]], event_str)
			else:
				return self.process_unrelated_event(component, event, event_str)

		elif component == "default-scheduler":
			if event["reason"] == "Scheduled":
				node_name = event["message"].split(" to ")[-1].strip()
				return Scheduler("scheduled", [event["involvedObject"]["name"], node_name], event_str) 
			else:
				return self.process_unrelated_event(component, event, event_str)

		elif component == "kubelet":
			if event["reason"] == "Started":
				return Kubelet("start", [event["involvedObject"]["name"], event["source"]["host"]], event_str)

		else:
			return self.process_unrelated_event(component, event, event_str)


	def parse_event_log(self, events):
		for item in self.sevents["items"]:
			all_time = set()
			if "firstTimestamp" in item and item["firstTimestamp"] is not None:
				all_time.add(item["firstTimestamp"])
			if "lastTimestamp" in item and item["lastTimestamp"] is not None:
				all_time.add(item["lastTimestamp"])
			if "creationTimestamp" in item["metadata"] and item["metadata"]["creationTimestamp"] is not None:
				all_time.add(item["metadata"]["creationTimestamp"])
			if "eventTime" in item and item["eventTime"] is not None:
				all_time.add(item["eventTime"])
			#print(all_time)

			related = False
			for t in all_time:
				if self.in_timerange(t):
					related = True
					break

			if related:
				#print(all_time)
				all_time_timestamp = self.cut_redundant(all_time)
				event_class = self.convert_event_class(item)
				if event_class is not None:
					for t in all_time_timestamp:
						events.append(([t], event_class))

				#print(event_str)

		return events

	def parse_pod_cpu(self, events):
		all_cpu_logs = self.spod_cpu.split("idx")
		last_time = {}
		for cpu_log in all_cpu_logs[1:]:
			l_cpu_log  = cpu_log.split("\n")
			event_time = l_cpu_log[0].split(",")[3] + "Z"
			if self.in_timerange(event_time) and len(l_cpu_log) > 1:
				for i in range(2, len(l_cpu_log)-1):
					items = l_cpu_log[i].split(",")
					cur_name = items[0]
					cur_cpu = int(items[1][:-1])
					if cur_name not in last_time:
						last_time[cur_name] = cur_cpu
					else:
						change = self.test_cpu(last_time[cur_name], cur_cpu)
						if change is not None:
							events.append(([self.str_to_timestamp(event_time)], CPU_Change("cpu_change", [cur_name], "pod " + cur_name + " cpu " + change, change)))
							#print("pod " + cur_name + " cpu " + change)
						last_time[cur_name] = cur_cpu
		return events

	def parse_command(self, events):
		for l in self.scommand.split("\n")[1:-1]:
			items = l.split(",")
			t = items[3]+"Z"
			if self.in_timerange(t):
				if "apply" in items[1]:
					events.append(([self.str_to_timestamp(t)], Apply_Dep("apply_dep", [items[1].split(" ")[2].strip()], items[1] + "; " + items[0])))
				elif "drain" in item[0]:
					node = item[0].split(" ")[2].strip()
					events.append(([self.str_to_timestamp(t)], Maintenance("start", [node], items[0])))
				elif "uncordon" item[0]:
					node = item[0].split(" ")[2].strip()
					events.append(([self.str_to_timestamp(t)], Maintenance("end", [node], items[0])))
				else:
					logger.critical("Unknown type of command ignored: " + items[1] + "; " + items[0])

		return events

	def test_cpu(self, last_cpu, cur_cpu):
		if last_cpu == 0:
			return None
		if abs((last_cpu - cur_cpu)*100/last_cpu) >= self.cpu_threshold:
			if last_cpu > cur_cpu:
				return "decrease"
			else:
				return "increase"
		return None

	def timestamp_to_str(self, t):
		return datetime.utcfromtimestamp(t).strftime("%Y-%m-%d %H:%M:%S")

	def str_to_timestamp(self, t):
		try:
			datetime_t =  datetime.strptime(t, "%Y-%m-%dT%H:%M:%S%z")
		except ValueError:
			datetime_t =  datetime.strptime(t, "%Y-%m-%dT%H:%M:%S.%f%z")

		return int(datetime.timestamp(datetime_t))

	def cut_redundant(self, all_time):
		all_time_timestamp = set()
		for t in all_time:
			all_time_timestamp.add(self.str_to_timestamp(t))

		all_time_timestamp = list(all_time_timestamp)
		all_time_timestamp.sort()
		return all_time_timestamp

	def in_timerange(self, ft): 
		if ft is None:
			return False
		try:
			datetime_ft =  datetime.strptime(ft, "%Y-%m-%dT%H:%M:%S%z")
		except ValueError:
			datetime_ft =  datetime.strptime(ft, "%Y-%m-%dT%H:%M:%S.%f%z")

		if datetime_ft <= datetime.strptime(self.et, "%Y-%m-%dT%H:%M:%S%z") and datetime_ft >= datetime.strptime(self.st, "%Y-%m-%dT%H:%M:%S%z"):
			return True
		return False

	def print_events(self, events):
		print("~~~~~~Printing all related events, Total"+ str(len(events)) + "~~~~~~~~~")
		for e in events:
			event_str = "["+self.timestamp_to_str(e[0][-1])+"]" + str(e[-1])
			print(event_str)

	def print_veri_events(self, events):
		print("~~~~~~Printing all related events, Total"+ str(len(events)) + "~~~~~~~~~")
		for e in events:
			event_str = "["+str(e[0])+"]" + str(e[1])
			print(event_str)


if __name__ == '__main__':
	with open(sys_path+"/results/"+sys.argv[2]+"_3") as f:
		veri_logs = f.read()

	mf = Model_Fidelity(sys.argv[1])
	mf.check_model_fidelity(veri_logs)


