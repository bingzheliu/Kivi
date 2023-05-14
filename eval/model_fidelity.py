import os
import json
from datetime import datetime
import sys
from math import *

class model_fidelity:
	cpu_threshold = 10
	related_t = ["firstTimestamp", "lastTimestamp", "creationTimestamp"]

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

	def log_parser(self):
		# The data format is ISO 8601-formatted date
		events = []
		events = self.parse_event_log(events)
		events = self.parse_pod_cpu(events)
		events = self.parse_command(events)

		self.print_events(events)
		sorted(events, key=self.event_sort)

	def event_sort(self, event):
		if len(event[0]) > 1:
			return event[0][-1]

		return event[0][0]

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
				
				#print(json.dumps(item, indent = 1))
				component = ""
				if len(item["reportingComponent"]) > 0:
					component += (item["reportingComponent"] + " ")
				if len(item["source"]) > 0:
					component += (item["source"]["component"])
					if "host" in item["source"]:
						component += (":" + item["source"]["host"])
	
				event_str = "[" + component + "] " + item["reason"] + "; " + item["message"] + "; object: "+item["metadata"]["name"]
				events.append((all_time_timestamp, event_str))

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
							events.append(([self.str_to_timestamp(event_time)], "pod " + cur_name + " cpu " + change))
							#print("pod " + cur_name + " cpu " + change)
						last_time[cur_name] = cur_cpu
		return events

	def parse_command(self, events):
		for l in self.scommand.split("\n")[1:-1]:
			items = l.split(",")
			t = items[3]+"Z"
			if self.in_timerange(t):
				events.append(([self.str_to_timestamp(t)], items[1] + "; " + items[0]))

		return events

	def test_cpu(self, last_cpu, cur_cpu):
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
		for e in events:
			event_str = "["+self.timestamp_to_str(e[0][-1])+"]" + e[1]
			print(event_str)


if __name__ == '__main__':
	mf = model_fidelity(sys.argv[1])
	mf.log_parser()

