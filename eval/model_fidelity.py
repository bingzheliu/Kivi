import os
import json
from datetime import datetime
import sys

class model_fidelity:
	def __init__(self, path):
		dir_list = os.listdir(path)
		for fn in dir_list:
			if "start_end_time" in fn:
				with open(path+"/"+fn) as f:
					self.stime = f.read()
					#print(self.stime)

			if "events" in fn:
				with open(path+"/"+fn) as f:
					self.sevents = json.load(f)
				#print(self.sevents)

		self.related_t = ["firstTimestamp", "lastTimestamp", "creationTimestamp"]

	def cut_redundant(self, all_time):
		all_time_timestamp = set()
		for t in all_time:
			try:
				datetime_t =  datetime.strptime(t, "%Y-%m-%dT%H:%M:%S%z")
			except ValueError:
				datetime_t =  datetime.strptime(t, "%Y-%m-%dT%H:%M:%S.%f%z")

			all_time_timestamp.add(int(datetime.timestamp(datetime_t)))

		all_time_timestamp = list(all_time_timestamp)
		all_time_timestamp.sort()
		return all_time_timestamp

	def log_parser(self):
		# The data format is ISO 8601-formatted date
		for l in self.stime.split("\n"):
			if l.startswith("start_time"):
				st = l.split(",")[2] + "Z"
			if l.startswith("end_time"):
				et = l.split(",")[2] + "Z"

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
				if self.in_timerange(t, st, et):
					related = True
					break

			if related:
				#print(all_time)
				all_time_timestamp = self.cut_redundant(all_time)
				str_t = ""
				for t in all_time_timestamp:
					str_t += (datetime.utcfromtimestamp(t).strftime("%Y-%m-%d %H:%M:%S") + " ")
				#print(json.dumps(item, indent = 1))
				component = ""
				if len(item["reportingComponent"]) > 0:
					component += (item["reportingComponent"] + " ")
				if len(item["source"]) > 0:
					component += (item["source"]["component"])
					if "host" in item["source"]:
						component += (":" + item["source"]["host"])
	

				print("["+str_t+"] [" + component + "] " + item["reason"] + "; " + item["message"])

	def in_timerange(self, ft, st, et): 
		if ft is None:
			return False
		try:
			datetime_ft =  datetime.strptime(ft, "%Y-%m-%dT%H:%M:%S%z")
		except ValueError:
			datetime_ft =  datetime.strptime(ft, "%Y-%m-%dT%H:%M:%S.%f%z")

		if datetime_ft <= datetime.strptime(et, "%Y-%m-%dT%H:%M:%S%z") and datetime_ft >= datetime.strptime(st, "%Y-%m-%dT%H:%M:%S%z"):
			return True
		return False


if __name__ == '__main__':
	mf = model_fidelity(sys.argv[1])
	mf.log_parser()

