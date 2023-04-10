import sys


# log_level 1: warning and critical reason that the failure happen
# log_level 2: steps that result in the error
# log_level 3: detailed output of all steps
# log_level 4: the values of important variables
# log_level 6: details in plugins process
def parse_spin_error_trail(output, failure_type, log_level):
	result_log = ""
	failure_details = ""
	output_lines = output.splitlines()

	for i in range(0, len(output_lines)):
		s = output_lines[i]
		if s.startswith("[*"):
			count = 0
			while s[count] != "]":
				count += 1

			if count - 1 <= int(log_level):
				result_log += (s + "\n")

		if "START OF CYCLE" in s:
			result_log += (s + "\n")

		if s.startswith("pan:1:") or s.startswith("spin: trail ends"):
			failure_details = output_lines[i-1] + "\n"
			while not s.startswith("global vars"):
				failure_details += (s+"\n")
				i += 1
				s = output_lines[i]
			result_log += failure_details

	return 	result_log, failure_details
				

def analyze_end_state(file_error_trail):
	return file_error_trail

def analyze_assert(file_error_trail):
	return file_error_trail

def parse_pan_output(output):
	total_mem = 0
	elapsed_time = 0
	failure_type = "None"
	error_trail_name = None
	failure_details = ""
	for s in output.splitlines():
		# TODO:check on how to test if the file is ended
		if "pan:1: invalid end state" in s:
			failure_type = analyze_end_state(s)
			 
		if "pan:1: assertion violated" in s:
			failure_type = analyze_assert(s)
		
		if "pan:1: end state in claim reached" in s:
			failure_type = "Never Claim Violated"

		if "pan: wrote" in s:
			error_trail_name = s.split("pan: wrote")[1].strip()	 

		if "pan:1: non-progress cycle" in s:
			failure_type = "non-progress cycle"

		if "error:" in s:
			failure_type = analyze_assert(s)

		if "total actual memory usage" in s:
			total_mem = s.split("total")[0].strip()

		if "elapsed time" in s:
			elapsed_time = s.split("time")[1].split("seconds")[0].strip()


	return failure_type, failure_details, error_trail_name, total_mem, elapsed_time

if __name__ == '__main__':
	# file_base = sys.argv[1]
	filename = sys.argv[1]
	# file_error_trail = sys.argv[3]
	# file_exec_log = sys.argv[4]
	# log_level = sys.argv[5]

	# parse_pan_output(file_base, file_exec_log, file_error_trail)
	with open(filename) as f:
		failure_type = ""
		result_log, failure_details = parse_spin_error_trail(f.read(), failure_type, 3)
		print(result_log, failure_details)







