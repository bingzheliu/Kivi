import sys


# log_level 1: warning and critical reason that the failure happen
# log_level 2: steps that result in the error
# log_level 3: detailed output of all steps
# log_level 4: the values of important variables
def parse_spin_error_trail(file_base, filename, file_error_trail, log_level):
	with open(file_base + "/results/" + filename, "w") as fw:
		with open(file_base + "/results/raw_data/" + file_error_trail) as fr:
			s = fr.readline()

			while len(s) > 0:
				if s.startswith("[*"):
					count = 0
					while s[count] != "]":
						count += 1

					if count - 1 <= int(log_level):
						fw.write(s)
				s = fr.readline()

def analyze_end_state(file_error_trail):
	return "invalid end state"

def analyze_assert(file_error_trail):
	return "assertion violated"

def parse_pan_output(file_base, file_exec_log, file_error_trail):
	with open(file_base + "/results/raw_data/" + file_exec_log) as fr:
		s = fr.readline()

		total_mem = 0
		elapsed_time = 0
		failure_type = 0

		# TODO:check on how to test if the file is ended
		while len(s) > 0:
			if "invalid end state" in s:
				failure_type = analyze_end_state(file_error_trail)
				 
			if "assertion violated" in s:
				failure_type = analyze_assert(file_error_trail)
				 

			if "total actual memory usage" in s:
				total_mem = s.split("total")[0].strip()

			if "elapsed time" in s:
				elapsed_time = s.split("time")[1].split("seconds")[0].strip()

			s = fr.readline()

		print(failure_type, total_mem, elapsed_time)

if __name__ == '__main__':
	file_base = sys.argv[1]
	filename = sys.argv[2]
	file_error_trail = sys.argv[3]
	file_exec_log = sys.argv[4]
	log_level = sys.argv[5]

	parse_pan_output(file_base, file_exec_log, file_error_trail)

	#parse_spin_error_trail(file_base, filename, file_error_trail, log_level)







