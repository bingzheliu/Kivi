# This module includes the shared functions and variables in kivi.

import logging
import argparse
import json
import os
from copy import deepcopy
import subprocess
import sys
from config import *
#__all__ = ["args", "sys_path", "logger", "model_logger"]

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
system_name = "Kivi"
# print("Initilizing " + system_name)

#formatter = logging.Formatter("[%(asctime)s;%(filename)s;%(levelname)s;%(funcName)s() ] %(message)s", "%Y-%m-%d %H:%M:%S")
formatter = logging.Formatter("%(message)s")

def setup_logger(name, level=logging.INFO, handler_type="stream", filename=None):
    """To setup as many loggers as you want"""

    if handler_type == "file" and filename is not None:
    	handler = logging.FileHandler(filename)
    else:
    	handler = logging.StreamHandler(sys.stdout)   

    handler.setFormatter(formatter)

    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.addHandler(handler)

    return logger

def setup_argparser(arg_parser):
    # can use subparser to parse for verification v.s. simulation. 
    main_arg = arg_parser.add_argument_group("Main parameters")
    mode = main_arg.add_mutually_exclusive_group(required=True)
    mode.add_argument('-c', '--case', type=str, help='Verify an existing case, entering a case name. We support c1-8.')
    # TODO: this may need to be convert into absolute path
    mode.add_argument('-p', '--path', type=str, help='Verify from runtime configs, entering config path.')

    main_arg.add_argument('-s', '--scale', type=int, default=3, help='Choose a scale if use -c and -o. Default: 3 nodes.')
    main_arg.add_argument('-cn', "--case_non_violation", action='store_true', help='Decide if generate cases without violations if use -c. Default: False.')

    verification_arg = arg_parser.add_argument_group("Verification parameters")
    verification_arg.add_argument('-o', '--original', action='store_true', help='Disable scaling algorithm and verify for the original configs (single topology without scaling algorithm).')
    verification_arg.add_argument('-f', '--fast_find', type=int, default=0, help='When using scaling algorithm, increasing the scale faster instead of trying all the scales. Speed can be chosen from 0 to 3. With default 0 the original speed.')
    # TODO: add option to send to pan and see if we want to find all the violations
    verification_arg.add_argument('-a', '--all_violation', action='store_true', help='Find all violations (default: stop after finding one).')
    verification_arg.add_argument('-v', '--verbose_level', type=int, default=1, help="Log level for generated examples. Smaller value means less hints in the examples." )
    verification_arg.add_argument('-r', '--random', action='store_true', help='Enable the verifier to automatically try random seed for verification. If -to is not defined, the default timeout for each random number is ' + str(default_timeout)+ 'sec.')
    verification_arg.add_argument('-to','--timeout', type=int, help='Timeout for each pan execuation.')
    #verification_arg.add_argument('-eh', '--extreamly_high_confidence', action='store_true', help='Enable extreamly high confidence mode for verification. Default: disable -- verification will stop at N(Node) = 10 with high confidence.')
    verification_arg.add_argument("-ig", '--intents_group', type=int, default=0, help="Defines how many intents to be verified at a time. Default is 0, meaning all intents are verified together.")

    spin_arg = arg_parser.add_argument_group("Spin options", description="Options sent to pan or spin. All options need to be quoted and separated by comma without dash, e.g., 'm10000, n'")
    spin_arg.add_argument('-pc', '--pan_compile', type=str, default="DVECTORSZ=100000, DT_RAND, DP_RAND", help="Options for pan compiler. ")
    spin_arg.add_argument('-pr', '--pan_runtime',  type=str, default='m100000', help="Options for pan runtime.")
    spin_arg.add_argument('-l', '--loop', action='store_true', help="Check if exists loop/oscillation using SPIN default implementation.")

    other_parser = arg_parser.add_argument_group("Other runtime parameters")
    other_parser.add_argument('-jf', '--json_file_path', type=str, help="the file path to dump the intermediate JSON file of cluster setup.")
    other_parser.add_argument('-lf', "--log_output_file", type=str, help="stream the output to file. Need to specify a filename. Default: output to terminal")
    other_parser.add_argument("-fd", "--file_debug", type=int, default=0, help="store the intermediate files for debug purposes. Default is 0, meaning no file is written. ")

    simulation_arg = arg_parser.add_argument_group("Simulation parameters")
    simulation_arg.add_argument("-si", "--simulation", action='store_true', help="Simulation mode.")


arg_parser = argparse.ArgumentParser(prog=system_name,description='Kivi parameters.')
setup_argparser(arg_parser)
args = arg_parser.parse_args()



if args.log_output_file is not None:
	# first file logger
	logger = setup_logger('verifier_logger', verifier_logging, handler_type="file", filename=args.log_output_file)

	# second file logger
	model_logger = setup_logger('model_logger', model_logging, handler_type="file", filename=args.log_output_file)

else:
	# first file logger
	logger = setup_logger('verifier_logger', verifier_logging)

	# second file logger
	model_logger = setup_logger('model_logger', model_logging)


# logger = logging.getLogger(__name__)
# # :%(lineno)s 
# FORMAT = "[%(asctime)s;%(filename)s;%(levelname)s;%(funcName)s() ] %(message)s"
# logging.basicConfig(format=FORMAT, level=logging.DEBUG)


# TODO: each run of an execuation should actually be one class, so they won't affect each other.
def my_mkdir(_dir):
    if not os.path.exists(_dir):
        logger.info("mkdir " + _dir)
        os.mkdir(_dir)
    else:
        logger.debug(_dir + " exists")


def myprint(output, log_func=logger.info):
    if len(output) > 0:
        log_func(output)

# temp/case_id stores the pml and json file. For cases with different scale, a seperate dir will be generate for each scale
# temp/case_id/min_exp stores the json file for each scale that are tested. 
# result/case_id stores the runtime result. 
def generate_dir(file_base, case_id, scale):
    my_mkdir(file_base+"/temp/"+ str(case_id))
    if scale == 0:
        pml_base_path = file_base + "/temp/" + str(case_id) 
    else:
        pml_base_path = file_base + "/temp/" + str(case_id) + "/" + str(scale)
    my_mkdir(pml_base_path)
    my_mkdir(pml_base_path+"/min_exp")

    result_base_path = file_base + "/results/" + str(case_id)
    my_mkdir(file_base + "/results")
    my_mkdir(result_base_path)
    my_mkdir(result_base_path + "/raw_data")
    
    return pml_base_path, result_base_path

# TODO: deal with the situation where max search is too small
def run_script(commands, print_stdout, _timeout=None):
	s_output = ""
	for s in commands:
		s_output += (s + " ")
	logger.info("running " + s_output)

	spin_script = subprocess.Popen(commands,
	                     stdout=subprocess.PIPE, 
	                     stderr=subprocess.PIPE)

	if _timeout is not None:
		try:
		    stdout, stderr = spin_script.communicate(timeout=_timeout)
		except subprocess.TimeoutExpired:
			logger.info("Timeout after "+str(_timeout)+" sec")
			spin_script.kill()
			stdout, stderr = spin_script.communicate()
			myprint(stderr.decode(), logger.error)
			return False, stdout, stderr
	else:
		stdout, stderr = spin_script.communicate()
		myprint(stderr.decode(), logger.error)
	
	return True, stdout, stderr

# temp/case_id stores the pml and json file. For cases with different scale, a seperate dir will be generate for each scale
# temp/case_id/min_exp stores the json file for each scale that are tested. 
# result/case_id stores the runtime result. 
def generate_dir(file_base, case_id, scale):
    my_mkdir(file_base+"/temp/"+ str(case_id))
    if scale == 0:
        pml_base_path = file_base + "/temp/" + str(case_id) 
    else:
        pml_base_path = file_base + "/temp/" + str(case_id) + "/" + str(scale)
    my_mkdir(pml_base_path)
    my_mkdir(pml_base_path+"/min_exp")

    result_base_path = file_base + "/results/" + str(case_id)
    my_mkdir(file_base + "/results")
    my_mkdir(result_base_path)
    my_mkdir(result_base_path + "/raw_data")
    
    return pml_base_path, result_base_path

def json_readable_str(json_config):
    return json.dumps(json_config, indent=2)

