import logging
import argparse
import os
from copy import deepcopy
#__all__ = ["args", "sys_path", "logger", "model_logger"]

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
system_name = "Kivi"
# print("Initilizing " + system_name)

formatter = logging.Formatter("[%(asctime)s;%(filename)s;%(levelname)s;%(funcName)s() ] %(message)s", "%Y-%m-%d %H:%M:%S")

def setup_logger(name, level=logging.INFO):
    """To setup as many loggers as you want"""

    handler = logging.StreamHandler()        
    handler.setFormatter(formatter)

    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.addHandler(handler)

    return logger

def setup_argparser(arg_parser):
    # can use subparser to parse for verification v.s. simulation. 
    mode = arg_parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('-c', '--case', type=str, help='Verify an exiting cases, entering a case name')
    mode.add_argument('-p', '--path', type=str, help='Verify from runtime configs, entering config path')

    verification_arg = arg_parser.add_argument_group("Verification parameters")
    verification_arg.add_argument('-o', '--original', action='store_true', help='Disable finding minimal examples and verify for the original configs')
    verification_arg.add_argument('-f', '--fast_find', action='store_true', help='When finding minimal examples, find the minimal scale faster instead of trying all the scales')
    # TODO: add option to send to pan and see if we want to find all the violations
    verification_arg.add_argument('-a', '--all_violation', action='store_true', help='Find all violations (default: stop after finding one)')
    verification_arg.add_argument('-v', '--verbose_level', type=int, default=1, help="Log level for generated examples. Smaller value means less hints in the examples." )

    spin_arg = arg_parser.add_argument_group("Spin options", description="Options sent to pan or spin. All options need to be quoted and seperated by comma without dash, e.g., 'm10000, n'")
    spin_arg.add_argument('-pc', '--pan_compile', type=str, default="DVECTORSZ=450000, DT_RAND, DP_RAND", help="Options for pan compiler. ")
    spin_arg.add_argument('-pr', '--pan_runtime',  type=str, default='m1000000', help="Options for pan runtime")

    arg_parser.add_argument('-s', '--scale', type=int, default=3, help='Choose a scale if use -c and -o. Default: 3 nodes.')
    arg_parser.add_argument('-cn', "--case_non_violation", action='store_true', help='Deside if generate cases without violations if use -c. Default: False.')


# first file logger
logger = setup_logger('verifier_logger', logging.DEBUG)

# second file logger
model_logger = setup_logger('model_logger', logging.INFO)

arg_parser = argparse.ArgumentParser(prog=system_name,description='Verifier parameters.')
setup_argparser(arg_parser)
args = arg_parser.parse_args()
logger.debug(args)


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
