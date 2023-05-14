import sys
from datetime import datetime
import os
import logging

import yaml

# logger = logging.getLogger(__name__)
# # :%(lineno)s 
# FORMAT = "[%(asctime)s;%(filename)s;%(levelname)s;%(funcName)s() ] %(message)s"
# logging.basicConfig(format=FORMAT, level=logging.DEBUG)


formatter = logging.Formatter("[%(asctime)s;%(filename)s;%(levelname)s;%(funcName)s() ] %(message)s", "%Y-%m-%d %H:%M:%S")

def setup_logger(name, level=logging.INFO):
    """To setup as many loggers as you want"""

    handler = logging.StreamHandler()        
    handler.setFormatter(formatter)

    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.addHandler(handler)

    return logger

# first file logger
logger = setup_logger('verifier_logger', logging.DEBUG)

# second file logger
model_logger = setup_logger('model_logger', logging.INFO)

log_level = 1


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

#TODO: move these to other places
file_base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
with open(file_base+"/src/configs.yaml") as f:
	configs = yaml.safe_load(f)

print(configs)
