import logging

confident_node_size = 6
confident_pod_size_factor = 3

# For small scale finder algorithm
resource_difference_tolerance = 8

model_logging = logging.CRITICAL
verifier_logging = logging.INFO

default_timeout = 300

# how many loops will be counted as oscillation in verification
loop_times = 3

#how cases are scaled up
case_free = True