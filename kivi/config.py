# This module includes all the default interal configurations for verification. 

import logging

confident_node_size = 6
confident_pod_size_factor = 6

# For small scale finder algorithm
resource_difference_tolerance = 8

model_logging = logging.ERROR
verifier_logging = logging.ERROR

default_timeout = 300
# how many random seed we should try
random_limit = 5

# how many loops will be counted as oscillation in verification
loop_times = 3

#how cases are scaled up
case_free = True

#verification internal parameters
## initial queue size
queue_size = 10