# Kivi: verifying your Kubernetes clusters

## Installation and Requirement

[Spin](https://github.com/nimble-code/Spin) (>=6.5.2)

Python (>=3.8)

### Script
We provide a script for easy installation. 
```
./install.sh
```
This is a simple script that has only been tested on Unix-like operating system. Pull requests are welcome.

### Manual
If the script does not work, you could do it manually as follows.
1. Create `libs`, `results` and `temp` directories under the root dir. 
2. Install [Spin](https://github.com/nimble-code/Spin) into `libs`. 
3. Install required libs by ```pip3 install -r requirements.txt```

Then you are good!


## Usage
```
cd bin

python3 kivi_runner.py [options]
```

### Option
```
usage: Kivi [-h] (-c CASE | -p PATH) [-s SCALE] [-cn] [-log] [-o] [-f FAST_FIND] [-a] [-v VERBOSE_LEVEL] [-r] [-to TIMEOUT] [-ig INTENTS_GROUP] [-pc PAN_COMPILE] [-pr PAN_RUNTIME] [-l]
            [-jf JSON_FILE_PATH] [-lf LOG_OUTPUT_FILE] [-fd FILE_DEBUG] [-si]

Kivi parameters.

optional arguments:
  -h, --help            show this help message and exit

Main parameters:
  -c CASE, --case CASE  Verify an existing case, entering a case name. We support c1-8.
  -p PATH, --path PATH  Verify from runtime configs, entering config path.
  -s SCALE, --scale SCALE
                        Choose a scale if use -c and -o. Default: 3 nodes.
  -cn, --case_non_violation
                        Decide if generate cases without violations if use -c. Default: False.

Verification parameters:
  -log, --input_logs    Get the input from run time logs
  -o, --original        Disable scaling algorithm and verify for the original configs (single topology without scaling algorithm).
  -f FAST_FIND, --fast_find FAST_FIND
                        When using scaling algorithm, increasing the scale faster instead of trying all the scales. Speed can be chosen from 0 to 3. With default 0 the original speed.
  -a, --all_violation   Find all violations (default: stop after finding one).
  -v VERBOSE_LEVEL, --verbose_level VERBOSE_LEVEL
                        Log level for generated examples. Smaller value means less hints in the examples.
  -r, --random          Enable the verifier to automatically try random seed for verification. If -to is not defined, the default timeout for each random number is 300sec.
  -to TIMEOUT, --timeout TIMEOUT
                        Timeout for each pan execuation.
  -ig INTENTS_GROUP, --intents_group INTENTS_GROUP
                        Defines how many intents to be verified at a time. Default is 0, meaning all intents are verified together.

Spin options:
  Options sent to pan or spin. All options need to be quoted and separated by comma without dash, e.g., 'm10000, n'

  -pc PAN_COMPILE, --pan_compile PAN_COMPILE
                        Options for pan compiler.
  -pr PAN_RUNTIME, --pan_runtime PAN_RUNTIME
                        Options for pan runtime.
  -l, --loop            Check if exists loop/oscillation using SPIN default implementation.

Other runtime parameters:
  -jf JSON_FILE_PATH, --json_file_path JSON_FILE_PATH
                        the file path to dump the intermediate JSON file of cluster setup.
  -lf LOG_OUTPUT_FILE, --log_output_file LOG_OUTPUT_FILE
                        stream the output to file. Need to specify a filename. Default: output to terminal
  -fd FILE_DEBUG, --file_debug FILE_DEBUG
                        store the intermediate files for debug purposes. Default is 0, meaning no file is written.

Simulation parameters:
  -si, --simulation     Simulation mode.
```

## Example
### Verifying pre-defined failure cases
We have prepared a few [failure cases](documents/failure_cases.md) for users to understand our system. 

To test on case [C3](documents/failure_cases.md#C3), you could run it with `-c` to select such case to verify. Other available pre-defined cases are `c[1-8]`. These cases have been introduced in Section 3 of [our paper](https://arxiv.org/abs/2311.02800). 
```
python3 kivi_runner.py -o -c c3
```
You can see the following minimal example demonstrating the traces that lead to the error `no feasible node!`:
```
Working on the intents: pod_always_schedulable 
========================
1 failure(s) are found!
-----Failure #1-----
Counterexample:
[0][CPU Change] CPU change 2 on pod 4, now 10, and node 3, now 46
[1][HPA] Need to rescale, pod number change from 5 to 6
[2][Deployment] Too few replicas, need to create 1
[3][Deployment] Adding a new pod 6 to deployment 1
[4][Scheduler - no_feasible_node] No feasible node!



Summary:
    1 failure(s) found!
    Violating intent(s): pod_always_schedulable 
    Elapsed time: 1.04 seconds
```
This shows a five-step example that leads to the issue: 1) CPU changes in a unit of 2 on pod 4; 2) HPA decides to scale up the number of pods to 6; 3/4) deployment controller compares the specReplica and running replica, and creates 1 replica; 5) Scheduler does not found any feasible node for this new pod. 

### Verifying according to real user input
We implemented a (preliminary) parser to parse the real configurations, logs and yamls. In particular, user can provide Kivi etheir 1) their configurations so we could verify before deployment, or 2) running cluster logs that we can verify as it is. We have prepared the example input for case [C3](documents/failure_cases.md#C3) for both ways. 

#### Verifying configurations before deployment
User need to provide their yamls (in `yaml/`) for deployment, config for HPA if applicable, their intents in `user_input/intents.json` and the cluster configs in `user_input/cluster_config.json`. To test using our prepared input, run this command, using `-p` to enter the path of the configs:
```
python3 kivi_runner.py -p ../examples/c3/configs -o
```
You will see a similar output that demonstrates the same minimal example. The major difference is that the example will show how the problem happen from scratch, starting with 0 replicas.

Note: user can remove the `-o` to enable the incremental scaling algorithm, which will explore all the possible topologies. Please refer to Section 4 in [our paper](https://arxiv.org/abs/2311.02800) to learn more about the incremental scaling algorithm.

#### Verifyng runtime logs
We have collected the logs (e.g., `kubectl get deployments`) from Kubernetes clusters that reproduced the C3 failure cases, which are stored in `examples/c3/logs/setup` folder. Additionally, user need to provide their intent in `user_input/intents.json`.  To verify the logs, run it with `-p` to enter the path of logs, and use `-log` to tell Kivi the inputs are logs. 
```
python3 kivi_runner.py -p ../examples/c3/logs -log
```
You will see a similar output that demonstrates the same minimal example.  

### Simulation mode
KIVI also provide a simulation mode to help debug cluster or help you understand configuration change before deployment. Intead of verifying for all possible execution path, simulation mode will randomly pick one path and generate a sequence of events for that path. Such path may not be a violation at all. To use simulation mode, use `-si` option. 
```
python3 kivi_runner.py -p ../examples/c3/logs -log -si
```
You will see a similar output as before. Because this example does not have much non-deterministic and hence execuation path is the same as the counterexample. 

## Paper and Documentation
Please find more documents in `documents/`, including an [overview of the system architecture](documents/sys_arch.md). We are still working on adding more docs onto this repo.

If you want to understand more details, please refer to our paper [Kivi: Verification for Cluster Management](https://arxiv.org/abs/2311.02800) and our [KubeCon presentation](https://static.sched.com/hosted_files/kccncna2023/9b/Kivi-KubeCon.pdf). 

## Contributors
This repo is part of the research project **Kivi: Verification for Cluster Management**, authored by [Bingzhe Liu](https://bingzhe.web.engr.illinois.edu/), [Gangmuk Lim](https://gangmuk.github.io/), [Ryan Beckett](https://www.microsoft.com/en-us/research/people/rybecket/) and [P. Brighten Godfrey](https://pbg.cs.illinois.edu/).

## Contact
Bingzhe Liu (bzheliu at gmail.com)

