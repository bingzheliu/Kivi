# Kivi: verifying your Kubernetes clusters

## Install and Requirement

[Spin](https://github.com/nimble-code/Spin) (>=6.5.2)

Python (>=3.8)

### Manual
1. Create `libs`, `results` and `temp` directories under the root dir. 
2. Install [Spin](https://github.com/nimble-code/Spin) into `libs`. 
3. Install required libs by ```pip3 install -r requirements.txt```

Then you are good!

### Script
```
./install.sh
```
This is a simple script that has only been tested in Mac. Pull requests are welcome.


## Usage
```
cd bin

python3 kivi_runner.py [options]
```

### Option
```
usage: Kivi [-h] (-c CASE | -p PATH) [-o] [-f FAST_FIND] [-a] [-v VERBOSE_LEVEL] [-r] [-to TIMEOUT] [-ig INTENTS_GROUP] [-pc PAN_COMPILE] [-pr PAN_RUNTIME] [-l]
            [-s SCALE] [-cn] [-jf JSON_FILE_PATH] [-lf LOG_OUTPUT_FILE] [-fd FILE_DEBUG] [-si]

Kivi parameters.

optional arguments:
  -h, --help            show this help message and exit
  -c CASE, --case CASE  Verify an existing case, entering a case name.
  -p PATH, --path PATH  Verify from runtime configs, entering config path.
  -s SCALE, --scale SCALE
                        Choose a scale if use -c and -o. Default: 3 nodes.
  -cn, --case_non_violation
                        Decide if generate cases without violations if use -c. Default: False.

Verification parameters:
  -o, --original        Disable scaling algorithm and verify for the original configs (single topology without scaling algorithm).
  -f FAST_FIND, --fast_find FAST_FIND
                        When using scaling algorithm, increasing the scale faster instead of trying all the scales. Speed can be chosen from 0 to 3. With default 0 the
                        original speed.
  -a, --all_violation   Find all violations (default: stop after finding one).
  -v VERBOSE_LEVEL, --verbose_level VERBOSE_LEVEL
                        Log level for generated examples. Smaller value means less hints in the examples.
  -r, --random          Enable the verifier to automatically try random seed for verification. If -to is not defined, the default timeout for each random number is
                        300sec.
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

To test on case [S3](documents/failure_cases.md#S3), you could run it with `-c` to select such case to verify. Other available pre-defined cases are `h1`, `h2`, `s4` and `s6`.
```
python3 kivi_runner.py -o -c s3
```
You can see the following minimal example demonstrating the traces that lead to the error `no feasible node!`:
```
1 failure(s) are found!
-----Failure #1-----
Minimal example:
[*][CPU Change] CPU change 2 on pod 4, now 10, and node 3, now 46
[*][HPA] Need to rescale, scale metric is 0, original is 5, now is 6.
[*][Deployment] Too few replicas in replicaSet 1 need to create 1
[*][Deployment] Adding a new pod 6 to deployment 1
[*][Scheduler] No feasible node!
```
This shows a five-step example that leads to the issue: 1) CPU changes in a unit of 1 on pod 1; 2) HPA decides to scale up the number of pods to 6; 3/4) deployment controller compares the specReplica and running replica, and creates 1 replica; 5) Scheduler does not found any feasible node for this new pod. 

### Verifying runtime logs
We also implemented a (preliminary) parser to parse the real logs and yamls. We have collected the logs (e.g., `kubectl get deployments`) from Kubernetes clusters that reproduced the aforementioned [S3](documents/failure_cases.md#S3) failure cases, which are stored in `examples/s3` folder. To verify the real clusters, run it with `-p` to enter the path of logs and yamls. 
```
python3 kivi_runner.py -o -p ../examples/s3/from_five_pods
```
You will see a similar output that demonstrates the same minimal example.  

## Documentation
Please find more documents in `documents/`, including an [overview of the system architecture](documents/sys_arch.md). 

It is a work-in-progress. 

## Contributors
This repo is part of the research project **Kivi: Verification for Cluster Management**, authored by [Bingzhe Liu](https://bingzhe.web.engr.illinois.edu/), [Gangmuk Lim](https://gangmuk.github.io/), [Ryan Beckett](https://www.microsoft.com/en-us/research/people/rybecket/) and [P. Brighten Godfrey](https://pbg.cs.illinois.edu/).

## Contact
Bingzhe Liu (bzheliu at gmail.com)

