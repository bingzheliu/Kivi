# Kivi: verifying your Kubernetes clusters

## Install and Requirement

[Spin](https://github.com/nimble-code/Spin) (>=6.5.2)

### Manual
1. Create `libs`, `results` and `temp` directories under the root dir. 
2. Install [Spin](https://github.com/nimble-code/Spin) into `libs`. 
3. Install required libs by ```pip3 install -r requirements.txt```

Then you are good!

### Script
```
./install.sh
```
This is a simply script that has only been tested in Mac. Pull request are welcome.


## Usage
```
cd bin

python3 kivi_runner.py [options]
```

### Option
```usage: Kivi [-h] (-c CASE | -p PATH) [-o] [-f] [-a] [-v VERBOSE_LEVEL] [-pc PAN_COMPILE] [-pr PAN_RUNTIME] [-s SCALE] [-cn]

Verifier parameters.

optional arguments:
  -h, --help            show this help message and exit
  -c CASE, --case CASE  Verify an exiting cases, entering a case name
  -p PATH, --path PATH  Verify from runtime configs, entering config path
  -s SCALE, --scale SCALE
                        Choose a scale if use -c and -o. Default: 3 nodes.
  -cn, --case_non_violation
                        Deside if generate cases without violations if use -c. Default: False.

Verification parameters:
  -o, --original        Disable finding minimal examples and verify for the original configs
  -f, --fast_find       When finding minimal examples, find the minimal scale faster instead of trying all the scales
  -a, --all_violation   Find all violations (default: stop after finding one)
  -v VERBOSE_LEVEL, --verbose_level VERBOSE_LEVEL
                        Log level for generated examples. Smaller value means less hints in the examples.

Spin options:
  Options sent to pan or spin. All options need to be quoted and seperated by comma without dash, e.g., 'm10000, n'

  -pc PAN_COMPILE, --pan_compile PAN_COMPILE
                        Options for pan compiler.
  -pr PAN_RUNTIME, --pan_runtime PAN_RUNTIME
                        Options for pan runtime
```

## Example
### Verifying pre-defined failure cases
We have prepared a few [failure cases](documents/failure_cases.md) for users to understand our system. 

To test on case [S3](documents/failure_cases.md#S3), you could run it with `-c` to select such case to verify. 
```
python3 kivi_runner.py -o -c s3
```
You can see the following minimal example demonstrating the traces that lead to the error `no feasiable node!`:
```
1 failure(s) are found!
-----Failure #1-----
Minimal example:
[*][CPU Change] CPU change 1 on pod 1, now 9, and node 1, now 15
[*][HPA] Need to rescale, scale metric is 0, orgional is 5, now is 6.
[*][Deployment] Too few replicas in replicaSet 11 need to create 1
[*][Deployment] Adding a new pod 6 to deployment 1
[*][Scheduler] No feasiable node!
```
This shows a five-step example that lead to the issue: 1) CPU changes in a unit of 1 on pod 1; 2) HPA decides to scale up pod to 6; 3/4) deployment controller compares the specReplica and running replica, and creates 1 replica; 5) Scheduler does not found any feasiable node for this new pod. 

### Verifying runtime logs
We also implemented a (preliminary) parser to parse the real logs and yamls. We have collected the logs (e.g., `kubectl get deployments`) from Kubernetes clusters that reproduced the aforementioned [S3](documents/failure_cases.md#S3) failure cases, which are stored in `examples/s3` folder. To verify the real clusters, run it with `-p` to enter the path of logs and yamls. 
```
python3 kivi_runner.py -o -p ../examples/s3/from_five_pods
```
You will see a similar output that demonstrate the same minimal example.  

## Contact
Bingzhe Liu (bzheliu at gmail.com)

