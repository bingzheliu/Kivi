# Kivi: verifying your Kubernetes clusters

## Install and Requirement

[Spin](https://github.com/nimble-code/Spin) (>=6.5.2)

### Manual
1. Create `libs`, `results` and `temp` directories under the root dir. 
2. Install [Spin](https://github.com/nimble-code/Spin) into libs. 
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

### Example
Test on case S3. 
```
python3 kivi_runner.py -c s3
```
You can see the following minimal example demonstrating the traces that lead to the error `no feasiable node!`:
```
1 failure(s) are found!
-----Failure #1-----
Minimal example:
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 1 to deployment 1
[*][Scheduler]Pod 1 is scheduled on node 1, with score 581
[*][Kubelet]Created pod 1 on node 1, deployment 1 now have 1 replicas
[*][CPU Change]node 1, now 51
[*][HPA]Need to rescale, scale metric is 0, orgional is 1, now is 2.
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 2 to deployment 1
[*][Scheduler]Pod 2 is scheduled on node 2, with score 581
[*][Kubelet]Created pod 2 on node 2, deployment 1 now have 2 replicas
[*][HPA]Need to rescale, scale metric is 0, orgional is 2, now is 3.
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 3 to deployment 1
[*][Scheduler]Pod 3 is scheduled on node 3, with score 581
[*][Kubelet]Created pod 3 on node 3, deployment 1 now have 3 replicas
[*][HPA]Need to rescale, scale metric is 0, orgional is 3, now is 4.
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 4 to deployment 1
[*][Scheduler]Pod 4 is scheduled on node 1, with score 575
[*][Kubelet]Created pod 4 on node 1, deployment 1 now have 4 replicas
[*][HPA]Need to rescale, scale metric is 0, orgional is 4, now is 5.
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 5 to deployment 1
[*][Scheduler]Pod 5 is scheduled on node 2, with score 575
[*][Kubelet]Created pod 5 on node 2, deployment 1 now have 5 replicas
[*][HPA]Need to rescale, scale metric is 0, orgional is 5, now is 6.
[*][Deployment]Too few replicas in replicaSet 4 need to create 1
[*][Deployment]Adding a new pod 6 to deployment 1
[*][Scheduler]No feasiable node!
```

## Contact
Bingzhe Liu (bzheliu at gmail.com)

