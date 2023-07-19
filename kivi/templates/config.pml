
/*----------- k8s cluster setup ------------*/
//#define MAX_POD [$MAX_POD]
//#define MAX_NODE [$MAX_NODE]
//#define MAX_DEPLOYMENT [$MAX_DEPLOYMENT]
// Can't be more than 255
#define NODE_NUM [$NODE_NUM]
#define POD_NUM [$POD_NUM]
#define DEP_NUM [$DEP_NUM]
#define POD_CPU_THRE 64
#define NODE_ALLOWED_POD_NUM 80
#define POD_TEMPLATE_NUM [$POD_TEMPLATE_NUM]
#define DEP_TEMPLATE_NUM [$DEP_TEMPLATE_NUM]

// Propotional to the pods/nodes/deployments size
#define MAX_SCHEDULER_QUEUE [$POD_QUEUE]
#define MAX_KUBELET_QUEUE [$POD_QUEUE]
#define MAX_NODE_CONTROLLER_QUEUE [$NODE_QUEUE]
#define MAX_HPA_QUEUE [$DEP_QUEUE]
#define MAX_DEP_QUEUE [$DEP_QUEUE]
/*----------- deployment Config ------------*/

#define SlowStartInitialBatchSize 1


/*----------- scheduler Config ------------*/
// Both are enabled by default for the podSpreading plugins: https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#topologyspreadconstraints-field
#define enableNodeInclusionPolicyInPodTopologySpread 1
#define enableMinDomainsInPodTopologySpread 1
// Because we have 2 default pod spreading policy, so this is true
#define systemDefaulted 1
#define userDefinedConstraints [$userDefinedConstraints]

// scheduler "internal" config, set for their default values. 
#define MAX_LABEL [$MAX_LABEL]
#define MAX_VALUE [$MAX_VALUE]
#define MAX_2D [$MAX_VALUE]
// https://github.com/kubernetes/kubernetes/blob/c549b59983e114a872b0df18d74c1d217f3f62bd/pkg/scheduler/framework/interface.go#L109
#define MAX_NODE_SCORE 100


/*----------- hpa Config ------------*/

// HPA "internal" config, set for their default values. 

// default is 10 ( == 0.1 in percentage)
#define HPA_TOLERANCE 10

// These are default value defined in horizontal.go
#define HPA_SCALE_UP_LIMIT_MIN 4
#define HPA_SCALE_UP_LIMIT_FACTOR  2

/*----------- Array Config ------------*/
#define MAX_NUM_METRICS [$MAX_NUM_METRICS]
#define MAX_NO_SCHEDULE_NODE [$MAX_NO_SCHEDULE_NODE]
#define MAX_PEFER_NO_CHEDULE_NODE [$MAX_PEFER_NO_CHEDULE_NODE]
#define MAX_TOPO_CON [$MAX_TOPO_CON]
#define MAX_AFFINITY_RULE [$MAX_AFFINITY_RULE]
#define MAX_MATCHED_NODE [$MAX_MATCHED_NODE]
#define MAX_CPU_PATTERN [$MAX_CPU_PATTERN]


/*----------- Time Config ------------*/
// TODO: all the time can be config along with the event by the users
#define HPA_RUN_TIME 1
#define HPA_WAIT_TIME 15
#define SCHEDULER_RUN_TIME 1
#define DEP_RUN_TIME 1
#define KUBELET_RUN_TIME 1
#define NODEC_RUN_TIME 1
#define MAINTENANCE_WAIT_TIME 60
#define KERNEL_RECOVER_TIME 60
#define EVENT_CPU_TIME 60
// Default descheduler interval is 5min
#define DESCHEDULER_WAIT_TIME 300


/*--------- Descheduler Config -----------*/
#define maxNoOfPodsToEvictPerNode 5000
#define maxNoOfPodsToEvictPerNamespace 5000
#define MAX_NUM_DESPLUGINS 6
#define MAX_NUM_BALPLUGINS 4
#define MAX_NUM_EVICPLUGINS 1
// TBC for descheduler test
#define DES_PROFILE_NUM 1
