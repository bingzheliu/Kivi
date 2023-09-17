
/*----------- k8s cluster setup ------------*/
//#define MAX_POD [$MAX_POD]
//#define MAX_NODE [$MAX_NODE]
//#define MAX_DEPLOYMENT [$MAX_DEPLOYMENT]
// Can't be more than 255
#define NODE_NUM [$NODE_NUM]
#define POD_NUM [$POD_NUM]
#define DEP_NUM [$DEP_NUM]
// Will need to make it an variable if work for more namespaces.
#define NAMESPACE_NUM 1
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
#define MAX_DESCHEDULER_QUEUE [$POD_QUEUE]
#define MAX_TAINT_MANAGER_QUEUE [$POD_QUEUE]
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
#define MAX_NO_EXECUTE_NODE [$MAX_NO_EXECUTE_NODE]
#define MAX_NO_SCHEDULE_NODE [$MAX_NO_SCHEDULE_NODE]
#define MAX_PEFER_NO_CHEDULE_NODE [$MAX_PEFER_NO_CHEDULE_NODE]
#define MAX_TOPO_CON [$MAX_TOPO_CON]
#define MAX_AFFINITY_RULE [$MAX_AFFINITY_RULE]
#define MAX_MATCHED_NODE [$MAX_MATCHED_NODE]
#define MAX_CPU_PATTERN [$MAX_CPU_PATTERN]


/*----------- Time Config ------------*/
// TODO: all the time can be config along with the event by the users
// 1 = 0.1s
#define HPA_RUN_TIME 1
#define HPA_WAIT_TIME 150
#define SCHEDULER_RUN_TIME 1
#define DEP_RUN_TIME 1
#define KUBELET_RUN_TIME 1
#define NODEC_RUN_TIME 1
#define MAINTENANCE_WAIT_TIME 600
#define KERNEL_RECOVER_TIME 600
#define EVENT_CPU_TIME 600
// Default descheduler interval is 5min
#define DESCHEDULER_WAIT_TIME 3000


/*--------- Descheduler Config -----------*/
#define maxNoOfPodsToEvictPerNode [$maxNoOfPodsToEvictPerNode]
#define maxNoOfPodsToEvictPerNamespace [$maxNoOfPodsToEvictPerNamespace]
#define MAX_NUM_DESPLUGINS [$MAX_NUM_DESPLUGINS]
#define MAX_NUM_BALPLUGINS [$MAX_NUM_BALPLUGINS]
#define MAX_NUM_EVICPLUGINS 1
// TBC for descheduler test
#define DES_PROFILE_NUM [$DES_PROFILE_NUM]

/*--------- Event Config -----------*/
// TODO: this can be passed as a parameter by the users
#define EVENT_CPU_COUNT 3

/*--------- Intent Config -----------*/
#define LOOP_TIMES [$LOOP_TIMES]

/*--------- Internal Config -----------*/
#define UNDEFINED_VALUE 0

/*--------- optimization ------*/
// #define TRANSIT 1
// By default we don't look into the failures in transit (kubelet hence always run first than deployment).
#define BACK_TO_BACK_OPT 1

/*--------- ifdef ----------*/
// Intents: NO_FEASIABLE_NODE, 
// Data structure: MORE_PODS
[$IFDEF]