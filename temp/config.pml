
/*----------- k8s cluster setup ------------*/
#define MAX_POD 205
#define MAX_NODE 104
#define MAX_DEPLOYMENT 4
#define NODE_NUM 101
#define POD_NUM 202
#define DEP_NUM 1
#define POD_CPU_THRE 64
#define NODE_ALLOWED_POD_NUM 80
#define POD_TEMPLATE_NUM 3


/*----------- deployment Config ------------*/
#define DEPLOYMENT_QUEUE_SIZE 250


/*----------- scheduler Config ------------*/
// Both are enabled by default for the podSpreading plugins: https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#topologyspreadconstraints-field
#define enableNodeInclusionPolicyInPodTopologySpread 1
#define enableMinDomainsInPodTopologySpread 1

// scheduler "internal" config, set for their default values. 
#define SCHEDULER_QUEUE_SIZE 250

#define MAX_LABEL 10
#define MAX_VALUE 104
#define MAX_2D 104
// https://github.com/kubernetes/kubernetes/blob/c549b59983e114a872b0df18d74c1d217f3f62bd/pkg/scheduler/framework/interface.go#L109
#define MAX_NODE_SCORE 100

#define MAX_TOPO_CON 3


/*----------- hpa Config ------------*/
#define HPA_MAX_REPLICAS 1000
// #define HPA_MAX_REPLICAS 5

// HPA "internal" config, set for their default values. 
#define HPA_QUEUE_SIZE 250

// default is 0.1
#define HPA_TOLERANCE 0
#define HPA_MIN_REPLICAS 1

#define HPA_SCALE_UP_LIMIT_MIN 4
#define HPA_SCALE_UP_LIMIT_FACTOR  2

#define MAX_NUM_METRICS 10



