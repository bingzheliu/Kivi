
/*----------- k8s cluster setup ------------*/
#define MAX_POD [$MAX_POD]
#define MAX_NODE [$MAX_NODE]
#define MAX_DEPLOYMENT [$MAX_DEPLOYMENT]
#define NODE_NUM [$NODE_NUM]
#define POD_NUM [$POD_NUM]
#define DEP_NUM [$DEP_NUM]
#define POD_CPU_THRE 64
#define NODE_ALLOWED_POD_NUM 80
#define POD_TEMPLATE_NUM [$POD_TEMPLATE_NUM]
#define DEP_TEMPLATE_NUM [$DEP_TEMPLATE_NUM]


#define MAX_QUEUE_SIZE 20
/*----------- deployment Config ------------*/
#define MAX_CPU_PATTERN 10
#define SlowStartInitialBatchSize 1


/*----------- scheduler Config ------------*/
// Both are enabled by default for the podSpreading plugins: https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#topologyspreadconstraints-field
#define enableNodeInclusionPolicyInPodTopologySpread 1
#define enableMinDomainsInPodTopologySpread 1
// Because we have 2 default pod spreading policy, so this is true
#define systemDefaulted 1
#define userDefinedConstraints [$userDefinedConstraints]

// scheduler "internal" config, set for their default values. 
#define MAX_LABEL 10
#define MAX_VALUE [$MAX_NODE]
#define MAX_2D [$MAX_NODE]
// https://github.com/kubernetes/kubernetes/blob/c549b59983e114a872b0df18d74c1d217f3f62bd/pkg/scheduler/framework/interface.go#L109
#define MAX_NODE_SCORE 100

#define MAX_TOPO_CON 3


/*----------- hpa Config ------------*/

// HPA "internal" config, set for their default values. 

// default is 10 ( == 0.1 in percentage)
#define HPA_TOLERANCE 10

// These are default value defined in horizontal.go
#define HPA_SCALE_UP_LIMIT_MIN 4
#define HPA_SCALE_UP_LIMIT_FACTOR  2

#define MAX_NUM_METRICS 10

