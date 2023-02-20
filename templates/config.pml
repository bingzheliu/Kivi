
/*----------- k8s cluster setup ------------*/
#define MAX_POD 10
#define NODE_NUM 10
#define POD_NUM 10
#define POD_CPU_THRE 64
#define NODE_ALLOWED_POD_NUM 80



/*----------- deployment Config ------------*/
#define DEPLOYMENT_QUEUE_SIZE 100


/*----------- scheduler Config ------------*/

// scheduler "internal" config, set for their default values. 
#define SCHEDULER_QUEUE_SIZE 100

#define MAX_LABEL 10
// https://github.com/kubernetes/kubernetes/blob/c549b59983e114a872b0df18d74c1d217f3f62bd/pkg/scheduler/framework/interface.go#L109
#define MAX_NODE_SCORE 100

// #define SCHEDULER_THRE_NODE 1
// #define SCHEDULER_THRE_ZONE 1



/*----------- hpa Config ------------*/
// #define HPA_MAX_REPLICAS [$MAX_REPLICAS]
#define HPA_MAX_REPLICAS 5

// HPA "internal" config, set for their default values. 
#define HPA_QUEUE_SIZE 100

#define HPA_THRE 4
#define HPA_TOLERANCE 1
#define HPA_MIN_REPLICAS 1

#define HPA_SCALE_UP_LIMIT_MIN 4
#define HPA_SCALE_UP_LIMIT_FACTOR  2

#define MAX_NUM_METRICS 10



