/*
	Note: 
		1. About resources
			a. The unit for resource: m (for CPU) and mi (for memory). 1 core = 1000m. 
			   Details: https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/#resource-units-in-kubernetes
 			b. The resource is calculated by sum of requested resource instead of the actual resource usage.
*/

typedef twoDArray {
	short a[MAX_2D];
}

typedef nodeType {
	short id;
	short name;

	int cpu;
	int cpuLeft;
	int memory;
	int memLeft;

	// 0: false, 1: ready, 2: unhealthy
	unsigned status : 3;
	byte numPod;

	// index is the key, and each index store its value, only 1 value for 1 key
	short labelKeyValue[MAX_LABEL];

	/*----internal---*/
	// used by scheduler
	short score;
	// the current score for the current plugins before normalizing
	short curScore;
	// 1: current node can be scheduled according to affinity
	bit curAffinity;
	// 1: current node can taint the current pod and can't be scheduled
	bit curTaint;

	bit maintained;
}

// TODO: We made an assumption here that pods are managed by the deployment. But it's not always this case. So may need to sepreate more for the pod v.s. deployment.
// But for now, it's OK to assume that is created by other resources: https://kubernetes.io/docs/concepts/workloads/pods/#working-with-pods
typedef podType {
	short id;
	short name;
	byte namespace;
	// No more than 255 nodes
	byte loc;


	// label is per pod basis
	short labelKeyValue[MAX_LABEL];

	// https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#pod-phase
	// 0: idle; 1: running (the only healthy status); 
	// 2: pending (not count for replicas); 3: being terminated (still count for replicas) 
	unsigned status : 3;

	// resource
	int cpu;
	int memory;

	bit critical;

	// CPU pattern change index
	byte curCpuIndex;

	short startTime;

	/*----internal----*/
	// 0: pod, 1: deployment
	// potentially can support CronJob, Job, etc. in the future. 
	unsigned workloadType : 3;
	// If workloadType is 0 (pod), then this is the ID for a podTemplate array (need to define such an array somewhere).
	// Otherwise it's the array index for the deployment (or other types of owners)
	byte workloadId;
	byte podTemplateId;

	short score;
	//short num_deschedule;
	// short toDelete;

	// used for invariants
	bit important;
}

typedef replicaSetType {
	short id;
	short deploymentId;

	short replicas;
	short specReplicas;
	byte version;
	
	/*****internal****/
	// when use each podId, need to check whether 1) podIds is 0, or 2) the related pod status is 0. The index can be larger than replicas.
	short podIds[POD_NUM];

}

// No more than 255 HPA metrics
typedef hpaSpecType {
	bit isEnabled;
	byte numMetrics;
	// 0 means CPU, 1 means Memory
	byte metricNames[MAX_NUM_METRICS];
	short metricTargets[MAX_NUM_METRICS];
	// 0 means values, including PodMetric and the valued ResourceMetric; 1 means utlization, including ResourceMetric
	byte metricTypes[MAX_NUM_METRICS];

	short minReplicas;
	short maxReplicas;
}

// These matched node include the 1) affinity rules, 2) the nodeSelector and 3) the addedAffinity in additional scheduler profiles
typedef affinityRuleType {
	bit isRequired;
	// weight: [1:100]
	byte weight;
	byte numMatchedNode;
	byte matchedNode[MAX_MATCHED_NODE];
}

typedef topoSpreadConType {
	byte maxSkew;
	byte minDomains;

	byte topologyKey;

	// 0: DoNotSchedule, 1: ScheduleAnyway
	bit whenUnsatisfiable;

	// labelSelector: https://kubernetes.io/docs/reference/kubernetes-api/common-definitions/label-selector/#LabelSelector
	// We only support match labels, or anything that can be translated into match labels. 
	// We merge matchLabelKeys with the labelSelector, which is also how they are implemented. 
	// All label values should not exceed 255
	byte numMatchedLabel;
	byte labelKey[MAX_LABEL];
	byte labelValue[MAX_LABEL]

	// 0: ignore, 1: honor
	bit nodeAffinityPolicy;
	bit nodeTaintsPolicy;

	// Omit
	// matchLabelKeys
}

// https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-template-v1/
// TODO: check on if the label key used in nodes can also be used in pods
typedef podTemplateType {
	/*--- metadata ---*/
	short labelKeyValue[MAX_LABEL];

	/*--- podSpec ---*/
	// https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#PodSpec

	// In fact, the requested CPU and memory will be defined for each container in the pod, but we simplified them into one resources for now, and may pre-process the container info in the wrapper functions. 
	// https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#resources
	int cpuRequested;
	int memRequested;

	// For scheduler: https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#scheduling
	//// node affinity, https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#node-affinity
	affinityRuleType affinityRules[MAX_AFFINITY_RULE];
	byte numRules;
	//// node name
	short nodeName;

	//// Taint
	/*
		Taint: we assume taint and toleration won't be modified; and with that, we do not model NoExecute
		noScheduleNode: stores a list of node name that is noSchedulable.
		preferNoScheduleNode: stores a list of node name (can be duplicated, meaning there's multiple taint for that node) that is preferNoScheduleNode. Assuming # of preferred taint is less than 2 in average for node. 
	*/
	byte numNoScheduleNode;
	byte noScheduleNode[MAX_NO_SCHEDULE_NODE];
	short numPreferNoScheduleNode;
	byte preferNoScheduleNode[MAX_PEFER_NO_CHEDULE_NODE];

	//// Pod Spreading Policy
	byte numTopoSpreadConstraints;
	topoSpreadConType topoSpreadConstraints[MAX_TOPO_CON];

	// This is optional. But be aware, if not defined, the initial CPU value will be set to the requested CPU, which may not be user's expectation. 
	// If defined, the timeCpuRequest[0] must be 0 to define the initial behavior of CPU. This field will be mostly used when create pods in runtime.
	// curCpuRequest represent the current CPU usage of the pod; timeCpuRequest represent until when this usage will start. 
	byte maxCpuChange;
	int curCpuRequest[MAX_CPU_PATTERN];
	short timeCpuRequest[MAX_CPU_PATTERN];

	/* 
	   Not implemented.
	   0 means never. pod with this value will be placed in the scheduling queue ahead of lower-priority pods, but they cannot preempt other pods. A non-preempting pod waiting to be scheduled will stay in the scheduling queue. Non-preempting pods may still be preempted by other, high-priority pods.
	   1 means PreemptLowerPriority, which will allow pods of that PriorityClass to preempt lower-priority pods, which is a default behavior.
	   https://kubernetes.io/docs/concepts/scheduling-eviction/pod-priority-preemption/
	*/
	// bit preemptionPolicy;
	//  Not implemented: If the priority class is not found, the Pod is rejected.
	// short priority;

}

typedef deploymentType {
	// We use id as an equivalence as name.
	short id;
	short name;
	byte namespace;
	// TODO: decide if we need status or if we need to delete it, status includes progressing, available.
	// short statusType; 
	bit status;

	replicaSetType replicaSets[2];
	bit curVersion; 

	short specReplicas;
	short replicas;

	/*-----For rollout or recreate-----*/
	// default is 25%
	short maxSurge;
	// default is 25%
	short maxUnavailable;

	// https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#strategy
	// 0 is recreate, 1 is rollingupdates
	short strategy;

	// must be defined for any new deployment
	byte podTemplateId;

	/*-----For HPA-----*/
	hpaSpecType hpaSpec;

	// Internal 
	byte replicasInDeletion;
	byte replicasInCreation;

	/*-----Internal----*/
	byte evicted;

	/*-----omitting-----*/
	// short progressDeadlineSeconds;
	// short minReadySeconds;
	// short maxRetries;
	// bit paused;

	// short label;
	// Omitting labels notes
	// A deployment yaml can contains three places for labels: https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#creating-a-deployment
	// 1. metadata.labels, not fully sure how this connects with pods
	// 2. spec.selector, which demonstrates which pods will be selected for the deployment
	// 3. spec.temlate.metadata, which demonstrate the labels that will be created for the pods. 
	// We are omiting 1 and 2 for now, as we don't find the usage for 1 in our current model, and 2 has been realized in a more direct/simplified way -- we directly store deployment ID in pods and also the reverse.	 
	// We can improve how we treat selector later if needed.

	// short namespace;
	// short selector;
}

//The plugins will be executed in the order of their array index
typedef deschedulerProfileType {
	// removePodsViolatingNodeAffinity: 1
	short numDeschedulePlugins;
	byte deschedulePlugins[MAX_NUM_DESPLUGINS];

	// removeDuplicates: 1; removePodsViolatingTopologySpreadConstraint: 2;
	short numBalancePlugins;
	byte balancePlugins[MAX_NUM_BALPLUGINS];

	// We only support the default evictor for now. If user have multiple evictor, we'll need the following structure.
	// short numEvictorPlugins;
	// byte evictorPlugins[MAX_NUM_EVICPLUGINS];

	// default false
	bit evictSystemCriticalPods;
}

typedef nodePodsArray {
	bit pods[POD_NUM];
	short numPods;
}

typedef deschedulerMatchingArray {
	nodePodsArray nodePods[NODE_NUM];
	bit exist;
}