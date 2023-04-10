// TODO: refine the array sizes to save spaces. 
// typedef queueType {
// 	short q[MAX_QUEUE_SIZE]
// }

typedef twoDArray {
	short a[MAX_2D];
}

typedef nodeType {
	short id;
	short name;

	short cpu;
	short cpuLeft;
	short memory;
	short memLeft;

	// 0: false, 1: ready, 2: unhealthy
	short status;
	short numPod;

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
	short loc;

	// https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#pod-phase
	// 0: idle; 1: running (the only healthy status); 
	// 2: pending (not count for replicas); 3: being terminated (still count for replicas) 
	short status;

	// resource
	short cpu;
	short memory;

	/*----internal----*/
	// 0: pod, 1: deployment
	// potentially can support CronJob, Job, etc. in the future. 
	short workloadType;
	// If workloadType is 0 (pod), then this is the ID for a podTemplate array (need to define such an array somewhere).
	short workloadId;
	short podTemplateId;

	short score;
	//short num_deschedule;
	// short toDelete;

	// used for invariants
	bit important;

	// CPU pattern change index
	short curCpuIndex;
}

typedef replicaSetType {
	short id;
	short deploymentId;

	short replicas;
	short specReplicas;
	short version;
	
	/*****internal****/
	// when use each podId, need to check whether 1) podIds is 0, or 2) the related pod status is 0. The index can be larger than replicas.
	short podIds[MAX_POD];

}

typedef hpaSpecType {
	bit isEnabled;
	short numMetrics;
	short metricNames[MAX_NUM_METRICS];
	short metricTargets[MAX_NUM_METRICS];
	// 0 means values, including PodMetric and the valued ResourceMetric; 1 means utlization, including ResourceMetric
	short metricTypes[MAX_NUM_METRICS];

	short minReplicas;
	short maxReplicas;
}

// These matched node include the 1) affinity rules, 2) the nodeSelector and 3) the addedAffinity in additional scheduler profiles
typedef affinityRuleType {
	bit isRequired;
	// weight: [1:100]
	short weight;
	short numMatchedNode;
	short matchedNode[MAX_NODE];
}

typedef topoSpreadConType {
	short maxSkew;
	short minDomains;

	short topologyKey;

	// 0: DoNotSchedule, 1: ScheduleAnyway
	bit whenUnsatisfiable;

	// labelSelector: https://kubernetes.io/docs/reference/kubernetes-api/common-definitions/label-selector/#LabelSelector
	// We only support match labels, or anything that can be translated into match labels. 
	// We merge matchLabelKeys with the labelSelector, which is also how they are implemented. 
	short numMatchedLabel;
	short labelKey[MAX_LABEL];
	short labelValue[MAX_LABEL]


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
	// TODO: this may need to be seperate from this template as it's a runtime info
	// now this label is for a workload; if the label is per pod, need to model it in a different way.
	short labelKeyValue[MAX_LABEL];

	/*--- podSpec ---*/
	// https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#PodSpec

	// In fact, the requested CPU and memory will be defined for each container in the pod, but we simplified them into one resources for now, and may pre-process the container info in the wrapper functions. 
	// https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#resources
	short cpuRequested;
	short memRequested;

	// For scheduler: https://kubernetes.io/docs/reference/kubernetes-api/workload-resources/pod-v1/#scheduling
	//// node affinity, https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#node-affinity
	affinityRuleType affinityRules[MAX_LABEL];
	short numRules;
	//// node name
	short nodeName;

	//// Taint
	/*
		Taint: we assume taint and toleration won't be modified; and with that, we do not model NoExecute
		noScheduleNode: stores a list of node name that is noSchedulable.
		preferNoScheduleNode: stores a list of node name (can be duplicated, meaning there's multiple taint for that node) that is preferNoScheduleNode. Assuming # of preferred taint is less than 2 in average for node. 
	*/
	short numNoScheduleNode;
	short noScheduleNode[MAX_NODE];
	short numPreferNoScheduleNode;
	short preferNoScheduleNode[NODE_NUM*2];

	//// Pod Spreading Policy
	short numTopoSpreadConstraints;
	topoSpreadConType topoSpreadConstraints[MAX_TOPO_CON];

	short maxCpuChange;
	short curCpuRequest[MAX_CPU_PATTERN];

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
	// We use id as an equivalence as name
	short id;
	short name;
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
	bit strategy;

	short podTemplateId;

	/*-----For HPA-----*/
	hpaSpecType hpaSpec;


	// Internal 
	short replicasInDeletion;
	short replicasInCreation;

	/*-----omitting-----*/
	// short progressDeadlineSeconds;
	// short minReadySeconds;
	// short maxRetries;
	// bit paused;


	// Need to convert label and namespace from string into an ID 
	// TODO: improve how we treat selector later
	// short label;
	// short namespace;
	// short selector;
}

