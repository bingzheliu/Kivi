typedef nodeType {
	short id;
	short name;
	short zone;

	unsigned cpu : 6;
	unsigned cpuLeft : 6;
	unsigned mem : 6;
	unsigned memLeft : 6;

	bit status;
	short numPod;

	/*----internal---*/
	// used by scheduler
	short score;
	// the current score for the current plugins before normalizing
	short curScore;

	/*
	// nodel labels --> May not be useful if we pre-processing the affinity rules
	short numLabel;
	short labelName[MAX_LABEL];
	short labelValue[MAX_LABEL];
	*/
}


typedef podType {
	short id;
	short loc;

	// https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#pod-phase
	// 0: pending; 1: running; 2: terminated (not sure if we need this)
	short status;
	short deploymentId;

	// resource
	short cpu;
	short memory;

	/*----internal----*/
	short score;
	//short num_deschedule;
	short toDelete;

	// used for invariants
	bit important;

	/*----Omit----*/
	// short label;
}

typedef replicaSetType {
	short id;
	short deploymentId;

	short replicas;
	short specReplicas;
	short version;
	
	/*****internal****/
	short podIds[MAX_POD];

}

typedef hpaSpecType {
	bit isEnabled;
	short numMetrics;
	short metricNames[MAX_NUM_METRICS];
	short metricTargets[MAX_NUM_METRICS];
	// 0 means values, including PodMetric and the valued ResourceMetric; 1 means utlization, including ResourceMetric
	short metricTypes[MAX_NUM_METRICS];
}

// These matched node include the 1) affinity rules, 2) the nodeSelector and 3) the addedAffinity in additional scheduler profiles
typedef affinityRule{
	bit isRequired;
	// weight: [1:100]
	short weight;
	// We pre-processed the regex when generated the model. valid until hit value == -1.
	short matchedNode[NODE_NUM];
}


typedef deploymentType {
	short id;
	// TODO: decide if we need status or if we need to delete it, status includes progressing, available.
	short statusType; 
	bit status;

	replicaSetType replicaSets[2];
	bit curVersion; 

	short minReplicas;
	short maxReplicas;
	short specReplicas;
	short replicas;

	// In fact, the requested CPU and memory will be defined for each container in the pod, but we simplified them into one resources for now, and may pre-process the container info in the wrapper functions. 
	short cpuRequested;
	short memRequested;

	/*-----For rollout or recreate-----*/
	// default is 25%
	short maxSurge;
	// default is 25%
	short maxUnavailable;

	// https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#strategy
	// 0 is recreate, 1 is rollingupdates
	bit strategy;

	/*-----For scheduler-----*/
	// node affinity, https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#node-affinity
	affinityRule affinityRules[MAX_LABEL];
	short numRules;
	// node name
	short nodeName;

	/*
		Taint: we assume taint and toleration won't be modified; and with that, we do not model NoExecute
		noScheduleNode: stores a list of node name that is noSchedulable.
		preferNoScheduleNode: stores a list of node name (can be duplicated, meaning there's multiple taint for that node) that is preferNoScheduleNode. Assuming # of preferred taint is less than 2 in average for node. 
	*/
	short numNoScheduleNode;
	short noScheduleNode[NODE_NUM];
	short numPreferNoScheduleNode;
	short preferNoScheduleNode[NODE_NUM*2];
	

	/*-----For HPA-----*/
	hpaSpecType hpaSpec;


	/*-----omitting-----*/
	// short podTemplate;
	// short progressDeadlineSeconds;
	// short minReadySeconds;
	// short maxRetries;
	// bit paused;


	// Need to convert label and namespace from string into an ID 
	// TODO: improve how we treat selector later
	// short label;
	// short namespace;
	// short selector;

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

