typedef nodeType {
	short id;
	short zone;
	unsigned cpu : 6;
	unsigned cpuLeft : 6;
	bit status;
	short numPod;
	short name;

	// used by scheduler
	short score;
	//// the current score for the current plugins before normalizing
	short curScore;

	// nodel labels --> May not be useful if we pre-processing the affinity rules
	short numLabel;
	short labelName[MAX_LABEL];
	short labelValue[MAX_LABEL];
}

// These matched node include the 1) affinity rules, 2) the nodeSelector and 3) the addedAffinity in additional scheduler profiles
typedef affinityRule{
	bit isRequired;
	// weight: [1:100]
	short weight;
	// We pre-processed the regex when generated the model. valid until hit value == -1.
	short matchedNode[NODE_NUM];
}


typedef podType {
	short id;
	short loc;

	// https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#pod-phase
	// 0: pending; 1: running; 2: terminated (not sure if we need this)
	short status;
	short cpu;
	short label;
	short version;

	short deploymentId;

	/*****internal****/
	short score;
	//short num_deschedule;
	short toDelete;

	// used for invariants
	bit important;
}

typedef replicaSetType {
	short id;
	short deploymentId;

	short replicas;
	short version;
	
	/*****internal****/
	short podIds[MAX_POD];
	short expReplicas;
}


typedef deploymentType {
	short id;

	// In fact, the requested CPU and memory will be defined for each container in the pod, but we simplified them into one resources for now, and may pre-process the container info in the wrapper functions. 
	short cpuRequested;
	short memRequested;

	// Need to convert label and namespace from string into an ID 
	// TODO: improve how we treawt selector later
	short label;
	short namespace;
	short selector;

	// default is 25%
	short maxSurge;
	// default is 25%
	short maxUnavailable;
	// progressing, available
	short statusType; 
	bit status;

	// short version;

	// https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#strategy
	// 0 is recreate, 1 is rollingupdates
	bit strategy;

	replicaSetType replicaSets[2];
	bit curVersion; 

	// node affinity, https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#node-affinity
	affinityRule affinityRules[MAX_LABEL];
	short numRules;

	// node name
	short nodeName;

	/* 
	   0 means never. pod with this value will be placed in the scheduling queue ahead of lower-priority pods, but they cannot preempt other pods. A non-preempting pod waiting to be scheduled will stay in the scheduling queue. Non-preempting pods may still be preempted by other, high-priority pods.
	   1 means PreemptLowerPriority, which will allow pods of that PriorityClass to preempt lower-priority pods, which is a default behavior.
	   https://kubernetes.io/docs/concepts/scheduling-eviction/pod-priority-preemption/
	*/
	bit preemptionPolicy;

	//  If the priority class is not found, the Pod is rejected.
	short priority;

	/*
		Taint: we assume taint and toleration won't be modified; and with that, we do not model NoExecute
		noScheduleNode: stores a list of node name that is noSchedulable.
		preferNoScheduleNode: stores a list of node name (can be duplicated, meaning there's multiple taint for that node) that is preferNoScheduleNode. Assuming # of preferred taint is less than 2 in average for node. 
	*/
	short numNoScheduleNode;
	short noScheduleNode[NUM_NODE];
	short numPreferNoScheduleNode;
	short preferNoScheduleNode[NUM_NODE*2];


	/*****internal****/
	// short podIds[MAX_POD];
	// short numOldVersion;
	// short numNewversion;
	short maxReplicas;
	short expReplicas;
	short replicas;

	/****omitting****/
	// short podTemplate;
	// short progressDeadlineSeconds;
	// short minReadySeconds;
	// short maxRetries;
	// bit paused;
}

