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

// These matched node include both the affinity rules and the nodeSelector
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
	short priority;

	// node affinity, https://kubernetes.io/docs/concepts/scheduling-eviction/assign-pod-node/#node-affinity
	affinityRule affinityRules[MAX_LABEL];
	short numRules;

	// node name
	short nodeName;

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

	short replicas;
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

	short version;

	// https://kubernetes.io/docs/concepts/workloads/controllers/deployment/#strategy
	// 0 is recreate, 1 is rollingupdates
	bit strategy;

	replicaSetType replicaSets[2];
	bit curVersion; 

	/*****internal****/
	// short podIds[MAX_POD];
	// short numOldVersion;
	// short numNewversion;
	short maxReplicas;
	short expReplicas;

	/****omitting****/
	// short podTemplate;
	// short progressDeadlineSeconds;
	// short minReadySeconds;
	// short maxRetries;
	// bit paused;
}

