// 1. default configs and plugins are done according to v1beta3.

// default configs: https://github.com/kubernetes/kubernetes/blob/9ac6c0480a1844194a13dd5a36da1efbc73e63d8/pkg/scheduler/apis/config/v1beta3/defaults.go
// https://kubernetes.io/docs/reference/config-api/kube-scheduler-config.v1beta3/

// each default plugins register themselves in their code: https://github.com/kubernetes/kubernetes/tree/95bd687a284f63535cbf48b0696d8ae57c9929ef/pkg/scheduler/framework/plugins
// https://kubernetes.io/docs/reference/scheduling/config/#scheduling-plugins

// 2. Though plugins can be triggered in multiple stages of scheduler, we could just merge these logic and make it only be on one stage. 

// 3. The following plugins are not modeled for now: ImageLocality, NodePorts, NodeUnschedulable, VolumeBinding
// VolumeRestrictions, VolumeZone, NodeVolumeLimits, EBSLimits, GCEPDLimits, AzureDiskLimits, PrioritySort
// DefaultBinder.


inline helperFilter()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].score == 1 ->
			node[i].score = 0;
		:: nodes[i].score == 0 ->
			node[i].score == -1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od
}

/*******************
Filter plugins
*******************/
inline nodeName()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].name == pods[curPod].nodeName && nodes[i].score != -1 -> nodes[i].score = 1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	helperFilter();
}


// Rules for node affinity (refer to PreFilter() in node_affinity.go):
// 1. nodeAffinity and nodeSelector are ANDed (looks like there would only be one nodeAffinity feild)
// 2. the nodeSelectorTerms in nodeAffinity are ORed
// 3. the requiredDuringSchedulingIgnoredDuringExecution and preferredDuringSchedulingIgnoredDuringExecution are ANDed
// 4. the matchExpressions in nodeSelectorTerms are ANDed. 
inline nodeAffinityFilter()
{
	j = 0;
	do
	:: j < pods[curPod].numRules ->
		if
		:: pods[curPod].affinityRules[j].isRequired == 1 ->
			k = 0;
			do
			:: pods[curPod].affinityRules[j].matchedNode[k] != -1 ->
				if 
				:: nodes[pods[curPod].affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[pods[curPod].affinityRules[j].matchedNode[k]].score = 1;
				:: else->;
				fi;
				k++;
			:: else -> break;
			od
		:: else->;
		fi;
		j++;
	:: else -> break;
	od;

	helperFilter();
}

inline taintToleration()
{
	
}


/*******************
Score plugins
*******************/
// not implemented the reverse
inline defaultNormalizeScore()
{
	max = 0;
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].score != -1 && nodes[i].curScore > max -> 
			max = nodes[i].curScore;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od

	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].score != -1 -> 
			nodes[i].score += (nodes[i].curScore * MAX_NODE_SCORE / nodes[i].curScore);
			nodes[i].curScore = 0;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od
}

inline nodeAffinityScore()
{
	j = 0;
	do
	:: j < pods[curPod].numRules ->
		if
		:: pods[curPod].affinityRules[j].isRequired == 0 ->
			k = 0;
			do
			:: pods[curPod].affinityRules[j].matchedNode[k] != -1 ->
				if 
				:: nodes[pods[curPod].affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[pods[curPod].affinityRules[j].matchedNode[k]].curScore += pods[curPod].affinityRules[j].weight;
				:: else->;
				fi;
				k++;
			:: else -> break;
			od
		:: else->;
		fi;
		j++;
	:: else -> break;
	od;

	defaultNormalizeScore()
}

inline podTopologySpread()
{
	
}

inline nodeResourcesFit()
{
	
}

inline nodeResourcesBalancedAllocation()
{
	
}

inline interPodAffinity()
{
	
}

inline defaultPreemption()
{
	
}

