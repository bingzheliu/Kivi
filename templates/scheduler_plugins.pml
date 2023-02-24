// 1. default configs and plugins are done according to v1beta3.

// default configs: https://github.com/kubernetes/kubernetes/blob/9ac6c0480a1844194a13dd5a36da1efbc73e63d8/pkg/scheduler/apis/config/v1beta3/defaults.go
// https://kubernetes.io/docs/reference/config-api/kube-scheduler-config.v1beta3/

// each default plugins register themselves in their code: https://github.com/kubernetes/kubernetes/tree/95bd687a284f63535cbf48b0696d8ae57c9929ef/pkg/scheduler/framework/plugins
// https://kubernetes.io/docs/reference/scheduling/config/#scheduling-plugins


// default weight: https://github.com/kubernetes/kubernetes/blob/9ac6c0480a1844194a13dd5a36da1efbc73e63d8/pkg/scheduler/apis/config/v1beta3/default_plugins.go

// 2. Though plugins can be triggered in multiple stages of scheduler, we could just merge these logic and make it only be on one stage. 

// 3. The following plugins are not modeled for now: ImageLocality, NodePorts, NodeUnschedulable, VolumeBinding
// VolumeRestrictions, VolumeZone, NodeVolumeLimits, EBSLimits, GCEPDLimits, AzureDiskLimits, PrioritySort
// DefaultBinder.

// 4. TODO: a few plugins are interesting, but have not implemented -- podSpreading, preemption, balancedResource. 

#define TAINT_WEIGHT 3
#define NODE_AFFINITY_WEIGHT 2
#define NODE_RESOURCE_FIT 1
#define NODE_PODTOPO_SPREAD_WEIGHT 2
// unsure about this in v1beta3, looks like if it's undefined, the framework will give it a 1. 
#define NODE_NAME_WEIGHT 1

// 1: leastAllocated, 2: mostAllocated...
#define STRATEGY_RESOURCE 1


inline helperFilter()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].score == 1 ->
			nodes[i].score = 0;
		:: nodes[i].score == 0 ->
			nodes[i].score = -1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od
}

/*******************
Filter plugins

Now assume the order of these plugins do not matter, and should be idempotence
*******************/
// TODO: check where this has been called.
// Using nodeName overrules using nodeSelector or affinity and anti-affinity rules.
inline nodeNameFilter()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: ((d[pods[curPod].deploymentId].nodeName == 0) || (nodes[i].name == d[pods[curPod].deploymentId].nodeName)) && (nodes[i].score != -1) -> nodes[i].score = 1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	helperFilter();

	printf("Finished nodeNameFilter.\n")
	printfNodeScore();
}


// Rules for node affinity (refer to PreFilter() in node_affinity.go):
// 1. nodeAffinity and nodeSelector are ANDed (looks like there would only be one nodeAffinity feild)
// 2. the nodeSelectorTerms in nodeAffinity are ORed
// 3. the requiredDuringSchedulingIgnoredDuringExecution and preferredDuringSchedulingIgnoredDuringExecution are ANDed
// 4. the matchExpressions in nodeSelectorTerms are ANDed. 
// 5. the addedAffinity and NodeAffinity are ANDed (and would be processed by pre-processors). 
inline nodeAffinityFilter()
{
	bit flag = 1;
	j = 0;
	do
	:: j < d[curD].numRules ->
		if
		:: d[curD].affinityRules[j].isRequired == 1 ->
			k = 0;
			flag = 0;
			do
			:: d[curD].affinityRules[j].matchedNode[k] != 0 ->
				if 
				:: nodes[d[curD].affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[d[curD].affinityRules[j].matchedNode[k]].score = 1;
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

	if 
		:: flag == 1->
			j = 1;
			do
			:: j < NODE_NUM+1 ->
				if
					:: nodes[j].score = -1 -> nodes[j].score = 1;
					:: else->;
				fi;
				j++;
			:: else -> break;
			od;
		:: else->;
	fi;

	helperFilter();

	printf("Finished nodeAffinityFilter.\n")
	printfNodeScore();
}

inline taintTolerationFilter()
{
	j = 0;
	do
	:: j < d[curD].numNoScheduleNode ->
	   nodes[d[curD].noScheduleNode[j]].score = -1;
	   j++;
	:: else -> break;
	od;

	printf("Finished taintTolerationFilter.\n")
	printfNodeScore();
}


/*******************
Score plugins
*******************/
// not implemented the reverse
inline defaultNormalizeScoreAndWeight(reverse, weight)
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

	if
	:: max == 0 && reverse == 1 ->
		i = 1;
		do
		:: i < NODE_NUM+1 ->
			if 
				:: nodes[i].score != -1 -> 
					 nodes[i].curScore = MAX_NODE_SCORE;
					 nodes[i].score = nodes[i].score + (nodes[i].curScore * weight);
					 nodes[i].curScore = 0;
				:: else->;
			fi;
			i++;
		:: else -> break;
		od;
		goto s2;
	:: max == 0 && reverse == 0 ->
		goto s2;
	:: else->;
	fi;

	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: nodes[i].score != -1 -> 
			nodes[i].curScore = (nodes[i].curScore * MAX_NODE_SCORE / max);
			if
			:: reverse == 1 ->
				nodes[i].curScore = MAX_NODE_SCORE - nodes[i].curScore;
			:: else->;
			fi;
			nodes[i].score = nodes[i].score + (nodes[i].curScore * weight);
			nodes[i].curScore = 0;
		:: else->;
		fi;
		i++;
	:: else -> break;
s2:	od
}

inline nodeAffinityScore()
{
	j = 0;
	do
	:: j < d[curD].numRules ->
		if
		:: d[curD].affinityRules[j].isRequired == 0 ->
			k = 0;
			do
			:: d[curD].affinityRules[j].matchedNode[k] != 0 ->
				if 
				:: nodes[d[curD].affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[d[curD].affinityRules[j].matchedNode[k]].curScore = nodes[d[curD].affinityRules[j].matchedNode[k]].curScore + d[curD].affinityRules[j].weight;
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

	defaultNormalizeScoreAndWeight(0, NODE_AFFINITY_WEIGHT);

	printf("Finished nodeAffinityScore.\n")
	printfNodeScore();
}

inline taintTolerationScore()
{
	j = 0;
	do
	:: j < d[curD].numPreferNoScheduleNode ->
		k = d[curD].preferNoScheduleNode[j];
		if 
		:: nodes[k].score != -1 ->
			nodes[k].curScore++;
		:: else->;
	  	fi;
	   j++;
	:: else -> break;
	od;

	defaultNormalizeScoreAndWeight(1, TAINT_WEIGHT);

	printf("Finished taintTolerationScore.\n")
	printfNodeScore();
}


// we only model allowedPod, CPU and mem for now. 
inline nodeResourcesFitFilter()
{	
	i = 1;
	j = pods[curPod].deploymentId;
	do 
	::	i < NODE_NUM+1 ->
		if
		::  (d[j].cpuRequested > nodes[i].cpuLeft) || (d[j].memRequested > nodes[i].memLeft) || (nodes[i].numPod + 1) > NODE_ALLOWED_POD_NUM -> 
			nodes[i].score = -1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	printf("Finished nodeResourcesFitFilter.\n")
	printfNodeScore();
}

/*
 	default resource spec (weight), where both cpu and mem are weighted 1: https://github.com/kubernetes/kubernetes/blob/d436f5d0b7eb87f78eb31c12466e2591c24eef59/pkg/scheduler/apis/config/v1beta3/defaults.go#L31
	according to 
		- LeastAllocated impl: https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/least_allocated.go#L29
		- mostAllocated impl: https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/most_allocated.go#L30
*/
inline nodeResourceFitScore()
{
	i = 1;
	j = pods[curPod].deploymentId;
	short cpuScore, memScore;
	do 
	::	i < NODE_NUM+1 ->
		if
		:: nodes[i].score != -1 ->
			if 
				:: STRATEGY_RESOURCE == 1 ->
					cpuScore = ((nodes[i].cpuLeft - d[j].cpuRequested) * MAX_NODE_SCORE / nodes[i].cpuLeft) * 1;
					memScore = ((nodes[i].memLeft - d[j].memRequested) * MAX_NODE_SCORE / nodes[i].memLeft) * 1;
					nodes[i].score = nodes[i].score + ((cpuScore+memScore) * NODE_RESOURCE_FIT / 2 )
				:: STRATEGY_RESOURCE == 2 ->
					cpuScore = ((d[j].cpuRequested) * MAX_NODE_SCORE / nodes[i].cpuLeft) * 1;
					memScore = ((d[j].memRequested) * MAX_NODE_SCORE / nodes[i].memLeft) * 1;
					nodes[i].score = nodes[i].score + ((cpuScore+memScore) * NODE_RESOURCE_FIT / 2 )
				:: else -> 
					printf("No/Wrong scheduling strategy defined!\n");
					assert(false);
			fi;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	printf("Finished nodeResourceFitScore.\n")
	printfNodeScore();
}

/* May not implement for now, as it is suggested not to use it in large cluster. 
inline interPodAffinity()
{
	
}
*/

/* May not implement this for now. But this is interesting and should be implement in the next phase
If this comes into play, we will need to consider how to do re-scheduling, and also may need to distinguish between the three stage of the filters, which are "architecture"-level change. So postpond it a bit for now. 
inline defaultPreemption()
{
	
}
*/

/*
inline podTopologySpread()
{
	
}

// https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/balanced_allocation.go
inline nodeResourcesBalancedAllocation()
{
	
}
*/