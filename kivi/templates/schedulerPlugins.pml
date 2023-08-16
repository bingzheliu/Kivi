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

// 4. TODO: a few plugins are interesting, but have not implemented -- preemption, balancedResource. 

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
inline nodeNameFilter(podSpec)
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if
		:: ((podSpec.nodeName == 0) || (nodes[i].name == podSpec.nodeName)) && (nodes[i].score != -1) -> nodes[i].score = 1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	helperFilter();

	printf("[***][SchedulerPlugins] Finished nodeNameFilter.\n")
	printfNodeScore();
}


// Rules for node affinity (refer to PreFilter() in node_affinity.go):
// 1. nodeAffinity and nodeSelector are ANDed (looks like there would only be one nodeAffinity feild)
// 2. the nodeSelectorTerms in nodeAffinity are ORed
// 3. the requiredDuringSchedulingIgnoredDuringExecution and preferredDuringSchedulingIgnoredDuringExecution are ANDed
// 4. the matchExpressions in nodeSelectorTerms are ANDed. 
// 5. the addedAffinity and NodeAffinity are ANDed (and would be processed by pre-processors). 
inline nodeAffinityFilter(podSpec)
{
	bit flag = 1;
	j = 0;
	for (j : 0 .. podSpec.numRules - 1) {
		if
		:: podSpec.affinityRules[j].isRequired == 1 ->
			k = 0;
			flag = 0;
			for (k : 0 .. podSpec.affinityRules[j].numMatchedNode - 1) {
				if 
				:: nodes[podSpec.affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[podSpec.affinityRules[j].matchedNode[k]].score = 1;
					nodes[podSpec.affinityRules[j].matchedNode[k]].curAffinity = 1;
				:: else->;
				fi;
			}
		:: else->;
		fi;
	}

	if 
		:: flag == 1->
			j = 1;
			for (j : 1 .. NODE_NUM) {
				if
					:: nodes[j].score != -1 -> 
						nodes[j].score = 1;
						nodes[j].curAffinity = 1;
					:: else->;
				fi;
			}
		:: else->;
	fi;

	helperFilter();

	printf("[***][SchedulerPlugins] Finished nodeAffinityFilter.\n")
	printfNodeScore();
}

inline taintTolerationFilter(podSpec)
{
	j = 0;
	do
	:: j < podSpec.numNoScheduleNode ->
	   nodes[podSpec.noScheduleNode[j]].score = -1;
	   nodes[podSpec.noScheduleNode[j]].curTaint = 1;
	   j++;
	:: else -> break;
	od;

	printf("[***][SchedulerPlugins] Finished taintTolerationFilter.\n")
	printfNodeScore();
}

// helper function for pod spreading policy
inline findMatchedPod(i, j, podSpec)
{
	k = 1;
	
	for (k : 1 .. POD_NUM) {
		printf("[******] Matching pod %d (status %d, loc %d)\n", k, pods[k].status, pods[k].loc)
		if 
			// TODO: check if this pod status can be 2 (pending) now counting 2
			:: ((pods[k].status != 1 && pods[k].status != 2) || pods[k].loc != i) -> goto fmpend;
			:: else->;
		fi;
		p = 0;

		// go through all the labels in constraints, and see if the pod matches all of them
		for (p : 0 .. podSpec.topoSpreadConstraints[j].numMatchedLabel - 1) {
			printf("[******] matching pod %d with {%d, %d}\n", k, p, podSpec.topoSpreadConstraints[j].labelKey[p])
			if 
			 	// TBDL Need to double check if the pods have extra keys than the matchlabel, will it be selected.
				::(pods[k].labelKeyValue[podSpec.topoSpreadConstraints[j].labelKey[p]] != podSpec.topoSpreadConstraints[j].labelValue[p]) -> goto fmpend;
				// ::(podTemplates[pods[k].podTemplateId].labelKeyValue[podSpec.topoSpreadConstraints[j].labelKey[p]] != podSpec.topoSpreadConstraints[j].labelValue[p]) -> goto fmpend;
				:: else->; 
			fi;
			printf("[******] matched pod %d with {%d, %d}\n", k, p, podSpec.topoSpreadConstraints[j].labelKey[p])
		}
		count++;
fmpend:	skip;
	}
}

// TODO: check if user did not set on enableNodeInclusionPolicyInPodTopologySpread
inline podTopologySpreadPreFilter(podSpec)
{
	i = 1;
	do
		:: i < NODE_NUM + 1 ->
			if 
				:: enableNodeInclusionPolicyInPodTopologySpread == 0 && nodes[i].curAffinity != 1 -> 
					goto stopo1;
				:: else->;
			fi;

			// This checks if ALL topology keys in spread Constraints are present in node labels. (not in docs but in their code)
			j = 0;
			do
				:: j < podSpec.numTopoSpreadConstraints ->
					if
						:: podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1 ->
							goto stopo2;
						:: else->;
					fi;

					if
						:: nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey] == -1 ->
							goto stopo1;
						:: else->;
					fi;
stopo2:				j++;
				:: else -> break;
			od;
			
			j = 0;
			do
				:: j < podSpec.numTopoSpreadConstraints ->
					if
						:: podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1 ->
							goto stopo5;
						:: else->;
					fi;
					// impl matchNodeInclusionPolicies in common.go
					if 
						:: (enableNodeInclusionPolicyInPodTopologySpread == 1) &&  ((podSpec.topoSpreadConstraints[j].nodeAffinityPolicy == 1 && nodes[i].curAffinity != 1) || (podSpec.topoSpreadConstraints[j].nodeTaintsPolicy == 1 && nodes[i].curTaint == 1)) ->
							goto stopo1;
						:: else->;
					fi;

					short count = 0;
					findMatchedPod(i, j, podSpec);
					printf("[****][SchedulerPlugins] Matched pod for {node %d, topologyKey %d} is %d\n", i, podSpec.topoSpreadConstraints[j].topologyKey, count)

					// We don't need the tpCountsByNodes as we can't do the calculation of nodes in parallel
					short key = podSpec.topoSpreadConstraints[j].topologyKey;

					if 
						:: count >= 0 && tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]] == -1 -> 
							tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]] = count;
						:: else ->
							tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]] = tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]] + count;
					fi;
					printf("[****][SchedulerPlugins] Matched pod for {%d, %d} is %d\n", key, nodes[i].labelKeyValue[key], count)
					count = 0;
					key = 0;
stopo5:				j++;
				:: else -> break;
			od;

// stopo1 means to skip the calculation of this node
stopo1: 	i++;
		:: else -> break;
	od;

	// by default, this is disabled.
	if 
		:: enableMinDomainsInPodTopologySpread -> 
			i = 0;
			for (i : 0 .. MAX_LABEL-1) {
				j = 0;
				for (j : 0 .. MAX_VALUE-1) {
					if 
						:: tpPairToMatchNum[i].a[j] != -1 ->
							tpKeyToDomainsNum[i] ++; 
						:: else->;
					fi;
				}
			}
		:: else->;
	fi;

	// calculate min match for each topology pair
	i = 0;
	for (i : 0 .. MAX_LABEL-1) {
		j = 0;
		short curMin = POD_NUM;
		for (j : 0 .. MAX_VALUE-1) {
			if 
				// simplify the "update" function. The update function can be called by updateWithPod, which we don't model. So the tpVal should always not exists. 
				// It essentially finding the min number (and second min number). 
				:: tpPairToMatchNum[i].a[j] != -1 ->
					if 
						:: tpPairToMatchNum[i].a[j] < curMin ->
							curMin = tpPairToMatchNum[i].a[j];
						:: else->;
					fi;
				:: else->;
			fi;
		}
		tpKeyToCriticalPaths[i] = curMin;
		curMin = 0;
	}
}

inline podTopologySpreadFilter(curPod, podSpec)
{
	i = 1;
	do
		:: i < NODE_NUM + 1 ->
			if 
				:: nodes[i].score == -1 ->
					goto stopo4;
				:: else->;
			fi;
			j = 0;
			for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
				if
					:: podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1 ->
						goto stopo6;
					:: else->;
				fi;

				short key = podSpec.topoSpreadConstraints[j].topologyKey;
				if 
					:: nodes[i].labelKeyValue[key] == -1 ->
						nodes[i].score = -1;
						goto stopo4;
					:: else->;
				fi;

				short minMatchNum = tpKeyToCriticalPaths[key];
				// printf("[******] minMatchNum %d key %d\n", minMatchNum, key)
				if
					:: tpKeyToDomainsNum[key] < podSpec.topoSpreadConstraints[j].minDomains ->
						minMatchNum = 0;
					:: else->;
				fi;
				// printf("[******] minMatchNum %d\n", minMatchNum, key)

				short selfMatchNum = 0;
				p = 0;
				bit flag = 0;
				for (p : 0 .. podSpec.topoSpreadConstraints[j].numMatchedLabel - 1) {
						if 
							:: (pods[curPod].labelKeyValue[podSpec.topoSpreadConstraints[j].labelKey[p]] != podSpec.topoSpreadConstraints[j].labelValue[p]) ->
						 // :: (podSpec.labelKeyValue[podSpec.topoSpreadConstraints[j].labelKey[p]] != podSpec.topoSpreadConstraints[j].labelValue[p]) ->
								flag = 1;
								break;
							:: else->;
						fi;
				}
				if 
					:: flag == 0->
						selfMatchNum = 1;
					:: else->;
				fi;

				printf("[****][SchedulerPlugins] PodTopoSpread: on node %d, total num %d, selfMatchNum %d, minMatchNum %d\n", i, tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]], selfMatchNum, minMatchNum)

				if 
					:: tpPairToMatchNum[key].a[nodes[i].labelKeyValue[key]] + selfMatchNum - minMatchNum >  podSpec.topoSpreadConstraints[j].maxSkew ->
						printf("[***][SchedulerPlugins] Node %d not passing topoSpreadConstraints %d\n", i, j)
						nodes[i].score = -1;
					:: else->;
				fi;
				selfMatchNum = 0;
				flag = 0;
				key = 0;
				selfMatchNum = 0;
				minMatchNum = 0;

stopo6:	 		skip;
			}	
stopo4:		i++;
		:: else->break;
	od;
}

// default constraints when no constraints specified: https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/#internal-default-constraints
// a few potential issue with their impl: 
// 1) if the  enableNodeInclusionPolicyInPodTopologySpread is false, they did not process the taint. 
// 2) when filtering nodes (calculate their pods count), the nodes need to contains all topoKeys in order to be counted, which can cause confusing problem.
inline podTopologySpreadFiltering(curPod, podSpec)
{
	/*----- preFilter ----*/
	twoDArray tpPairToMatchNum[MAX_LABEL];
	short tpKeyToDomainsNum[MAX_LABEL];
	short tpKeyToCriticalPaths[MAX_LABEL];

	i = 0;
	for (i : 0 .. MAX_LABEL-1) {
		j = 0;
		tpKeyToDomainsNum[i] = 0;
		for (j : 0 .. MAX_VALUE-1) {
			tpPairToMatchNum[i].a[j] = -1;
		}
	}

	podTopologySpreadPreFilter(podSpec);
	podTopologySpreadFilter(curPod, podSpec);

	printf("[***][SchedulerPlugins] Finished podTopologySpreadFiltering.\n")
	printfNodeScore();

	clearArray(tpKeyToDomainsNum, MAX_LABEL)
	clearArray(tpKeyToCriticalPaths, MAX_LABEL)
}



/*******************
Score plugins
*******************/
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

inline nodeAffinityScore(podSpec)
{
	j = 0;
	do
	:: j < podSpec.numRules ->
		if
		:: podSpec.affinityRules[j].isRequired == 0 ->
			k = 0;
			do
			:: k < podSpec.affinityRules[j].numMatchedNode ->
				if 
				:: nodes[podSpec.affinityRules[j].matchedNode[k]].score != -1 ->
					nodes[podSpec.affinityRules[j].matchedNode[k]].curScore = nodes[podSpec.affinityRules[j].matchedNode[k]].curScore + podSpec.affinityRules[j].weight;
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

	printf("[***][SchedulerPlugins] Finished nodeAffinityScore.\n")
	printfNodeScore();
}

// TODO: check if without taint defined, do they still have score?
inline taintTolerationScore(podSpec)
{
	j = 0;
	do
	:: j < podSpec.numPreferNoScheduleNode ->
		k = podSpec.preferNoScheduleNode[j];
		if 
		:: nodes[k].score != -1 ->
			nodes[k].curScore++;
		:: else->;
	  	fi;
	   j++;
	:: else -> break;
	od;

	defaultNormalizeScoreAndWeight(1, TAINT_WEIGHT);

	printf("[***][SchedulerPlugins] Finished taintTolerationScore.\n")
	printfNodeScore();
}


/*
	Note:
	1. we only model allowedPod, CPU and mem for now. 
	2. If no resource request was defined, then treat them as 0, meaning all nodes always fits. 
	   See more details in computePodResourceRequest: it leverage the Resource type defined in framework/types.go, 
	   where if requests is empty, the Resource.Add() can't assign value to the Resource, and it will remains 0 and directly return in fitsRequest().
	   In this case, we set cpuReqested, memRequested as 0 by default.

	3. default resource spec (weight), where both cpu and mem are weighted 1: https://github.com/kubernetes/kubernetes/blob/d436f5d0b7eb87f78eb31c12466e2591c24eef59/pkg/scheduler/apis/config/v1beta3/defaults.go#L31
	according to 
		- LeastAllocated impl: https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/least_allocated.go#L29
		- mostAllocated impl: https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/most_allocated.go#L30
*/
inline nodeResourcesFitFilter(podSpec)
{	
	i = 1;
	do 
	::	i < NODE_NUM+1 ->
		if
		::  (podSpec.cpuRequested > nodes[i].cpuLeft) || (podSpec.memRequested > nodes[i].memLeft) || (nodes[i].numPod + 1) > NODE_ALLOWED_POD_NUM -> 
			nodes[i].score = -1;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	printf("[***][SchedulerPlugins] Finished nodeResourcesFitFilter.\n")
	printfNodeScore();
}

inline nodeResourceFitScore(podSpec)
{
	i = 1;
	short cpuScore, memScore;
	do 
	::	i < NODE_NUM+1 ->
		if
		:: nodes[i].score != -1 ->
			if 
				:: STRATEGY_RESOURCE == 1 ->
					// printf("[******] %d %d %d %d\n", nodes[i].cpuLeft, podSpec.cpuRequested, nodes[i].memLeft, podSpec.memRequested);
					cpuScore = ((nodes[i].cpuLeft - podSpec.cpuRequested) * MAX_NODE_SCORE / nodes[i].cpuLeft) * 1;
					memScore = ((nodes[i].memLeft - podSpec.memRequested) * MAX_NODE_SCORE / nodes[i].memLeft) * 1;
					// printf("[******] !!!! %d %d %d\n", cpuScore, memScore, nodes[i].cpuLeft - podSpec.cpuRequested);
					nodes[i].score = nodes[i].score + ((cpuScore * 1 + memScore * 1) * NODE_RESOURCE_FIT / 2 )
					// printf("[******] %d, %d\n", i, nodes[i].score);
				:: STRATEGY_RESOURCE == 2 ->
					cpuScore = ((podSpec.cpuRequested) * MAX_NODE_SCORE / nodes[i].cpuLeft) * 1;
					memScore = ((podSpec.memRequested) * MAX_NODE_SCORE / nodes[i].memLeft) * 1;
					nodes[i].score = nodes[i].score + ((cpuScore * 1 + memScore * 1) * NODE_RESOURCE_FIT / 2 )
				:: else -> 
					printf("[*Warning][SchedulerPlugins] No/Wrong scheduling strategy defined!\n");
					assert(false);
			fi;
		:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	printf("[***][SchedulerPlugins] Finished nodeResourceFitScore.\n")
	printfNodeScore();

	cpuScore = 0;
	memScore = 0;
}

inline podTopologySpreadPreScore(podSpec)
{
	// original is requireAllTopologies := len(pod.Spec.TopologySpreadConstraints) > 0 || !pl.systemDefaulted, in scoring.go
	// However, we have filled in the system default in pre-processing, so we check on a varibale passed by the pre-processor and see if user has defined any constraints. 
	bit requireAllTopologies = userDefinedConstraints;

	// The initPreScoreState function
	//// building default config has been done by the model generator
	i = 1;
	for (i : 1 .. NODE_NUM) {
		// in this iteration, they iterate only on filtered node
		if 
			:: nodes[i].score == -1 -> goto ptsp1;
			:: else->;
		fi;

		j = 0;
		for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
			if 
				:: (requireAllTopologies == 1) && (podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1) && (nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey] == -1) -> 
					ignoredNode[i] = 1; 
					goto ptsp1;
				:: else->;
			fi;
		}

		// In source code, they process hostname seperately. We don't do it as it does not make difference on logic
		// In summary, only the pods on top of filtered node + nodes match with all topoKey (exclude default constraints) will be counted. 
		j = 0;
		for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
			short curValue = nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey];
			// count how many distinct domains for each topoKey
			if 
				:: curValue == -1 -> goto ptsp2;
				:: else->;
			fi;
			if 
				:: (topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] == -1) && (podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1) -> 
					topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] = 0; 
					topoSize[podSpec.topoSpreadConstraints[j].topologyKey]++;
				:: else->;
			fi;
			curValue = 0;
ptsp2:		skip;
		}
ptsp1:	skip;			
	}
	// They weight each constraint based on how many distinct domains in the topoKey. 
	j = 0;
	for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
		// topologyNormalizingWeight: math.Log(float64(size + 2)), since Spin does not support log, we pre-populate the table for log
		logTable(topoSize[podSpec.topoSpreadConstraints[j].topologyKey] + 2, topologyNormalizingWeight[j]);
	}

	// Process the pod count for each domain by going through the nodes
	i = 1;
	for (i : 1 .. NODE_NUM) {
		// in this iteration, they iterate on all nodes
		if 
			:: enableNodeInclusionPolicyInPodTopologySpread == 0 && nodes[i].curAffinity != 1 -> goto ptsp3;
			:: else->;
		fi;

		j = 0;
		for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
			if
				:: ((requireAllTopologies == 1) && (podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 1) && (nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey] == -1)) -> 
					goto ptsp3;
				:: else->;
			fi;
		}
		
		j = 0;
		for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
			short curValue = nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey];
			if 
			 	:: (podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 0) || (curValue == -1)->
				 goto ptsp4;
			 	:: else->;
			fi;
			if 
				:: (enableNodeInclusionPolicyInPodTopologySpread == 1 && nodes[i].curAffinity != 1) || (topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] == -1) -> 
				 goto ptsp4;
				:: else->;
			fi;

			// We count all the pods, including terminating pods, as we don't model the terminating state for now. 
			short count = 0;
			findMatchedPod(i, j, podSpec);
			printf("[*****][SchedulerPlugins] Matched pod for {node %d, topologyKey %d} is %d\n", i, podSpec.topoSpreadConstraints[j].topologyKey, count)
			topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] = topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] + count;
			count = 0;
			curValue = 0;
ptsp4: 		skip;
		}
ptsp3:	skip;
	}
}

// Note: minDomains is not used in soft constraints acoording to the docs: 
// You can only specify minDomains in conjunction with whenUnsatisfiable: DoNotSchedule.
inline podTopologySpreadScore(podSpec)
{
	i = 1;
	for (i : 1 .. NODE_NUM) {
		if 
			:: (ignoredNode[i] == 1) || (nodes[i].score == -1) -> goto ptss1;
			:: else->;
		fi;

		j = 0;
		for (j : 0 .. podSpec.numTopoSpreadConstraints-1) {
			if 
				:: podSpec.topoSpreadConstraints[j].whenUnsatisfiable == 0 -> goto ptss2;
				:: else->;
			fi;
			// TODO: they didn't check on cur affinity for this node, may cause problem... May be because they have already filter those node out?

			// scoreForCount(cnt int64, maxSkew int32, tpWeight float64): float64(cnt)*tpWeight + float64(maxSkew-1),
			// which means that, if a topo has more domains, the more the matched pods, the more the scores
			short curValue = nodes[i].labelKeyValue[podSpec.topoSpreadConstraints[j].topologyKey];
			// [estimate] they did a round on the score, while we are all floored. 
			printf("[******][SchedulerPlugins] topoKey %d, curValue %d\n", podSpec.topoSpreadConstraints[j].topologyKey, curValue)
			if
				:: curValue != -1 ->
			nodes[i].curScore = nodes[i].curScore + topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue] * topologyNormalizingWeight[j] + (podSpec.topoSpreadConstraints[j].maxSkew - 1)
			printf("[******][SchedulerPlugins] Current Constraints on key %d. Node %d, curScore %d.\n", podSpec.topoSpreadConstraints[j].topologyKey, i, nodes[i].curScore)
			printf("[******][SchedulerPlugins] TopopairToCount %d, weight %d, maxSkew %d \n", topologyPairToPodCounts[podSpec.topoSpreadConstraints[j].topologyKey].a[curValue], topologyNormalizingWeight[j], podSpec.topoSpreadConstraints[j].maxSkew)
				:: else->;
			fi;
			curValue = 0;
ptss2:		skip;
		}
ptss1:  skip;
	} 
}

inline podTopologySpreadNormalizeScore()
{
	short minScore = MAX_NODE_SCORE;
	short maxScore = -1;

	i = 1;
	for (i : 1 .. NODE_NUM) {
		if 
			:: (nodes[i].score == -1) || (ignoredNode[i] == 1) ->
				nodes[i].curScore = -1; 
				goto ptsns1 ;
			:: else->;
		fi;
		minScore = (nodes[i].score != -1 && nodes[i].curScore < minScore ->  nodes[i].curScore : minScore)
		maxScore = (nodes[i].score != -1 && nodes[i].curScore > maxScore ->  nodes[i].curScore : maxScore)

ptsns1: skip;
	}

	for (i : 1 .. NODE_NUM) {
		if
			:: nodes[i].score == -1 || nodes[i].curScore == -1 -> 
				goto ptsns2;
			:: else->;
		fi;
		if 
			:: maxScore == 0 ->
				nodes[i].curScore = MAX_NODE_SCORE;
				nodes[i].score = nodes[i].score + NODE_PODTOPO_SPREAD_WEIGHT*nodes[i].curScore
			:: else->
				nodes[i].score = nodes[i].score + NODE_PODTOPO_SPREAD_WEIGHT*(MAX_NODE_SCORE * (maxScore + minScore - nodes[i].curScore) / maxScore)
		fi;
ptsns2: nodes[i].curScore = 0;
	}

	minScore = 0;
	maxScore = 0;
}

inline podTopologySpreadScoring(podSpec)
{
	twoDArray topologyPairToPodCounts[MAX_LABEL];
	short topoSize[MAX_LABEL];
	short topologyNormalizingWeight[MAX_LABEL]
	short ignoredNode[NODE_NUM+1];

	i = 0;
	for (i : 0 .. MAX_LABEL-1) {
		j = 0;
		for (j : 0 .. MAX_VALUE-1) {
			topologyPairToPodCounts[i].a[j] = -1;
		}
	}

	podTopologySpreadPreScore(podSpec);
	podTopologySpreadScore(podSpec);
	podTopologySpreadNormalizeScore();

	printf("[***][SchedulerPlugins] Finished podTopologySpreadScoring.\n")
	printfNodeScore();

	clearArray(ignoredNode, NODE_NUM+1)
	clearArray(topologyNormalizingWeight, MAX_LABEL)
	clearArray(topoSize, MAX_LABEL)
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
// https://github.com/kubernetes/kubernetes/blob/419e0ec3d2512afd8c1f35a44862f856bc4ac10f/pkg/scheduler/framework/plugins/noderesources/balanced_allocation.go
inline nodeResourcesBalancedAllocation()
{
	
}
*/