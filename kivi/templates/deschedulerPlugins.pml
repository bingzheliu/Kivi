
/*
	1. Plugins are executed in the same order as they appear in the configuration
		 see: https://docs.google.com/document/d/1tWpXoZ6YF3ksnmueM2POwASdxoiLW8y7TXuWFxT8NSo/edit#heading=h.ec817eouurjs 
	2. They only consider the ready nodes.  
*/

inline evict()
{
	
}

inline removePodsViolatingNodeAffinity()
{

}

// find out how many nodes can fit with the pods in deployment i
// The originial code in getTargetNodes look through the nodes via pods. Here, we assume the pods that are managed by the same workloads are identical. 

inline examTargetNodes(q)
{
	short m = 0, n = 0, k = 0, matchingNodes = 0;
	for (m : 1 .. NODE_NUM) {
		if 
			// Only look into ready nodes
			:: nodes[m].status != 1 ->
				goto DRMD2;
			:: else->;
		fi;

		// First check tolerence
		// Only skip TaintEffectNoSchedule and TaintEffectNoExecute
		for (n : 0 .. podTemplates[d[q].podTemplateId].numNoScheduleNode - 1)
		{
			if 
				:: podTemplates[d[q].podTemplateId].noScheduleNode[j] == m -> 
					goto DRMD2;
				:: else->;
			fi;
		}

		// check on node selector and affinity
		// If node selector is defined, then it should equal to the current node. 
		if 
			:: podTemplates[d[q].podTemplateId].nodeName != 0 && podTemplates[d[q].podTemplateId].nodeName != nodes[m].name ->
				goto DRMD2;
			:: else->;
		fi;

		// If affinity is defined, then find it node satisfy requiredDuringSchedulingIgnoredDuringExecution
		// This check called component-helpers/scheduling. However, the scheduling affinity plugin used a differnt code block, which is impl within the plugin -- they should use the same function, to be consistent. 
		// After checking the below code, it looks the same logic as the scheduler affinity code. May be better to do another check.  
		// Code: https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/component-helpers/scheduling/corev1/helpers.go#L39
		// The matching code: https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/component-helpers/scheduling/corev1/nodeaffinity/nodeaffinity.go#L84
		// Because looks like they are the same as scheduler, I am just using the same logic for now. 
		bit flag = 1;
		bit matched = 0;
		for (n : 0 .. podSpec.numRules - 1) {
			if
				:: podTemplates[d[q].podTemplateId].affinityRules[n].isRequired == 1 ->
					flag = 0;
					for (k : 0 .. podTemplates[d[q].podTemplateId].affinityRules[n].numMatchedNode - 1) {
						if 
							:: podTemplates[d[q].podTemplateId].affinityRules[n].matchedNode[k] == m ->
								matched = 1;
							:: else->;
						fi;
					}
				:: else->;
			fi;
		}
		if 
			:: flag == 0 && matched == 0->
				goto DRMD2;
			:: else->;
		fi;
		matchingNodes += 1
DRMD2:	skip;
	}
	// Only when matchingNodes > 1, the targetNodes will increase. 
	if 
		:: matchingNodes > 1 ->
			targetNodes = matchingNodes
		:: else->
	fi;

	printf("[****][DeScheduler] Target nodes for deployment %d is %d\n", q, targetNodes)
	m = 0;
	n = 0;
	k = 0;
	matchingNodes = 0;
}

inline removeDuplicates()
{
	/*
		Note:
		1. About duplicate pods. They count for duplicate pods if their ownerkey (namespace, owner/kind, owner/name, image) is the same. And they also check if a pod have multiple owner. 
		   How we model: as now one pod only belong to one owner, and we don't model image, so wen only compare the rest three. In addition, we assume the namespace will be identical for the pod and its owner. So we only compare the owner to simplify it.  
		2. The order of the pod that are listed matter. First, only the second time that saw a duplicate pods, these pods will be put into the duplicate record, not the first one.
		   Second, which pods got evicted also depends on this. But now we treat these pod equally, and hence we don't quite look into the orders for now.
		3. There should be other ways to impl this plugins, e.g., go through the owner instead of nodes, which should get an equavilence result. But to be more accurate, we try to model it the same way.
		   However, this can be heavier than other impl. In the future, one can provide choice to choose between the two implementation, having the trade-off between accuracy and performance.
	*/

	short ownerKeyOccurence[DEP_NUM];
	deschedulerMatchingArray duplicatePods;

	for (i : 1 .. NODE_NUM ) {
		if 
			// Only look into Ready node
			:: nodes[i].status != 1 ->
				goto DRMD1;
			:: else->;
		fi;

		// We now assume there's only one type of workload, the deployment. Otherwise need to consider to have a unique key for each workload, and use that key here. 
		bit duplicateKeysMap[DEP_NUM];

		for (j : 1 .. POD_NUM) {
			if 
				// According to podUtil.ListPodsOnANode, succeeded and failed pods are not considered because they don't occupy any resource. So pending is considered. 
				:: pods[j].loc == i && pods[j].status != 0 ->
					ownerKeyOccurence[pods[j].workloadId] = ownerKeyOccurence[pods[j].workloadId] + 1;
					if 
						:: duplicateKeysMap[pods[j].workloadId] == 1 ->
							duplicatePods[pods[j].workloadId].nodePods[i].pods[j] = 1
							duplicatePods[pods[j].workloadId].exist = 1
							duplicatePods[pods[j].workloadId].nodePods[i].numPods += 1 
						:: else ->
							duplicateKeysMap[pods[j].workloadId] = 1;
				:: else->;
			fi;
		}
DRMD1:	skip;
	}

	for (i : 1 .. DEP_NUM) {
		if 
			:: duplicatePods[i].exist == 1 ->
				short targetNodes = 0;
				examTargetNodes(i)
				if 
					:: targetNodes < 2 -> 
						printf("[**][DeScheduler] Less than two feasible nodes for duplicates to land, skipping eviction\n")
					:: else ->
						for (j : 1 .. NODE_NUM ) {
							if
								// estimate: this should be ceil, so we just add 1; meaning if it's exact equal to N, then it would become N+1
								// upperAvg := int(math.Ceil(float64(ownerKeyOccurence[ownerKey]) / float64(len(targetNodes))))
								// only proceed if if len(pods)+1 > upperAvg
								:: (duplicatePods[i].nodePods[j].numPods > 0) && ((duplicatePods[i].nodePods[j].numPods + 1) > (ownerKeyOccurence[i] / targetNodes + 1)) ->
									short k = 0, count = 0;
									for (k : 1 .. POD_NUM) {
										if 
											// Only evict pod[upperAvg-1:], meaning only evict total - (upperAvg - 1) pods.
											:: count < duplicatePods[i].nodePods[j].numPods - (ownerKeyOccurence[i] / targetNodes) ->
												if 
													:: duplicatePods[i].nodePods[j].pods[k] == 1 ->
														evict(k)
														count += 1;
													:: else->;
												fi;
											:: else->
												break;
										fi;
									}
								:: else->;
							fi;
						}
				fi;
			:: else->;
		fi;
	}

	printf("[***][DeScheduler] removeDuplicates plugins finished!")
}

inline removePodsViolatingTopologySpreadConstraint()
{	
	
}

inline defaultEvictor()
{

}