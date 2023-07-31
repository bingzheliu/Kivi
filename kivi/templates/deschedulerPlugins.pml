
/*
	1. Plugins are executed in the same order as they appear in the configuration
		 see: https://docs.google.com/document/d/1tWpXoZ6YF3ksnmueM2POwASdxoiLW8y7TXuWFxT8NSo/edit#heading=h.ec817eouurjs 
	2. They only consider the ready nodes.  
*/


// There are eviction plugins (besides the eviction itself), which defines the default prefilter/filter, and will be initilized in each New() in each plugin, 
// wrapped by WrapFilterFuncs that essentially just go through filter one-by-one (filter are ANDed), and then called when run ListPodsOnANode in plugin, 
// where the actual caller func impl is in BuildGetPodsAssignedToNodeFunc.

/*
	They filter according to the following:
	1. In ListPodsOnANode, Scceeded and failed pods are not considered because they don't occupy any resource. So pending is considered. 
	2. default Filter plugin: 
		a. HaveEvictAnnotation, directly incldue the pod without checking others.
		b. DaemonSet, mirror, static, and terminating pods are excluded. 
		c. Check on some default constraints, including the following:
			1) EvictFailedBarePods, true will evict the pods without owner, default is false.
			2) EvictSystemCriticalPods, true will evict system critical pods, default is false.
				can further set the PriorityThreshold for defining the "criticial", default is not set, omitting now. 
			3) EvictLocalStoragePods, default false
			4) IgnorePvcPods, default false
			5) LabelSelector, if set, the unmatched pod will be excluded, default null.
			More details in plugins/defaultevictor/defaults.go and https://github.com/kubernetes-sigs/descheduler#evictor-plugin-configuration-default-evictor 
			Note that these args are configed per profile. 
	3. In preEvictionFilter, if defaultEvictorArgs.NodeFit is ture, it essentially checks if each pod can be able to fit with any other nodes 

	They have a WrapFilterFuncs to put all the above func together (In particular, in New() of the plugin). We combine all the above into filter(). 
*/
// filter the pod j on node i.
inline filter(i, j)
{
	// For 1 and 2.b, we now only modeled terminating pod, and hence only check on pod status.
	if 
		:: pods[j].loc != i || pods[j].status == 0 || pods[j].status == 3 ->
			flag = 0;
			goto DF1;
		:: else->;
	fi;
	// For 2.a, skipping for now.

	// For 2.c, only model 2), but can easily append them here later. 
	if 
		:: pods[j].critical && deschedulerProfiles[ii].evictSystemCriticalPods == 0 ->
			flag = 0;
			goto DF1;
		:: else->;
	fi;
	// for 3, the defaultEvictorArgs.NodeFit default is false. Omtting for now.

DF1: skip
}

// Evictor is used across all the plugins in all the profiles. It is defined under descheduler/evictions
inline evictPod(k)
{
	// check maxPodsToEvictPerNode and maxPodsToEvictPerNamespace(Omitting for now)
	if 
		:: (nodePodCount[pods[k].loc] + 1 > maxNoOfPodsToEvictPerNode) || (namespacePodCount[pods[k].namespace] + 1 > maxNoOfPodsToEvictPerNamespace) ->
			printf("[**][Descheduler] Exceeded maxNoOfPodsToEvictPerNode or maxNoOfPodsToEvictPerNamespace for pod %d\n", k)
			flag = 1
		:: else ->
			printf("[*][Descheduler] Duplicated pod %d (status %d) on node %d, pending for deletion!\n", k, pods[k].status, pods[k].loc)
			// call into kubernetes client to evict the pod. We use the same way that deployment evict the pods. 
			d[pods[k].workloadId].replicasInDeletion ++;
			pods[k].status = 3;
			updateQueue(kblQueue, kblTail, kblIndex, k, MAX_KUBELET_QUEUE)

			nodePodCount[pods[k].loc] ++
			namespacePodCount[pods[k].namespace] ++
	fi;
}

// inline removePodsViolatingNodeAffinity()
// {

// }

// find out how many nodes can fit with the pods in deployment i
// The originial code in getTargetNodes look through the nodes via pods. Here, we assume the pods that are managed by the same workloads are identical. 

inline examTargetNodes(q)
{
	short m = 0, n = 0, matchingNodes = 0;
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
		flag = 1;
		bit matched = 0;
		for (n : 0 .. podTemplates[d[q].podTemplateId].numRules - 1) {
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
		matchingNodes ++
DRMD2:	skip;
	}
	// Only when matchingNodes > 1, the targetNodes will increase. 
	if 
		:: matchingNodes > 1 ->
			targetNodes = matchingNodes
		:: else->
	fi;

	printf("[****][DeScheduler] Number of target nodes for deployment %d is %d\n", q, targetNodes)
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

	short ownerKeyOccurence[DEP_NUM+1];
	deschedulerMatchingArray duplicatePods[DEP_NUM+1];
	bit flag = 0;
	for (i : 0 .. DEP_NUM ) {
		ownerKeyOccurence[i] = 0
		duplicatePods[i].exist = 0
		for (j : 0 .. NODE_NUM ) {
			duplicatePods[i].nodePods[j].numPods = 0
			for (k : 0 .. POD_NUM ) {
				duplicatePods[i].nodePods[j].pods[k] = 0
			}
		}
	}

	for (i : 1 .. NODE_NUM ) {
		if 
			// Only look into Ready node
			:: nodes[i].status != 1 ->
				goto DRMD1;
			:: else->;
		fi;

		// We now assume there's only one type of workload, the deployment. Otherwise need to consider to have a unique key for each workload, and use that key here. 
		bit duplicateKeysMap[DEP_NUM+1];
		for (j : 1 .. DEP_NUM) {
			duplicateKeysMap[j] = 0
		}

		for (j : 1 .. POD_NUM) {
			flag = 1;
			filter(i, j)
			if 
				:: flag == 1 ->
					ownerKeyOccurence[pods[j].workloadId] = ownerKeyOccurence[pods[j].workloadId] + 1;
					if 
						:: duplicateKeysMap[pods[j].workloadId] == 1 ->
							duplicatePods[pods[j].workloadId].nodePods[i].pods[j] = 1
							duplicatePods[pods[j].workloadId].exist = 1
							duplicatePods[pods[j].workloadId].nodePods[i].numPods ++
						:: else ->
							duplicateKeysMap[pods[j].workloadId] = 1;
					fi;
				:: else->;
			fi;
		}
DRMD1:	skip;
	}
	// short kk = 0
	// for (i : 0 .. DEP_NUM ) {
	// 	for (j : 0 .. NODE_NUM ) {
	// 		for (kk : 0 .. POD_NUM ) {
	// 			printf("%d %d %d: %d, %d\n", i, j, kk, duplicatePods[i].nodePods[j].numPods, duplicatePods[i].nodePods[j].pods[kk])
	// 		}
	// 	}
	// }

	for (i : 1 .. DEP_NUM) {
		if 
			:: duplicatePods[i].exist == 1 ->
				short targetNodes = 0;
				examTargetNodes(i)
				if 
					:: targetNodes < 2 -> 
						printf("[**][DeScheduler] Less than two feasible nodes for duplicates to land, skipping eviction\n")
					:: else ->
						short upperAvg;
						// estimate: this should be ceil, we overestimate, to make it floor, and hence it's possible that the pods get evicted in our model, but not in the system
						// upperAvg := int(math.Ceil(float64(ownerKeyOccurence[ownerKey]) / float64(len(targetNodes))))
						upperAvg = ownerKeyOccurence[i] / targetNodes 
						for (j : 1 .. NODE_NUM ) {
							if
								// only proceed if if len(pods)+1 > upperAvg
								:: (duplicatePods[i].nodePods[j].numPods > 0) && ((duplicatePods[i].nodePods[j].numPods + 1) > upperAvg ) ->
									short count = 0;
									for (k : 1 .. POD_NUM) {
										if 
											// Only evict pod[upperAvg-1:], meaning only evict total - (upperAvg - 1) pods.
											:: count < duplicatePods[i].nodePods[j].numPods - (upperAvg - 1) ->
												// printf("node%d: %d, %d\n", j, count, duplicatePods[i].nodePods[j].numPods - (upperAvg - 1))
												if 
													:: duplicatePods[i].nodePods[j].pods[k] == 1 ->
														flag = 0
														// Imp in evictions/evictions.go/EvictPod
														evictPod(k)
														// if NodeLimitExceeded is true, should change to another node. 
														if
															:: flag == 1 ->
																goto DRMD3;
															:: else->;
														fi;
														count ++;
													:: else->;
												fi;
											:: else->
												break;
										fi;
									}
								:: else->;
							fi;
DRMD3:						skip;
						}
				fi;
			:: else->;
		fi;
	}

	printf("[***][DeScheduler] removeDuplicates plugins finished!")
}

// inline removePodsViolatingTopologySpreadConstraint()
// {	
	
// }

// inline defaultEvictor()
// {

// }