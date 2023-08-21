
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

	They have a WrapFilterFuncs to put some above func together (In particular, in New() of the plugin), where each plugin process it differently.
	We combined listPodsOnANode and filter.
*/
// filter the pod q
inline filter(q)
{
	// For 1 and 2.b, we now only modeled terminating pod, and hence only check on pod status.
	if 
		:: pods[q].status == 0 || pods[q].status == 3 ->
			flag = 0;
			goto DF1;
		:: else->;
	fi;
	// For 2.a, skipping for now.

	// For 2.c, only model 2), but can easily append them here later. 
	if 
		:: pods[q].critical && deschedulerProfiles[ii].evictSystemCriticalPods == 0 ->
			flag = 0;
			goto DF1;
		:: else->;
	fi;

DF1: skip
}

inline preEvictionFilter(q)
{
	// for 3, the defaultEvictorArgs.NodeFit default is false. Omtting for now.
	skip
}

// Evictor is used across all the plugins in all the profiles. It is defined under descheduler/evictions
inline evictPod(q)
{
	// check maxPodsToEvictPerNode and maxPodsToEvictPerNamespace(Omitting for now)
	if 
		:: (nodePodCount[pods[q].loc] + 1 > maxNoOfPodsToEvictPerNode) || (namespacePodCount[pods[q].namespace] + 1 > maxNoOfPodsToEvictPerNamespace) ->
			printf("[**][Descheduler] Exceeded maxNoOfPodsToEvictPerNode or maxNoOfPodsToEvictPerNamespace for pod %d\n", q)
			flag = 1
		:: else ->
			printf("[*][Descheduler] Pod %d (status %d) on node %d pending for deletion!\n", q, pods[q].status, pods[q].loc)
			// call into kubernetes client to evict the pod. We use the same way that deployment evict the pods. 
			d[pods[q].workloadId].replicasInDeletion ++;
			pods[q].status = 3;
			updateQueue(kblQueue, kblTail, kblIndex, q, MAX_KUBELET_QUEUE)

			nodePodCount[pods[q].loc] ++
			namespacePodCount[pods[q].namespace] ++
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
		matched = 0;
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
	deschedulerNodeDuplicateArray duplicatePods[DEP_NUM+1];
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
			// This plugin combine the below two togethor
			filter(j)
			preEvictionFilter(j)
			if 
				:: pods[j].loc == i && flag == 1 ->
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
						// upperAvg := int(math.Ceil(float64(ownerKeyOccurence[ownerKey]) / float64(len(targetNodes))))
						// estimate: this should be ceil, we approximate it by add 0.99 to the equation 
						// upperAvg = (100*ownerKeyOccurence[i]+99*targetNodes) / (targetNodes*100)
						// preciese: ceil(upperAvg, ownerKeyOccurence[i], targetNodes) -> test if it can be divided otherwise just add 1
						upperAvg = 0
						ceil(upperAvg, ownerKeyOccurence[i], targetNodes)
						// upperAvg = (2*ownerKeyOccurence[i]+targetNodes) / (targetNodes*2)
						// printf("[*]%d %d %d\n", upperAvg, ownerKeyOccurence[i], targetNodes)
						for (j : 1 .. NODE_NUM ) {
							if
								// only proceed if if len(pods)+1 > upperAvg
								:: (duplicatePods[i].nodePods[j].numPods > 0) && ((duplicatePods[i].nodePods[j].numPods + 1) > upperAvg ) ->
									count = 0;
									for (k : 1 .. POD_NUM) {
										if 
											// Only evict pod[upperAvg-1:], meaning only evict total - (upperAvg - 1) pods.
											:: count < duplicatePods[i].nodePods[j].numPods - (upperAvg - 1) ->
												// printf("node%d: %d, %d\n", j, count, duplicatePods[i].nodePods[j].numPods - (upperAvg - 1))
												if 
													:: duplicatePods[i].nodePods[j].pods[k] == 1 ->
														printf("[*][Descheduler] Duplicated Pod %d (status %d) on node %d pending for deletion!\n", k, pods[k].status, pods[k].loc)
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
		targetNodes = 0
		upperAvg = 0
	}

	// Clear local variables
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
	printf("[***][DeScheduler] removeDuplicates plugins finished!\n")

}

inline topologyIsBalanced()
{
	short minDomainSize = POD_NUM
	short maxDomainSize = 0

	for (k : 0 .. MAX_VALUE-1) {
		if	
			:: topologyValueToPods[k].exist == 1->
				minDomainSize = (topologyValueToPods[k].numPods < minDomainSize -> topologyValueToPods[k].numPods : minDomainSize)
				maxDomainSize = (topologyValueToPods[k].numPods > maxDomainSize -> topologyValueToPods[k].numPods : maxDomainSize)
				// printf("[*]%d %d %d %d %d %d\n", k, topologyValueToPods[k].numPods, podTemplates[i].topoSpreadConstraints[j].maxSkew, minDomainSize, maxDomainSize, j)
				if 
					:: maxDomainSize - minDomainSize > podTemplates[i].topoSpreadConstraints[j].maxSkew->
						flag = 0
						break
					:: else->
				fi;
			:: else->;
		fi;
	}
	minDomainSize = 0
	maxDomainSize = 0
}

inline sortDomains(sortedDomains)
{
	deschedulerTopoSortArray temp;
	for (k : 0 .. sumValues-1) {
		for (p : 0 .. sumValues-k-2) {
			if 
				:: sortedDomains[p].numPods > sortedDomains[p+1].numPods->
					temp.index = sortedDomains[p].index
					temp.numPods = sortedDomains[p].numPods
					sortedDomains[p].index = sortedDomains[p+1].index
					sortedDomains[p].numPods = sortedDomains[p+1].numPods
					sortedDomains[p+1].index = temp.index
					sortedDomains[p+1].numPods = temp.numPods
				:: else->
			fi;
		}
	}
}

inline balanceDomains(constraint)
{
	short idealAvgFloor, idealAvgCeil;
	// This again can be more aggressive to evict, overestimation.
	idealAvgFloor = sumPods / sumValues
	idealAvgCeil = 0
	ceil(idealAvgCeil, sumPods, sumValues)
	// Omitting --> they did the filter again here. TBD: double check and see if this can make any difference.

	// TBD: think about if there's potential estimation
	// Only consider to sort the domain according to number of pods, not considering the pod priority etc.
	p = 0
	for (k : 0 .. MAX_VALUE-1) {
		if 
			:: topologyValueToPods[k].exist == 1 ->
				sortedDomains[p].numPods = topologyValueToPods[k].numPods
				sortedDomains[p].index = k
				sortedDomains[p].evictedNumPods = 0
				p++
			:: else->
		fi
	}
	// for (k : 0 .. sumValues-1) {
	// 	printf("[*]%d %d %d %d!!\n", k, sortedDomains[k].numPods, sortedDomains[k].index, sortedDomains[p].evictedNumPods)
	// }
	// printf("[*]%d---------\n", idealAvg)
	sortDomains(sortedDomains)

	k = 0
	p = sumValues-1
	do 
		:: k < p->
			p = ((sortedDomains[p].numPods <= idealAvgCeil) -> p-1 : p)
			if 
				:: sortedDomains[p].numPods - sortedDomains[k].numPods <= constraint.maxSkew ->
					k++ 
					goto DRPVT1
				:: else->
			fi;
			short cur_min = POD_NUM

			// aboveAvg := math.Ceil(float64(len(sortedDomains[j].pods)) - idealAvg)
			// belowAvg := math.Ceil(idealAvg - float64(len(sortedDomains[i].pods)))
			// smallestDiff := math.Min(aboveAvg, belowAvg)
			min(cur_min, sortedDomains[p].numPods - idealAvgFloor, idealAvgCeil - sortedDomains[k].numPods)
			// overestimate: it's math.Ceil((skew - float64(constraint.MaxSkew)) / 2). We added 0.99
			short _ceil_a = 0
			ceil(_ceil_a, sortedDomains[p].numPods - sortedDomains[k].numPods-constraint.maxSkew, 2)
			// printf("[*]%d %d %d\n", _ceil_a, sortedDomains[p].numPods - sortedDomains[k].numPods-constraint.maxSkew, 2)
			min(cur_min, cur_min, _ceil_a)
			printf("%d %d %d %d\n", k, p, cur_min, idealAvgFloor, idealAvgCeil)
			if 
				:: cur_min <= 0 ->
					k++
					goto DRPVT1
				:: else->
			fi;
			_ceil_a = 0

			printf("[***][DeScheduler] For constraint with topologyKey %d, domain %d should evict %d pods (so domain %d can potentially add %d pods)\n", constraint.topologyKey, sortedDomains[p].index, cur_min, sortedDomains[k].index, cur_min)

			sortedDomains[p].evictedNumPods = sortedDomains[p].evictedNumPods + cur_min
			// Omitting topologyBalanceNodeFit for now. Hence omitting filterNodesBelowIdealAvg.

			sortedDomains[p].numPods = sortedDomains[p].numPods - cur_min
			sortedDomains[k].numPods = sortedDomains[k].numPods + cur_min

DRPVT1:		skip
		:: else->
			break
	od;

	cur_min = 0
	idealAvgCeil = 0
	idealAvgFloor = 0
	_ceil_a = 0
}

inline removePodsViolatingTopologySpreadConstraint()
{	
	// Omitting namepsace -- the seperation of namespaces may be done at verifier, which we can deal with them later togethor.
	bit podsForEviction[POD_NUM+1];
	for (i : 1 .. POD_NUM) {
		podsForEviction[i] = 0;
	}

	for (i : 1 .. POD_TEMPLATE_NUM ) {
		for (j : 0 .. podTemplates[i].numTopoSpreadConstraints - 1) {
			podsArray topologyValueToPods[MAX_VALUE];
			for (k : 0 .. MAX_VALUE-1) {
				topologyValueToPods[k].exist = 0
				topologyValueToPods[k].numPods = 0
				for ( p : 0 .. POD_NUM ) {
					topologyValueToPods[k].pods[p] = 0
				}
			}

			if 
				// need to match with the configured descheduler constraints.
				:: deschedulerProfiles[ii].constraintsTopologySpread == 2 || deschedulerProfiles[ii].constraintsTopologySpread == podTemplates[i].topoSpreadConstraints[j].whenUnsatisfiable->
					short sumPods = 0, sumValues = 0
					sumPods = 0;
					sumValues = 0;
					for (k : 1 .. NODE_NUM) {
						if 
							::nodes[k].status == 1 && nodes[k].labelKeyValue[podTemplates[i].topoSpreadConstraints[j].topologyKey] != -1 ->
								sumValues = (topologyValueToPods[nodes[k].labelKeyValue[podTemplates[i].topoSpreadConstraints[j].topologyKey]].exist == 0 -> sumValues + 1 : sumValues)
								topologyValueToPods[nodes[k].labelKeyValue[podTemplates[i].topoSpreadConstraints[j].topologyKey]].exist = 1
								
							:: else ->
						fi;
					}

					for (k : 1 .. POD_NUM) {
						flag = 1;
						// TBD: not sure if the pending pods (which has been scheduled by scheduler, yet not created) should be counted. Let's count it for now, which is the same as scheduler, but they may be different.
						filter(k)
						if 
							:: flag == 1 && pods[k].loc != 0 && nodes[pods[k].loc].status == 1 ->
								flag = 0
								for (p : 0 .. podTemplates[i].topoSpreadConstraints[j].numMatchedLabel - 1) {
									if 
										:: (pods[k].labelKeyValue[podTemplates[i].topoSpreadConstraints[j].labelKey[p]] != podTemplates[i].topoSpreadConstraints[j].labelValue[p]) ->
											flag = 1;
											break;
										:: else->;
									fi;
								}
								if 
									:: flag == 0 ->
										short curVal = nodes[pods[k].loc].labelKeyValue[podTemplates[i].topoSpreadConstraints[j].topologyKey] 
										topologyValueToPods[curVal].pods[k] = 1
										topologyValueToPods[curVal].numPods ++
										sumPods++
									:: else->;
								fi;
							:: else->;
						fi;
					}

					flag = 1
					topologyIsBalanced()
					if 
						:: flag == 0 ->
							// for (k : 0 .. MAX_VALUE-1) {
							// 	printf("[*]%d %d %d!!\n", k, topologyValueToPods[k].numPods, topologyValueToPods[k].exist)
							// 	for ( p : 1 .. POD_NUM ) { 
							// 		printf("[*]%d %d\n", p, topologyValueToPods[k].pods[p])
							// 	}
							// }
							// printf("[*]~~~~\n")

							deschedulerTopoSortArray sortedDomains[MAX_VALUE]
							balanceDomains(podTemplates[i].topoSpreadConstraints[j])
							// They run the podFilter again. Not sure if this is needed. Omitting for now
							for (k : 0 .. sumValues-1) {
								count = 0;
								for (p : 1 .. POD_NUM ) {
									if 
										:: count == sortedDomains[k].evictedNumPods ->
											break
										:: else->
									fi;
									if 
										:: topologyValueToPods[sortedDomains[k].index].pods[p] == 1 ->
											podsForEviction[p] = 1
											count++
											printf("[*][DeScheduler] For constraint topoKey %d, Pod %d pending for deletion\n", podTemplates[i].topoSpreadConstraints[j].topologyKey, p)
										:: else->
									fi;
								}
							}

						:: else->
							printf("[**][DeScheduler] Skipping constraint %d in podTemplates %d, it's balanced\n", j, i)
					fi;
				:: else->;
			fi;
			sumPods = 0;
			sumValues = 0;
		}
	}

	for (i : 1 .. POD_NUM) {
		if 
			:: podsForEviction[i] == 1 ->
				flag = 0
				// Imp in evictions/evictions.go/EvictPod
				evictPod(i)
			:: else->
		fi;
		podsForEviction[i] = 0;
	}
}

// inline defaultEvictor()
// {

// }