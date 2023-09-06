/*
   	Scheduler model. Author: Bingzhe Liu. 02/20/2023.
	1. We don't model the detailed queuing behavior for now, i.e. activeQ, backoffQ, unschedulable data structure. (introduced in scheduler/internal/queue/scheduling_queue.go)
	2. We don't model it as priority queue for now. Instead, every pod has an euqal priority and will be treated as FIFO. 
	3. We now only support single profile of the scheduling, in particular, the default one. But can be easily extend to support customized profile in the future. 
*/
#include "schedulerPlugins.pml"

/*-------------------------------
		Scheduling cycle
preFilter (go through all the nodes) -- filter (filter on per node basis) -- postScore -- preScore -- Score -- Normalize Score
We don't distinguish between preFilter and filter. 
We don't distinguish between preScore, score and normalizeScore. 
Because we don't need to fit into the scheduling framework as they have, e.g. each score() function is for one node. Instead, it's enough to implement in two phases to capture the logic. 
---------------------------------*/

inline filtering()
{
	// All these filter are AND logic
	nodeNameFilter(podTemplates[pods[curPod].podTemplateId]);
	nodeAffinityFilter(podTemplates[pods[curPod].podTemplateId]);
	taintTolerationFilter(podTemplates[pods[curPod].podTemplateId]);
	nodeResourcesFitFilter(podTemplates[pods[curPod].podTemplateId]);
	// this plugin needs to execute after nodeAffinity and taint as it uses their results.
	podTopologySpreadFiltering(curPod, podTemplates[pods[curPod].podTemplateId]);
}

inline scoring()
{	
	nodeAffinityScore(podTemplates[pods[curPod].podTemplateId]);
	taintTolerationScore(podTemplates[pods[curPod].podTemplateId]);
	nodeResourceFitScore(podTemplates[pods[curPod].podTemplateId]);
	podTopologySpreadScoring(podTemplates[pods[curPod].podTemplateId]);
}	


/*------------------------------*/

// set node score to be -1 if its status is 0.
inline clearNodeScore()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		nodesStable[i].score = 0;
		nodesStable[i].curScore = 0;
		if
			:: nodes[i].status != 1 ->
				nodesStable[i].score = -1;
				nodesStable[i].curScore = -1;
				nodesStable[i].curAffinity = 0;
				nodesStable[i].curTaint = 0;
			:: else->;
		fi;
		i++;
	:: else -> break;
	od
}

// get the node that have the highest score, if multiple are the same, choosing the smallest indexing node
inline selectHost()
{
	max = -1;
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if 
		// the actual implementation choose the node randomly when several nodes have the same score. We may omit this detail, and choose the first one encountered. 
		:: nodes[i].status == 1 && nodesStable[i].score > max ->
				max = nodesStable[i].score;
				selectedNode = i;
		:: else->;
		fi
		i++;
	:: else -> break;
	od;

	if
	:: max == -1 -> 
		printf("[*][Scheduler] No feasiable node!\n");
#ifdef NO_FEASIABLE_NODE
		assert(false);
#endif
	:: else->;
		printf("[*][Scheduler] scheduled; %d; %d; Pod %d is scheduled on node %d, with score %d\n", curPod, selectedNode, curPod, selectedNode, max);
	fi;	
}


inline scheduleOne()
{
	//merged preFilter();
	filtering();

	//merged preScore();
	scoring();
	//merged normalizeScore();

	selectHost();
}

// This is an invariants check. 
// If it's unschedulable and the pod is important, assert false.
// TODO: add various invaraints, e.g. the capacity of the deployment should be more than x. Can add these outside the scheduler. 
inline checkIfUnschedulable()
{
	if
	:: selectedNode == 0 && podsStable[curPod].important == 1 ->
#ifdef NO_FEASIABLE_NODE
		assert(false);
#endif
		skip
	:: else->;
	fi;
}

inline bindNode()
{
	pods[curPod].loc = selectedNode;
	updateQueue(kblQueue, kblTail, kblIndex, curPod, MAX_KUBELET_QUEUE)
	// nodes[selectedNode].numPod++;
	// nodes[selectedNode].cpuLeft = nodes[selectedNode].cpuLeft - pods[curPod].cpu;
	// nodes[selectedNode].memLeft = nodes[selectedNode].memLeft - pods[curPod].memory;

	// pods[curPod].status = 1;
	// pods[curPod].startTime = time;
	// //podTotal++;

	// if 
	// 	:: pods[curPod].workloadType == 1 ->
	// 		j = pods[curPod].workloadId;
	// 		d[j].replicas ++;

	// 		k = d[j].replicaSets[d[j].curVersion].replicas;
	// 		replicasetAddPod(d[j].replicaSets[d[j].curVersion], curPod)
	// 		d[j].replicasInCreation --;

	// 	:: else ->;
	// fi;

	// zone_num_pod[node[node_selected].zone]++;
}

// Before actually bind the pod, scheduler cache update the nodeInfo, so it can continue to work without waiting for bind.
// such cache info will be updated again before each scheduling in the schedule_one/schedulePod
inline assumePod()
{
	nodes[selectedNode].numPod++;
	nodes[selectedNode].cpuLeft = nodes[selectedNode].cpuLeft - podsStable[curPod].cpu;
	nodes[selectedNode].memLeft = nodes[selectedNode].memLeft - podsStable[curPod].memory;
}

proctype scheduler()
{
	short i = 0, j = 0, k = 0, max = 0, p = 0;
	printf("[**][Scheduler] Scheduler started.\n");

endSch1: atomic{
endSch2: do
		:: (sIndex != sTail) ->
				d_step{
					short curPod = sQueue[sIndex];
					short selectedNode = 0;
					// TODO: support other types of workload resources

					printf("[**][Scheduler] Attempting to schedule Pod %d\n", curPod);
					if 
						:: pods[curPod].status == 1 ->
							printf("[**][Scheduler] Pod %d has been scheduled!\n", curPod)
						:: pods[curPod].status == 3 ->
							printf("[**][Scheduler] Pod %d is pending for deletion, skip it!\n", curPod)
						:: else->
							clearNodeScore();
							scheduleOne();
							checkIfUnschedulable();
							assumePod();
							bindNode();

							// Only support HPA for deployment for now.
							if 
								:: pods[curPod].workloadType == 1 ->
									updateQueue(hpaQueue, hpaTail, hpaIndex, pods[curPod].workloadId, MAX_HPA_QUEUE)
									// hpaQueue[hpaTail] = pods[curPod].workloadId;
									// hpaTail ++;
								:: else ->;
							fi;
					fi;

					time = time + SCHEDULER_RUN_TIME

					clearNodeScore();

					updateQueueIndex(sIndex, MAX_SCHEDULER_QUEUE)
					selectedNode = 0;
					i = 0;
					j = 0;
					k = 0;
					p = 0;
					max = 0;
					curPod = 0;
				}
		od;
	}
}
