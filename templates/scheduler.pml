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
	podTopologySpreadFiltering(podTemplates[pods[curPod].podTemplateId]);
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
		nodes[i].score = 0;
		nodes[i].curScore = 0;
		if
			:: nodes[i].status != 1 ->
				nodes[i].score = -1;
				nodes[i].curScore = -1;
				nodes[i].curAffinity = 0;
				nodes[i].curTaint = 0;
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
		:: nodes[i].status == 1 && nodes[i].score > max ->
				max = nodes[i].score;
				selectedNode = i;
		:: else->;
		fi
		i++;
	:: else -> break;
	od;

	if
	:: max == -1 -> 
		printf("[*]No feasiable node!\n");
		assert(false);
	:: else->;
	fi;

	printf("[**]Pod %d is scheduled on node %d, with score %d\n", curPod, selectedNode, max);
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
	:: selectedNode == 0 && pods[curPod].important == 1 ->
		assert(false);
	:: else->;
	fi;
}

inline bindNode()
{
	nodes[selectedNode].numPod++;
	nodes[selectedNode].cpuLeft = nodes[selectedNode].cpuLeft - pods[curPod].cpu;
	nodes[selectedNode].memLeft = nodes[selectedNode].memLeft - pods[curPod].memory;

	pods[curPod].loc = nodes[selectedNode].id;
	pods[curPod].status = 1;
	podTotal++;

	if 
		:: pods[curPod].workloadType == 1 ->
			j = pods[curPod].workloadId;
			d[j].replicas ++;

			k = d[j].replicaSets[d[j].curVersion].replicas;
			updatePodIds(d[j].replicaSets[d[j].curVersion], curPod)
			d[j].replicaSets[d[j].curVersion].replicas++;
			d[pods[i].workloadId].replicasInCreation --;
			
		:: else ->;
	fi;

	// zone_num_pod[node[node_selected].zone]++;
}

proctype scheduler()
{
	short i = 0, j = 0, k = 0, max = 0;
	printf("[**]Scheduler started.\n");

	do
	:: (sIndex < sTail) ->
		atomic{
			short curPod = sQueue[sIndex];
			short selectedNode = 0;
			// TODO: support other types of workload resources

			printf("[**]Attempting to schedule Pod %d\n", curPod);

			clearNodeScore();
			scheduleOne();
			checkIfUnschedulable();
			bindNode();

			// Only support HPA for deployment for now.
			if 
				:: pods[curPod].workloadType == 1 ->
					hpaQueue[hpaTail] = pods[curPod].workloadId;
					hpaTail ++;
				:: else ->;
			fi;

			selectedNode = 0;
			i = 0;
			j = 0;
			k = 0;
			max = 0;

			sIndex ++;
		}
	od;
}
