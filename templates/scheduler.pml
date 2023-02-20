// scheduler
// 1. We don't model the detailed queuing behavior for now, i.e. activeQ, backoffQ, unschedulable data structure. (introduced in scheduler/internal/queue/scheduling_queue.go)
// 2. We don't model it as priority queue for now. Instead, every pod has an euqal priority and will be treated as FIFO. 
// 3. We now only support single profile of the scheduling, in particular, the default one. But can be easily extend to support customized profile in the future. 

#include "scheduler_plugins.pml"

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
	nodeNameFilter();
	nodeAffinityFilter();
	taintTolerationFilter();
	// nodeResourceFitFilter();
}

inline scoring()
{	
	nodeAffinityScore();
	taintTolerationScore();
	nodeResourceFitScore();
}	


/*------------------------------*/

inline clearNodeScore()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		nodes[i].score = 0;
		nodes[i].curScore = 0;
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
		:: nodes[i].status > 0 && nodes[i].score > max ->
				max = nodes[i].score;
				selectedNode = i;
		:: else->;
		fi
		i++;
	:: else -> break;
	od;

	if
	:: max == -1 -> 
		printf("No feasiable node!");
		assert(false);
	:: else->;
	fi;

	printf("Pod %d is scheduled on node %d, with score %d\n", curPod, selectedNode, max);
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
	//node[selectedNode].cpu_left = node[selectedNode].cpu_left - pod[curPod].cpu;
	pods[curPod].loc = nodes[selectedNode].id;
	pods[curPod].status = 1;
	pod_total++;

	j = pods[curPod].deploymentId;
	d[j].replicas ++;
	d[j].replicaSets[d[j].curVersion].replicas++;
	j = 0;
	// zone_num_pod[node[node_selected].zone]++;
}

proctype scheduler()
{
	short i = 0, j = 0, k = 0, max = 0;
	printf("Scheduler started.");

	do
	:: (sIndex < sTail) ->
		short curPod = sQueue[sIndex];
		short selectedNode = 0;
		short curD = pods[curPod].deploymentId;

		printf("Attempting to schedule Pod %d\n", curPod);

		atomic{
			clearNodeScore();
			scheduleOne();
			checkIfUnschedulable();
			bindNode();
		}

		selectedNode = 0;
		i = 0;
		j = 0;
		k = 0;
		max = 0;

		sIndex ++;
	od;
}
