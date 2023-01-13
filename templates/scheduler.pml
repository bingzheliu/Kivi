// scheduler
// 1. We don't model the detailed queuing behavior for now, i.e. activeQ, backoffQ, unschedulable data structure. (introduced in scheduler/internal/queue/scheduling_queue.go)
// 2. We don't model it as priority queue for now. Instead, every pod has an euqal priority and will be treated as FIFO. 
// 3. We now only support single profile of the scheduling, in particular, the default one. But can be easily extend to support customized profile in the future. 

#define SCHEDULER_THRE_NODE 1
#define SCHEDULER_THRE_ZONE 1

#define SCHEDULER_QUEUE_SIZE 100

#include "scheduler_plugins.pml"

// in controller_utils 
short sQueue[DEPLOYMENT_QUEUE_SIZE];
short sTail = 0;
short sIndex = 0;

/*-------------------------------
Scheduling cycle
preFilter -- filter -- preScore -- Score -- Normalize Score
We don't distinguish between preFilter and filter. 
We don't distinguish between preScore, score and normalizeScore. 
Because we don't need to fit into the scheduling framework as they have, e.g. each score() function is for one node. Instead, it's enough to implement in two phases to capture the logic. 
---------------------------------*/

inline filter()
{
	// All these filter are AND logic
	nodeName();
	nodeAffinityFilter();
}

inline score()
{	
	nodeAffinityScore();
}	


/*------------------------------*/

inline clearNodeScore()
{
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		nodes[i].score = 0;
		i++;
	:: else -> break;
	od
}

// get the node that have the highest score, if multiple are the same, choosing the smallest indexing node
inline findFeasibleNode()
{
	max = 0;
	i = 1;
	do
	:: i < NODE_NUM+1 ->
		if 
		:: node[i].status > 0 && node[i].score > max ->
				max = node[i].score;
				selectedNode = i;
		:: else->;
		fi
		i++;
	:: else -> break;
	od;

	printf("Pod %d is scheduled on node %d, with score %d\n", curPod, selectedNode, max);
}


inline scheduleOne()
{
	//omit preFilter();

	filter();
	//omit preScore();
	score();
	//omit normalizeScore();

	findFeasibleNode();
}

// This is an invariants check. 
// If it's unschedulable and the pod is important, assert false.
// TODO: add various invaraints, e.g. the capacity of the deployment should be more than x. Can add these outside the scheduler. 
inline checkIfUnschedulable()
{
	if
	:: selectedNode == 0 && pod[curPod].important == 1 ->
		assert(false);
	:: else->;
	fi;
}

inline bindNode()
{
	node[selectedNode].pod_num++;
	node[selectedNode].cpu_left = node[selectedNode].cpu_left - pod[curPod].cpu;
	pod[curPod].loc = node[selectedNode].id;
	pod[curPod].status = 1;
	pod_total++;
	zone_num_pod[node[node_selected].zone]++;
}

proctype scheduler()
{
	short i = 0, j = 0, k = 0, max = 0;
	printer("Scheduler started.");

	do
	:: (sIndex < sTail) ->
		short curPod = sQueue[sIndex];
		short selectedNode = 0;

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
