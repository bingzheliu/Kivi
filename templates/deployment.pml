/*
	1. We model the rollout event in sequence, meaning that when a rollout happen, no new rollout and scale event will take place at the same time.     
	2. We don't model unheathy pod for now, otherwise, need to modify the rollout (the scale down old replica part)
	3. Now the queue is not a rolling array. We make it only deal with number of DEPLOYMENT_QUEUE_SIZE events for now. 
	4. We modeled two version of the deployment. So any history feature/rollback to older version are not supported now.
*/

#define DEPLOYMENT_QUEUE_SIZE 100


// in controller_utils 
short dcQueue[DEPLOYMENT_QUEUE_SIZE];
short dcTail = 0;
short dcIndex = 0;


inline scorePods()
{
	// according to https://github.com/kubernetes/kubernetes/blob/3ffdfbe286ebcea5d75617da6accaf67f815e0cf/pkg/controller/replicaset/replica_set.go#L848
	// sort the pod according to the number of related pod, related pods are defined by the pods that belong to the replica sets whose "controllers" are 
	// the same. 
	// TODO: check on what exactly these controller means. For now, it looks like means replicasets that belong to the same deployment. 
	
	// There are many rules when it comes to deleting pods: https://github.com/kubernetes/kubernetes/blob/4106b10d9c3abe0e90153376ce7cb26b0fb2d1d5/pkg/controller/controller_utils.go#L753 
	// TODO: we mainly look into ranks for now, depending on which feature we model, will add more later. 
	

	i = 1;
	do
	:: i < NODE_NUM+1 ->
		podsOnNode[i] = 0;
		i++;
	:: else -> break;
	od;

	i = 1;
	do
	:: i < POD_NUM+1 ->
		if 
			:: pod[i].status == 1 && pod[i].deploymentId == curD ->
				podsOnNode[pod[i].loc]++;
			:: else->;
		fi;
		i++;
	:: else -> break;
	od;
}

inline deleteAPod()
{
	int cur_max = 0;
	i = 1;
	podSelected = 0;
	
	do
	:: i < POD_NUM+1 ->
		if 
			:: pod[i].status == 1 && pod[i].toDelete != 1 && pod[i].deploymentId == curD ->
				pod[i].score = podsOnNode[pod[i].loc];
				if 
				:: pod[i].score > cur_max ->
					cur_max = pod[i].score;
					podSelected = i;
				:: else->;
				fi;
				printf("pod score %d: %d; max: %d", i, pod[i].score, cur_max);
			:: else->;
		fi;
		i++;
	:: else -> break;
	od;
}

inline deletePods(numPods)
{
	short podsOnNode[NODE_NUM+1];
	scorePods();

	short numPodDeleted = 0;

	do
	:: numPodDeleted < diff->
		deleteAPod();
		pod[podSelected].toDelete = 1;
		numPodDeleted ++;
	:: else -> break;
	od;


}

/*
inline scale(curReplicaSet)
{
	// TODO: add pause
	if
		:: xxx -> 
			if
			:: dExpected[curD].replicas <  d[curD].replicas ->
				// Let assume the deleting pods is atomic
				atomic {
					printf("Starting the deployment controller to delete pods, %d, %d\n", pod_num_exp, pod_total);

					short diff = d[curD].replicas - dExpected[curD].replicas;
					deletePods(diff);

					d[curD].replicas = dExpected[curD].replicas;

					podSelected = 0;
					i = 0;
					max = 0;
					diff = 0;
					numPodDeleted = 0;
				}

			:: else ->
				// do slowStartBatch, https://github.com/kubernetes/kubernetes/blob/98742f9d77a57aec44cc05b1daf721973fb029be/pkg/controller/replicaset/replica_set.go#L742
				// may be simplified by not having these batch updates

				atomic {
					batchSize = SlowStartInitialBatchSize;
					remaining = dExpected[curD].replicas - d[curD].replicas;
					printf("Too few replicas in replicaSet %s need to create %", d[curD].name, remaining);
				}
				do
				:: batchSize > 0 ->
					// TODO: confirm if one batch needs to wait until the pods are scheduled or only created, currently I only see it is "posted" on API server, it shouldn't been scheduled.  --> looks like it may not wait
					// This code actually did the Pod Post: https://github.com/kubernetes/kubernetes/blob/97d37c29552790384b0a8b8f6f05648f28e07c55/staging/src/k8s.io/client-go/kubernetes/typed/core/v1/pod.go#L120 

					atomic {
						d[curD].replicas = d[curD].replicas + batchSize;
				
						remaining = remaining - batchSize;
						batchSize = min(remaining. 2*batchSize);
					}
				:: else -> break;
				od;
			fi;
		:: else->break;
	fi;
}
*/


inline enqueuePods(batchSize)
{
	i = 0;
	do
	:: i < batchSize ->
		j = 0;
		do
		:: j < POD_NUM -> 
			if
			:: pods[j].status == 0 ->
				pods[j].deploymentId = curD;
				pods[j].loc = 0;
				sQueue[sTail] = j;
				sTail++;
				break;
			:: else->;
			fi;
			j++;
		::else -> break;
		od;
		i++;
	:: else -> break;
	od;
}

inline scale(curReplicaSet)
{
	// $$$$ this variable can be parameterized. 
	short SlowStartInitialBatchSize = 1;
	short batchSize = 0, remaining = 0;

	// TODO: add pause
	if
	:: curReplicaSet.expReplicas <  curReplicaSet.replicas ->
		// Let assume the deleting pods is atomic
		atomic {
			printf("Starting the deployment controller to delete pods");

			short diff =  curReplicaSet.replicas - curReplicaSet.expReplicas;
			deletePods(diff);

			// TODO: deal with the scenairo that the deletion failed. 
			curReplicaSet.expReplicas = curReplicaSet.replicas;
			d[curD].replicas = d[curD].replicas - diff;

			podSelected = 0;
			i = 0;
			//cur_max = 0;
			diff = 0;
			//numPodDeleted = 0;
		}

	:: else ->
		// do slowStartBatch, https://github.com/kubernetes/kubernetes/blob/98742f9d77a57aec44cc05b1daf721973fb029be/pkg/controller/replicaset/replica_set.go#L742
		// may be simplified by not having these batch updates

		atomic {
			batchSize = SlowStartInitialBatchSize;
			remaining = curReplicaSet.expReplicas - curReplicaSet.replicas;
			printf("Too few replicas in replicaSet %s need to create %", curReplicaSet.id, remaining);
		}
		do
		:: batchSize > 0 ->
			// TODO: confirm if one batch needs to wait until the pods are scheduled or only created, currently I only see it is "posted" on API server, it shouldn't been scheduled.  --> looks like it may not wait
			// This code actually did the Pod Post: https://github.com/kubernetes/kubernetes/blob/97d37c29552790384b0a8b8f6f05648f28e07c55/staging/src/k8s.io/client-go/kubernetes/typed/core/v1/pod.go#L120 

			atomic {
				// curReplicaSet.replicas = curReplicaSet.replicas + batchSize;
				// d[curD].replicas = d[curD].replicas + batchSize;
				enqueuePods(batchSize);
		
				remaining = remaining - batchSize;
				min(batchSize, remaining, 2*batchSize);
			}
		:: else -> break;
		od;
	fi;
}


inline rollout()
{
	short newV = d[curD].curVersion;
	short oldV = 1 - newV;
	if
		:: d[curD].strategy == 0 ->
			// Recreate, looks like it does not comply with the MaxUnavailable Replicas. 
			d[curD].replicaSets[oldV].expReplicas = 0
			scale(d[curD].replicaSets[oldV]);

			d[curD].replicaSets[newV].expReplicas = d[curD].expReplicas;
			scale(d[curD].replicaSets[newV]);

		:: else ->
			// rollingUpdate
			// TODO: I did not fully understand the example 1: https://github.com/kubernetes/kubernetes/blob/4106b10d9c3abe0e90153376ce7cb26b0fb2d1d5/pkg/controller/deployment/rolling.go#L114
			// TODO: I did model the pod that is in the un-ready status. Need to determine whether to model it after looking into other controllers. 
			do
			:: d[curD].replicas < d[curD].expReplicas + d[curD].maxSurge -> 
				d[curD].replicaSets[newV].expReplicas = d[curD].expReplicas + d[curD].maxSurge - d[curD].replicas;
				scale(d[curD].replicaSets[newV]);
			:: d[curD].replicaSets[newV].replicas == d[curD].replicas -> break;
			:: else ->
				d[curD].replicaSets[oldV].expReplicas =  d[curD].replicas - d[curD].maxUnavailable;
				scale(d[curD].replicaSets[oldV]);
			od;
	fi;
}


/*****omitting*****/
// rsc.burstReplicas


proctype deployment_controller()
{
	short i = 0, podSelected;

	do
		:: (dcIndex < dcTail) ->
			int curD = dcQueue[dcIndex];

			if
			:: (d[curD].expReplicas != d[curD].replicas) -> 
				scale(d[curD].replicaSets[curVersion]);
			:: else-> 
				rollout();
			fi;

			dcIndex++;
	od;
}
