/*
	Deployment controller. Author: Bingzhe Liu. 02/20/2023.
	
	1. We model the rollout event in sequence, meaning that when a rollout happen, no new rollout and scale event will take place at the same time.     
	2. We don't model unheathy pod for now, otherwise, need to modify the rollout (the scale down old replica part)
	3. Now the queue is not a rolling array. We make it only deal with number of DEPLOYMENT_QUEUE_SIZE events for now. 
	4. We modeled two version of the deployment. So any history feature/rollback to older version are not supported now.
	5. Although deployment is not atomic in real world, we approximate it as atomic approach. Since the calculation of how many pods shouldn't take too long. 
*/


// according to https://github.com/kubernetes/kubernetes/blob/3ffdfbe286ebcea5d75617da6accaf67f815e0cf/pkg/controller/replicaset/replica_set.go#L848
// sort the pod according to the number of related pod, related pods are defined by the pods that belong to the replica sets whose "controllers" are 
// the same. 
// TODO: check on what exactly these controller means. For now, it looks like means replicasets that belong to the same deployment. 

// There are many rules when it comes to deleting pods: https://github.com/kubernetes/kubernetes/blob/4106b10d9c3abe0e90153376ce7cb26b0fb2d1d5/pkg/controller/controller_utils.go#L753 
// TODO: we mainly look into ranks for now, depending on which feature we model, will add more later. 
inline scorePods()
{
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
			:: pods[i].status == 1 && pods[i].workloadId == curD && pods[i].workloadType == 1 ->
				podsOnNode[pods[i].loc]++;
			:: else->;
		fi;
		i++;
	:: else -> break;
	od;
}

inline deleteAPodUpdate()
{
	d[curD].replicasInDeletion ++;
	pods[podSelected].status = 3;
	updateQueue(kblQueue, kblTail, kblIndex, podSelected, MAX_KUBELET_QUEUE)	
}

// TODO: check on if a pod has not been scheduled, will it be considered in deletion?
inline deleteAPod()
{
	short cur_max = 0;
	i = 1;
	podSelected = 0;
	
	do
	:: i < POD_NUM+1 ->
		if 
			:: pods[i].status == 1 && pods[i].workloadId == curD && pods[i].workloadType == 1 ->
				pods[i].score = podsOnNode[pods[i].loc];
				if 
				:: pods[i].score > cur_max ->
					cur_max = pods[i].score;
					podSelected = i;
				:: else->;
				fi;
				printf("[******][Deployment] pod score %d: %d; max: %d\n", i, pods[i].score, cur_max);
			:: else->;
		fi;
		i++;
	:: else -> break;
	od;

	printf("[**][Deployment] Deleting pod %d\n", podSelected);
	// TODO: deal with the scenairo that the deletion failed. 
	deleteAPodUpdate();

	cur_max = 0;
}

inline deletePods(numPods)
{
	short podsOnNode[NODE_NUM+1];
	short numPodDeleted = 0;

	do
	:: numPodDeleted < diff->
		scorePods();
		deleteAPod();
		// pods[podSelected].toDelete = 1;
		numPodDeleted ++;
	:: else -> break;
	od;

	numPodDeleted = 0;
	clearArray(podsOnNode, NODE_NUM+1)
}

inline enqueuePods(batchSize)
{
	i = 0;
	do
	:: i < batchSize ->
		j = 1;
		do
		:: j < POD_NUM+1 -> 
			if
			:: pods[j].status == 0 ->
				copyDeploymentInfoToPod(pods[j], curD);
				pods[j].status = 2;
				printf("[*][Deployment] create; %d; Adding a new pod %d to deployment %d\n", curD, j, curD)
				updateQueue(sQueue, sTail, sIndex, j, MAX_SCHEDULER_QUEUE)
				break;
			:: else->;
			fi;
			j++;
		::else -> break;
		od;
		i++;
	:: else -> 
		break;
	od;
}

inline scale(curReplicaSet)
{
	// $$$$ this variable can be parameterized. 
	short batchSize = 0, remaining = 0;

	// TODO: add dealing pause
	if
	:: curReplicaSet.specReplicas <  curReplicaSet.replicas - d[curD].replicasInDeletion ->
		short diff =  curReplicaSet.replicas - curReplicaSet.specReplicas - d[curD].replicasInDeletion;

		printf("[**][Deployment] Starting the deployment controller to delete %d pods\n", diff);
		deletePods(diff);

		podSelected = 0;
		i = 0;
		diff = 0;


	// TODO: refine the d[curD].replicasInCreation. 
	:: curReplicaSet.specReplicas >  curReplicaSet.replicas + d[curD].replicasInCreation ->
		// do slowStartBatch, https://github.com/kubernetes/kubernetes/blob/98742f9d77a57aec44cc05b1daf721973fb029be/pkg/controller/replicaset/replica_set.go#L742
		// may be simplified by not having these batch updates

		// Since we are doing atomic, batch may not actually make difference. But keep it for now. 
		remaining = curReplicaSet.specReplicas - curReplicaSet.replicas - d[curD].replicasInCreation;
		batchSize = (remaining < SlowStartInitialBatchSize -> remaining : SlowStartInitialBatchSize)
		printf("[*][Deployment] scale; %d; increase; %d; Too few replicas in replicaSet %d need to create %d\n", curD, curReplicaSet.specReplicas, curReplicaSet.id, remaining);
		
		do
		:: batchSize > 0 ->
			// TODO: confirm if one batch needs to wait until the pods are scheduled or only created, currently I only see it is "posted" on API server, it shouldn't been scheduled.  --> looks like it may not wait
			// This code actually did the Pod Post: https://github.com/kubernetes/kubernetes/blob/97d37c29552790384b0a8b8f6f05648f28e07c55/staging/src/k8s.io/client-go/kubernetes/typed/core/v1/pod.go#L120 

			// curReplicaSet.replicas = curReplicaSet.replicas + batchSize;
			// d[curD].replicas = d[curD].replicas + batchSize;
			d[curD].replicasInCreation = d[curD].replicasInCreation + batchSize;
			enqueuePods(batchSize);
			remaining = remaining - batchSize;
			min(batchSize, remaining, 2*batchSize);

		:: else -> break;
		od;
	:: else->;
	fi;

	batchSize = 0;
	remaining = 0;
}


inline rollout()
{
	short oldV = d[curD].curVersion;
	short newV = 1 - oldV;
	if
		:: d[curD].strategy == 0 ->
			// Recreate, looks like it does not comply with the MaxUnavailable Replicas. 
			d[curD].replicaSets[oldV].specReplicas = 0
			scale(d[curD].replicaSets[oldV]);

			d[curD].replicaSets[newV].specReplicas = d[curD].specReplicas;
			scale(d[curD].replicaSets[newV]);

			d[curD].curVersion = newV;

		:: else ->
			// rollingUpdate
			// TODO: I did not fully understand the example 1: https://github.com/kubernetes/kubernetes/blob/4106b10d9c3abe0e90153376ce7cb26b0fb2d1d5/pkg/controller/deployment/rolling.go#L114
			// TODO: I did model the pod that is in the un-ready status. Need to determine whether to model it after looking into other controllers. 
			do
			:: d[curD].replicas < d[curD].specReplicas + d[curD].maxSurge * d[curD].replicas / 100 -> 
				d[curD].replicaSets[newV].specReplicas = d[curD].specReplicas + d[curD].maxSurge *  d[curD].replicas / 100 - d[curD].replicas;
				scale(d[curD].replicaSets[newV]);
			:: d[curD].replicaSets[newV].replicas == d[curD].replicas -> break;
			:: else ->
				d[curD].replicaSets[oldV].specReplicas =  d[curD].replicas - d[curD].maxUnavailable * d[curD].replicas / 100;
				scale(d[curD].replicaSets[oldV]);
			od;

			d[curD].curVersion = newV;
	fi;
	oldV = 0;
	newV = 0;
}


/*****omitting*****/
// rsc.burstReplicas

// TODO: check on deployment trigger reason. If in bootstrapping, how it works?
// TODO: what if there's both pods in creation and deletion? 
proctype deploymentController()
{
		short i = 0, j = 0, podSelected = 0;

endDC:	do
		:: (dcIndex != dcTail && kblIndex == kblTail) ->
				atomic{
					d_step {
						short curD = dcQueue[dcIndex];
						printf("[**][Deployment] Start to work on deployment %d\n", curD)

						if
						:: (d[curD].specReplicas != d[curD].replicas + d[curD].replicasInCreation - d[curD].replicasInDeletion) -> 
							printf("[***][Deployment] replicas spec: %d, cur: %d, in creation: %d, in deletion: %d\n", d[curD].specReplicas, d[curD].replicas, d[curD].replicasInCreation, d[curD].replicasInDeletion)
							d[curD].replicaSets[d[curD].curVersion].specReplicas = d[curD].specReplicas;
							scale(d[curD].replicaSets[d[curD].curVersion]);
						// TODO: refine this rollout condition
						:: else-> ;
							printf("[**][Deployment] Deployment %d specReplicas is the same as replicas\n", curD)
							//rollout();
						fi;

						//updateQueue(hpaQueue, hpaTail, hpaIndex, curD)
						updateQueueIndex(dcIndex, MAX_DEP_QUEUE)

						time = time + DEP_RUN_TIME

						i = 0; 
						j = 0; 
						podSelected = 0;
						curD = 0;
					}
				}
		od;
}
