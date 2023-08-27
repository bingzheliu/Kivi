
//
// TODO: read the code to impl this controller. Now it's a simplified version based on documents. 
// Now this only in charge of deleting pod
proctype kubelet() {
	short i = 0, j = 0;
	bit flag = 0;
	printf("[**]kubelet controller started.\n");

	// TODO: deal with the scenairo that the deletion failed. 
endK:	do
		:: (kblIndex != kblTail) ->
			atomic {
				d_step{
					i = kblQueue[kblIndex];
					if 
						:: pods[i].status == 0 ->
							printf("[**][Kubelet] Pod %d has already been deleted\n", i)

						// create a pod
						:: pods[i].status == 2 && pods[i].loc != 0 ->
							short selectedNode = pods[i].loc

							pods[i].status = 1;
							pods[i].startTime = time;
							//podTotal++;

							if 
								:: pods[i].workloadType == 1 ->
									j = pods[i].workloadId;
									// d[j].replicas ++;
									// k = d[j].replicaSets[d[j].curVersion].replicas;
									replicasetAddPod(dStable[j].replicaSets[d[j].curVersion], i)
									dStable[j].replicasInCreation --;
									updateQueue(dsQueue, dsTail, dsIndex, pods[i].workloadId, MAX_DESCHEDULER_QUEUE);

								:: else ->;
							fi;

							printf("[*][Kubelet] start; %d; %d; Created pod %d on node %d, deployment %d now have %d replicas\n", i, selectedNode, i, selectedNode, pods[i].workloadId, d[pods[i].workloadId].replicas);
							selectedNode = 0;
							
						:: pods[i].status == 3 ->
							pods[i].curCpuIndex = 0;
							// d[pods[i].workloadId].replicas --;
							flag = 0
							replicasetDeletePod(dStable[pods[i].workloadId].replicaSets[d[pods[i].workloadId].curVersion], i)
							pods[i].status = 0;
							dStable[pods[i].workloadId].replicasInDeletion --;
							// podTotal = podTotal - 1;

							j = pods[i].loc
							if 
								:: j != 0 ->
									nodes[j].numPod = nodes[j].numPod - 1;
									nodes[j].cpuLeft = nodes[j].cpuLeft + podsStable[i].cpu;
									nodes[j].memLeft = nodes[j].memLeft + podsStable[i].memory;
								:: else->
							fi;
							// TODO: move this message to Deployment
							printf("[*][Kubelet] delete; %d; Deleted pod %d on node %d, deployment %d now have %d replicas\n", pods[i].workloadId, i, j, pods[i].workloadId, d[pods[i].workloadId].replicas);

							if 
								:: pods[i].workloadType == 1 ->
									printf("[******] Enqueue in kubelet\n")
									updateQueue(dcQueue, dcTail, dcIndex, pods[i].workloadId, MAX_DEP_QUEUE)
									updateQueue(hpaQueue, hpaTail, hpaIndex, pods[i].workloadId, MAX_HPA_QUEUE)
									updateQueue(dsQueue, dsTail, dsIndex, pods[i].workloadId, MAX_DESCHEDULER_QUEUE);
								:: else->;
							fi;
							// TODO: add a pod info clear func. Not clearing pod info for now, as we will override them later. But this may potentially cause problem if we made mistakes on overriding. 
						:: pods[i].status == 1 -> skip;
						:: else ->
							printf("[**][Kubelet] Unknown pod status %d with pod Id %d and location %d\n", pods[i].status, i, pods[i].loc)
					fi;
					updateQueueIndex(kblIndex, MAX_KUBELET_QUEUE);
					time = time + KUBELET_RUN_TIME;
					printf("[***] Finished Kubelet\n");
					i = 0;
					j = 0;
					flag = 0;
				}	
			}
	od;


}