
//
// TODO: read the code to impl this controller. Now it's a simplified version based on documents. 
// Now this only in charge of deleting pod
proctype kubelet() {
	short i = 0, j = 0, k = 0;
	printf("[**]kubelet controller started.\n");

	// TODO: deal with the scenairo that the deletion failed. 
endK:	do
		:: (kblIndex != kblTail) ->
			atomic {
				i = kblQueue[kblIndex];
				if 
					:: pods[i].status == 0 ->
						printf("[**][Kubelet] Pod %d has already been deleted\n", i)
					:: else->
						pods[i].status = 0;
						pods[i].curCpuIndex = 0;
						d[pods[i].workloadId].replicas --;
						replicasetDeletePod(d[pods[i].workloadId].replicaSets[d[pods[i].workloadId].curVersion], i)
						d[pods[i].workloadId].replicasInDeletion --;
						podTotal = podTotal - 1;

						j = pods[i].loc
						nodes[j].numPod = nodes[j].numPod - 1;
						nodes[j].cpuLeft = nodes[j].cpuLeft + pods[i].cpu;
						nodes[j].memLeft = nodes[j].memLeft + pods[i].memory;

						printf("[**][Kubelet] Deleted pod %d on node %d, deployment %d now have %d replicas\n", i, j, pods[i].workloadId, d[pods[i].workloadId].replicas);

						if 
							:: pods[i].workloadType == 1 ->
								updateQueue(dcQueue, dcTail, dcIndex, pods[i].workloadId)
							:: else->;
						fi;
						// TODO: add a pod info clear func. Not clearing pod info for now, as we will override them later. But this may potentially cause problem if we made mistakes on overriding. 
				fi;
				updateQueueIndex(kblIndex)
			}
	od;


}