
// About node controller
// 1. We don't impl the shut down grace period for now.

//
// TODO: read the code to impl this controller. Now it's a simplified version based on documents. 
// This now is a temp solution for development
proctype nodeController() {
	short i = 0, j = 0;
	printf("[**][nodeController] Node controller started.\n");

#ifdef TAINT
	run taintManger()
#endif

endNC:	do
		:: (ncIndex != ncTail) ->
			atomic{
				d_step{
					i = ncQueue[ncIndex];
					if 
						:: (nodes[i].status != 1) && (nodes[i].numPod > 0) ->
							// Not implement the graceful shutdown
							// TODO: may need another thread for automatically update deployment info. But the drawback is to add non-logic related interactions.
								j = 1;
								for (j : 1 .. POD_NUM ) {
									if 
										:: pods[j].loc == i && pods[j].status != 0 ->
											pods[j].status = 3
											d[pods[j].workloadId].replicasInDeletion++;
											updateQueue(kblQueue, kblTail, kblIndex, j, MAX_KUBELET_QUEUE)
										:: else ->;
									fi;
								}
							
						:: else->;
					fi;

					updateQueueIndex(ncIndex, MAX_NODE_CONTROLLER_QUEUE)
					time = time + NODEC_RUN_TIME

					i = 0;
					j = 0;
				}
			}
		od;
}


#ifdef TAINT
inline evictNoneToleratePod(i)
{
	// we skip the retries
	// we skip the PodDisruptionConditions for now. 
	deleteAPodUpdate(pods[i].workloadId, i);
}
// taint manger is started by the node controller. But it runs seperately
// Main logic in handlePodUpdate and processPodOnNode
proctype taintManger() {
	short i = 0, j = 0;
	printf("[**][taintManger] Taint manager has been started.\n")

endTM: do
	   :: (tmIndex != tmTail) ->
	   	atomic {
	   		d_step{
	   			i = tmQueue[tmIndex];
	   			if
	   				// Make sure the pods is running and has been scheduled. 
	   				:: (pods[i].status == 1) && (pods[i].loc != 0) ->
	   					bit flag;
	   					flag = 0;
	   					// Taint manger only consider the noExecute taint. 
	   					// In the handleNodeUpdate (when creating or update nodes), it only record the noExecute taint in its map.
	   					for (j : 0 .. podTemplates[pods[i].podTemplateId].numNoExecuteNode - 1) {
	   						if 
	   							:: nodesStable[pods[i].loc].taintType == podTemplates[pods[i].podTemplateId].noExecuteNode[j] ->
	   								// printf("[*] here!\n");
	   								flag = 1;
	   								break;
	   							::else->;
	   						fi;
	   					}
	   					if 
	   						:: flag == 1 ->
	   							printf("[*][taintManger] The pod %d is pending for eviction as it cannot tolerate the taint on node %d\n", i, pods[i].loc);
	   							evictNoneToleratePod(i)
	   						:: else->;
	   					fi;

	   				:: else->;
	   					// skip this pod 
	   			fi;

	   			updateQueueIndex(tmIndex, MAX_TAINT_MANAGER_QUEUE);
	   			time = time + NODEC_RUN_TIME;

	   			i = 0;
	   			j = 0;
	   		}
	   	}
	   	od;
}
#endif
