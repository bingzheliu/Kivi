// descheduler
/*
	Note:
	1. According to their design doc, the order of the plugins depends on how user define them in their yaml config files.
	2. Version: 0.27.1
*/
#include "deschedulerPlugins.pml"

proctype descheduler()
{
	short local_last_time = 0;
	short i = 0, j = 0, ii = 0, jj = 0, k = 0, p = 0, count = 0;
	bit flag = 0;

	printf("[**][Descheduler] Descheduler started!\n")

		// Estimation: it may interleave with other periodically controller (etc. HPA) in the wrong order, but it's over estimation, meaning we can cover more ways they iterleave with each other.
		// It's an estimation, because when all other controllers (except for periodical controller) are idle, all periodic controller can decide to start its process, while in reality they will follow the periodic time, which we don't model precisely here.
#ifdef BACK_TO_BACK_OPT
endDes1:atomic{
endDes:	do
		:: (dsIndex != dsTail) && (time-local_last_time >= DESCHEDULER_WAIT_TIME || (sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail && ncIndex == ncTail))-> 
#else
endDes:	do
		:: (dsIndex != dsTail) && (time-local_last_time >= DESCHEDULER_WAIT_TIME || (sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail && ncIndex == ncTail))-> 
				atomic{
#endif
						printf("[***][Descheduler] Checking for descheduling...\n")
						// If number of ready node is less or equal to 1, then shoudn't do anything
						i = 1;
						j = 0;
						for (i : 1 .. NODE_NUM ) {
							if 
								:: nodes[i].status == 1 ->
									j ++;
								:: else->;
							fi;
						}
						if 
							:: j <= 1 ->
								goto des1;
							:: else->
						fi;

#ifdef MORE_PODS
						short nodePodCount[NODE_NUM+1];
						short namespacePodCount[NAMESPACE_NUM+1];
#else
						byte nodePodCount[NODE_NUM+1];
						byte namespacePodCount[NAMESPACE_NUM+1];
#endif
						// Go through the profiles 
						// Run deschedule first
						for (ii : 0 .. DES_PROFILE_NUM-1) {
							jj = 0;
							for (jj : 0 .. deschedulerProfiles[ii].numDeschedulePlugins-1 ) {
								// TBD: some process for the evicted pods
								if 
									:: deschedulerProfiles[ii].deschedulePlugins[jj] == 1 ->
									//	removePodsViolatingNodeAffinity()
										skip
									// insert more types of plugins here
									:: else->
										printf("[*Warning] Unknown types of deschedule Plugins!\n")
								fi;
							}	
						}

						// Run balance later
						for (ii : 0 .. DES_PROFILE_NUM-1) {
							jj = 0;
							for (jj : 0 .. deschedulerProfiles[ii].numBalancePlugins-1 ) {
								// TBD: some process for the evicted pods
								if 
									:: deschedulerProfiles[ii].balancePlugins[jj] == 1 ->
										removeDuplicates()
									:: deschedulerProfiles[ii].balancePlugins[jj] == 2 ->
										removePodsViolatingTopologySpreadConstraint()
										skip
									// insert more types of plugins here
									:: else->
										printf("[*Warning] Unknown types of deschedule Plugins!\n")
								fi;
							}
						}
						

des1:					updateQueueIndex(dsIndex, MAX_DESCHEDULER_QUEUE);
						i = 0;
						j = 0;
						ii = 0;
						jj = 0;
						k = 0;
						p = 0;
						count = 0;
						flag = 0;
#ifdef BACK_TO_BACK_OPT
		od;
	}
#else
			}
		od;
#endif
}
