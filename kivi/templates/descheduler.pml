// descheduler


proctype descheduler()
{
	short local_last_time = 0;
	short i = 0, j = 0;

	// Not sure if we need to define a queue for descheduler -- it just run periodically
endDes:	do
		:: (time-local_last_time >= DESCHEDULER_WAIT_TIME || (sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail && ncIndex == ncTail))-> 
			atomic{
				d_step{
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

						// Go through the profiles 
						// Run deschedule first
						i = 0;
						for (i : 0 .. DES_PROFILE_NUM-1) {
							j = 0;
							for (j : 0 .. deschedulerProfiles[i].numDeschedulePlugins ) {
								// TBD: some process for the evicted pods
								if 
									:: deschedulerProfiles[i].deschedulePlugins[j] == 1 ->
										removePodsViolatingNodeAffinity()
									// insert more types of plugins here
									:: else->
										print("[*Warning] Unknown types of deschedule Plugins!")
								fi;
							}	
						}

						// Run balance later
						i = 0;
						for (i : 0 .. DES_PROFILE_NUM-1) {
							j = 0;
							for (j : 0 .. deschedulerProfiles[i].numBalancePlugins ) {
								// TBD: some process for the evicted pods
								if 
									:: deschedulerProfiles[i].balancePlugins[j] == 1 ->
										removeDuplicates()
									:: deschedulerProfiles[i].balancePlugins[j] == 2 ->
										removePodsViolatingTopologySpreadConstraint()
									// insert more types of plugins here
									:: else->
										print("[*Warning] Unknown types of deschedule Plugins!")
								fi;
							}
						}


des1:					i = 0;
						j = 0;
				}
			}
	od;
}
