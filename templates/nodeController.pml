
// About node controller
// 1. We don't impl the shut down grace period for now.

//
// TODO: read the code to impl this controller. Now it's a simplified version based on documents. 
// This now is a temp solution for development
proctype nodeController() {
	short i = 0, j = 0, k = 0, max = 0;
	printf("[**]Node controller started.\n");

	do
	:: (ncIndex < ncTail) ->
		atomic{
			i = ncQueue[ncIndex];
			if 
				:: (nodes[i].status != 1) && (nodes[i].numPod > 0) ->
					// Not implement the graceful shutdown
					// TODO: may need another thread for automatically update deployment info. But the drawback is to add non-logic related interactions.
						j = 1;
						for (j : 1 .. POD_NUM ) {
							if 
								:: pods[j].loc == i && pods[j].status == 1 ->
										kblQueue[kblTail] = j;
										kblTail++;
								:: else ->;
							fi;
						}
					
				:: else->;
			fi;

			ncIndex ++;
		}
	od;
}
