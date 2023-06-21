
short maxSkewNode = 0

proctype updateState()
{
	short i = 0, j = 0;
	do
		:: true -> 
			atomic {
				d_step{
					short curMaxPod = 0;
					short curMinPod = POD_NUM;
					for (i : 1 .. NODE_NUM) {
						if 
							:: nodes[i].status == 1 ->
								curMaxPod = (nodes[i].numPod > curMaxPod -> nodes[i].numPod : curMaxPod);
								curMinPod = (nodes[i].numPod < curMinPod -> nodes[i].numPod : curMinPod);
							:: else->;
						fi;
					}
					maxSkewNode = curMaxPod - curMinPod;
				}
			}
	od;
}