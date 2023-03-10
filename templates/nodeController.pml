

// TODO: think about how to write this condition
// This now is a temp solution for development
// TODO: may need another thread for automatically update deployment info. But the drawback is to add non-logic related interactions.
proctype nodeController(short i) {
	do 
		:: nodes[i].status == 0 ->
			atomic {
				int j = 1;
				for (j : 1 .. POD_NUM + 1) {
					if 
						:: pods[j].loc == i && pods[j].status == 1 ->
							pods[j].status = 0;
							d[pods[j].workloadId].replicas --;
							d[pods[j].workloadId].replicaSets[d[pods[j].workloadId].curVersion].replicas --;
						:: else ->;
					fi;
				}

				int k = 1;
				for (k : 1 .. DEP_NUM + 1) {
					dcQueue[dcTail] = k;
					dcTail++;
				}

				nodes[i].cpuLeft = nodes[i].cpu;
				nodes[i].memLeft = nodes[i].memory;
				nodes[i].numPod = nodes[i].memory;
			
			nodes[i].status = 1;
			}
	od;
}
