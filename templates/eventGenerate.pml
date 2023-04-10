
// proctype podCpuChangeWithPattern(short i)
// {
// 	short cur_pod_template_id = pods[i].podTemplateId;
// 	do 
// 		::  pods[i].status == 1 && pods[i].curCpuIndex < podTemplates[cur_pod_template_id].maxCpuChange ->
// 			atomic{
// 				d_step {
// 					short cpu_change = podTemplates[cur_pod_template_id].curCpuRequest[pods[i].curCpuIndex] - pods[i].cpu
// 					updatePodCpuUsageOnNode(i, cpu_change);
// 					pods[i].curCpuIndex ++;

// 					if 
// 						:: pods[i].workloadType == 1 ->
// 							hpaQueue[hpaTail] = pods[i].workloadId;
// 							hpaTail ++;
// 						:: else ->;
// 					fi;
// 				}
// 			}
// 		:: else-> break;
// 	od;
// }

inline podCpuChangeWithPatternExec(i)
{
	d_step {
		short cur_pod_template_id = pods[i].podTemplateId;
		short cpu_change = podTemplates[cur_pod_template_id].curCpuRequest[pods[i].curCpuIndex] - pods[i].cpu
		updatePodCpuUsageOnNode(i, cpu_change);
		pods[i].curCpuIndex ++;

		if 
			:: pods[i].workloadType == 1 ->
				updateQueue(hpaQueue, hpaTail, hpaIndex,  pods[i].workloadId)
			:: else ->;
		fi;
	}
}

// TODO: A potential problem is that we can't be sure about how long each CPU usage will last. 
proctype podCpuChangeWithPattern()
{
			do 
				:: true -> 
endPCCWP:			atomic{
					if
							// ::  pods[0].status == 1 && pods[0].curCpuIndex < podTemplates[pods[0].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(0)
							// ::  pods[1].status == 1 && pods[1].curCpuIndex < podTemplates[pods[1].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(1)
							// ::  pods[2].status == 1 && pods[2].curCpuIndex < podTemplates[pods[2].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(2)
							// ::  pods[3].status == 1 && pods[3].curCpuIndex < podTemplates[pods[3].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(3)
							// ::  pods[4].status == 1 && pods[4].curCpuIndex < podTemplates[pods[4].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(4)
							// ::  pods[5].status == 1 && pods[5].curCpuIndex < podTemplates[pods[5].podTemplateId].maxCpuChange ->
							// 		podCpuChangeWithPatternExec(5)
							[$podCpuChangeWithPattern]
					fi;
					}
			od;
}



// TODO: this is a passive event, may need to be distinguished 
// TODO: this may start too many process if nodes number is large. work on a different kind of implementation. 
proctype kernelPanic(short i)
{
	int times = 0;

endKP:	do 
		:: nodes[i].status == 1 && (nodes[i].cpuLeft * 100 / nodes[i].cpu <= 2) -> 
				atomic{
					times ++;
					printf("[**]node %d kernel panic, times %d\n", i, times)
					nodes[i].status = 2;

					updateQueue(ncQueue, ncTail, ncIndex, i)
					
					if 
						:: times > 5 ->
							assert(false)
						:: else->;
					fi;
				}	
			// recover from panic
			:: nodes[i].status == 2 && (nodes[i].cpuLeft * 100 / nodes[i].cpu > 2) ->
				atomic{
					printf("[**]node %d kernel panic recovered\n", i)
					nodes[i].status = 1;
				}
		od;
}
