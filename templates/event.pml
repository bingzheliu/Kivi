

// TODO: this is a passive event, may need to be distinguished 
proctype kernelPanic(short i)
{
	int times = 0;

	do 
		:: nodes[i].status == 1 && nodes[i].cpuLeft * 100 / nodes[i].cpu <= 2 -> 
			atomic{
				times ++;
				printf("[**]node %d kernel panic, times %d\n", i, times)
				nodes[i].status = 0;
				
				if 
					:: times > 5 ->
						assert(false)
					:: else->;
				fi;

				
			}	
	od;
}

proctype eventCpuChange(short targetDeployment)
{
	short cpu_change = 0, pod_selected = 0, index_selected = 0;
	bit direction = 0;
	int i = 0, j = 0, k = 0;

	do
	:: i < 5 -> 
		atomic {
			// can we only select the pod from the running list?

			d[targetDeployment].replicaSets[d[targetDeployment].curVersion].replicas != 0;

			select(index_selected : 0 .. d[targetDeployment].replicaSets[d[targetDeployment].curVersion].replicas-1);
			select(cpu_change : 1 .. 4);
			select(direction : 1 .. 1);

			// Because some podIds can be invalid, so need to do a post-processing
			j = 0;
			k = 0;
			printf("[**]Index %d is selected\n", index_selected)
			do
				:: j <= index_selected->
					pod_selected = d[targetDeployment].replicaSets[d[targetDeployment].curVersion].podIds[k]
					if
						:: (pods[pod_selected].status == 0) || (pod_selected == 0)->
							k++;
						:: else->
							j++;
							k++;
					fi;
				:: else->break;
			od;

			if
			:: direction == 0 ->
				cpu_change = -cpu_change;
			:: else->;
			fi;

			nodes[pods[pod_selected].loc].cpuLeft = nodes[pods[pod_selected].loc].cpuLeft + pods[pod_selected].cpu;
			if
				:: pods[pod_selected].cpu + cpu_change < 0 -> 
					pods[pod_selected].cpu = 0;
				:: pods[pod_selected].cpu + cpu_change > POD_CPU_THRE ->
					pods[pod_selected].cpu = POD_CPU_THRE;
				:: else ->
					pods[pod_selected].cpu = pods[pod_selected].cpu+cpu_change;
			fi;
			nodes[pods[pod_selected].loc].cpuLeft = nodes[pods[pod_selected].loc].cpuLeft - pods[pod_selected].cpu;

			printf("[**]CPU change %d on pod %d, now %d; node %d, now %d\n", cpu_change, pod_selected, pods[pod_selected].cpu, pods[pod_selected].loc, nodes[pods[pod_selected].loc].cpuLeft);

			// Only support HPA for deployment for now.
			if 
				:: pods[pod_selected].workloadType == 1 ->
					hpaQueue[hpaTail] = pods[pod_selected].workloadId;
					hpaTail ++;
				:: else ->;
			fi;

			i ++;
event_cpu_1:	cpu_change = 0;
				pod_selected = 0;
				direction = 0;
		}
	od;
}