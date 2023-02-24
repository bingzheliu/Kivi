
proctype eventCpuChange(short targetDeployment)
{
	short cpu_change = 0, pod_selected = 0;
	bit direction = 0;
	int i = 0;

	do
	:: i < 5 -> 
		atomic {
			// can we only select the pod from the running list?

			select(pod_selected : 0 .. d[targetDeployment].replicaSets[d[targetDeployment].curVersion].replicas-1);
			select(cpu_change : 1..4);
			select(direction : 1..1);

			pod_selected = d[targetDeployment].replicaSets[d[targetDeployment].curVersion].podIds[pod_selected]
			if 
				:: (pods[pod_selected].status == 0) || (pods[pod_selected].deploymentId != targetDeployment) ->
					assert(false)
				:: else->;
			fi;

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

			printf("CPU change %d on pod %d, now %d; node %d, now %d\n", cpu_change, pod_selected, pods[pod_selected].cpu, pods[pod_selected].loc, nodes[pods[pod_selected].loc].cpuLeft);

			hpaQueue[hpaTail] = pods[pod_selected].deploymentId;
			hpaTail ++;

			i ++;
			cpu_change = 0;
			pod_selected = 0;
			direction = 0;
		}
	od;
}