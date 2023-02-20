
proctype event_cpu_change()
{
	short cpu_change, pod_selected;
	bit direction;
	int i;

L1:	do
	:: true -> 
		atomic {
			// can we only select the pod from the running list?
			select(pod_selected : 1 .. POD_NUM);
			select(cpu_change : 1..1);
			select(direction : 1..1);

			if
			:: direction == 0 ->
				cpu_change = -cpu_change;
			:: else->;
			fi;

			printf("CPU change %d on pod %d\n", cpu_change, pod_selected);

			if 
			:: (pods[pod_selected].status == 1) ->
				if
				:: pods[pod_selected].cpu + cpu_change < 0 -> 
					pods[pod_selected].cpu = 0;
				:: pods[pod_selected].cpu + cpu_change > POD_CPU_THRE ->
					pods[pod_selected].cpu = POD_CPU_THRE;
				:: else ->
					pods[pod_selected].cpu = pods[pod_selected].cpu+cpu_change;
				fi;
			:: else-> goto L1;
			fi;

			hpaQueue[hpaTail] = pods[pod_selected].deploymentId;
			hpaTail ++;

			i = 0;
			cpu_change = 0;
			pod_selected = 0;
			direction = 0;
		}
	od;
}