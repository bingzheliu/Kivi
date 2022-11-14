
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
			:: (pod[pod_selected].status == 1) ->
				if
				:: pod[pod_selected].cpu + cpu_change < 0 -> 
					pod[pod_selected].cpu = 0;
				:: pod[pod_selected].cpu + cpu_change > POD_CPU_THRE ->
					pod[pod_selected].cpu = POD_CPU_THRE;
				:: else ->
					pod[pod_selected].cpu = pod[pod_selected].cpu+cpu_change;
				fi;
			:: else-> goto L1;
			fi;

			pod_cpu_change_status = 1;


			i = 0;
			cpu_change = 0;
			pod_selected = 0;
			direction = 0;
		}
	od;
}