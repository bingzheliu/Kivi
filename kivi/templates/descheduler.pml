// descheduler

#define MAX_DUPLICATE_REPLICA 1

proctype descheduler()
{
	short pod_selected, i, max;

	// not to implement more complicated pod filtering for now; 
L4:	do
	:: 	test_duplication() -> 
		printf("There's duplicated pods more than %d on node.\n", MAX_DUPLICATE_REPLICA);
		atomic {
			i = 1;
			do
			:: i < POD_NUM+1 ->
				if 
					:: pod[i].status == 1 ->
						if 
						:: node[pod[i].loc].pod_num > MAX_DUPLICATE_REPLICA ->
								pod_selected = i;
								break;
						:: else->;
						fi;
					:: else->;
				fi;
				i++
			:: else -> break;
			od;

			// not processed the case where there's no pod left, which should be elimited becase of the pre-condition test_duplication
			// deleting the pod
			printf("[descheduler] removing pod %d from node %d...\n", pod_selected, pod[pod_selected].loc)
			node[pod[pod_selected].loc].pod_num--;
			node[pod[pod_selected].loc].cpu_left = node[pod[pod_selected].loc].cpu_left + pod[pod_selected].cpu;
			zone_num_pod[node[pod[pod_selected].loc].zone]--;
			pod_total--;
			pod[pod_selected].loc = 0;
			pod[pod_selected].status = 0;
			pod[pod_selected].num_deschedule++;

			assert(pod[pod_selected].num_deschedule <= 2)

			pod_cpu_change_status = 1;

			pod_selected = 0;
			i = 0;
			max = 0;
		}
	od;
}
