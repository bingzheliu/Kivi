
proctype deployment_controller()
{
	short pod_selected, i, max;

	// not to implement other functionality for deployment controller for now

	// not to implement more complicated pod filtering for now; 
	// delete one pod at one time, can't do batch now
	do
	:: (pod_num_exp<pod_total) -> 
		printf("Starting the deployment controller to delete pods, %d, %d\n", pod_num_exp, pod_total);
		atomic {
			// according to https://github.com/kubernetes/kubernetes/blob/3ffdfbe286ebcea5d75617da6accaf67f815e0cf/pkg/controller/replicaset/replica_set.go#L848
			// sort the pod according to the number of related pod
			max = 0;
			i = 1;
			do
			:: i < POD_NUM+1 ->
				if 
					:: pod[i].status == 1 ->
						pod[i].score = node[pod[i].loc].pod_num;
						if 
						:: pod[i].score > max ->
								max = pod[i].score;
								pod_selected = i;
						:: else->;
						fi;
						printf("pod score %d: %d; max: %d", i, pod[i].score, max);
					:: else->;
				fi;
				i++
			:: else -> break;
			od;

			// not processed the case where there's no pod left, which should be elimited becase of the pre-condition pod_num_exp<pod_total
			// deleting the pod
			printf("[deployment] removing pod %d from node %d...\n", pod_selected, pod[pod_selected].loc)
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
