

short cur_node_in_maintenance = 0;
// up to p node could be put down at the same time
// TODO: check on if we could enforce some kind of ordering of the process. maintenance should take times, and two consecutive maintenance job should not happen too soon than scheduling
// Now we do it by waiting for other controller's job to be fully dequeued. 
proctype maintenance(short p)
{
	atomic{
		short i = 1;
		for (i : 1 .. NODE_NUM) {
			if 
				:: nodes[i].status == 1 && nodes[i].maintained == 0 && cur_node_in_maintenance < p ->
					cur_node_in_maintenance ++;
					printf("[***][maintenanceNode] # of %d nodes in maintenance\n", cur_node_in_maintenance);
					run maintenanceNode(i);
			fi;
		}
		i = 0;
	}
}

proctype maintenanceNode(short i)
{
	atomic {
		short local_last_time = time;
		printf("[**][maintenanceNode] Starting maintenance for node %d\n", i)
		nodes[i].status = 0;
		updateQueue(ncQueue, ncTail, ncIndex, i, MAX_NODE_CONTROLLER_QUEUE)
		// This condition is hard coded, meaning to wait for the node to fully shut down, and then put it back.
		if 
			:: ((time - local_last_time >= MAINTENANCE_WAIT_TIME) || (ncIndex == ncTail && hpaTail == hpaIndex && sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail)) ->
					nodes[i].status = 1;
					nodes[i].maintained = 1;
					cur_node_in_maintenance --;
					printf("[**][maintenanceNode] End maintenance for node %d\n", i)
					if 
						:: local_last_time + MAINTENANCE_WAIT_TIME > time ->
							time = local_last_time + MAINTENANCE_WAIT_TIME 
						:: else->;
					fi
					printf("[**]time %d, local_last_time %d, hpaTail %d, hpaIndex %d\n", time, local_last_time, hpaTail, hpaIndex)
		fi;
	}
}

proctype nodeFailure(short i)
{
	nodes[i].status = 0;
	updateQueue(ncQueue, ncTail, ncIndex, i, MAX_NODE_CONTROLLER_QUEUE)
	nodes[i].status = 1;
}


proctype eventCpuChange(short targetDeployment)
{
	short cpu_change = 0, pod_selected = 0, index_selected = 0;
	bit direction = 0;
	short i = 0;
	short local_last_time = time;

	do
	:: i < 5 && ((time - local_last_time >= EVENT_CPU_TIME) || (ncIndex == ncTail && hpaTail == hpaIndex && sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail)) -> 
		atomic {
			// can we only select the pod from the running list?

			d[targetDeployment].replicaSets[d[targetDeployment].curVersion].replicas != 0;

			select(index_selected : 0 .. d[targetDeployment].replicaSets[d[targetDeployment].curVersion].replicas-1);
			select(cpu_change : 1 .. 6);
			select(direction : 1 .. 1);

			d_step{
				printf("[**][eventCpuChange]Index %d is selected\n", index_selected)
				pod_selected = d[targetDeployment].replicaSets[d[targetDeployment].curVersion].podIds[index_selected]

				if
				:: direction == 0 ->
					cpu_change = -cpu_change;
				:: else->;
				fi;
				
				updatePodCpuUsageOnNode(pod_selected, cpu_change)

				// Only support HPA for deployment for now.
				if 
					:: pods[pod_selected].workloadType == 1 ->
						updateQueue(hpaQueue, hpaTail, hpaIndex, pods[pod_selected].workloadId, MAX_HPA_QUEUE)
					:: else ->;
				fi;

				i ++;

				cpu_change = 0;
				pod_selected = 0;
				direction = 0;
				index_selected = 0;
			}	
		}
	:: else->break;
	od;
}