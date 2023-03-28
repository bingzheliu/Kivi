

// TODO: this is a passive event, may need to be distinguished 
// TODO: this may start too many process if nodes number is large. work on a different kind of implementation. 
proctype kernelPanic(short i)
{
	int times = 0;

	do 
		:: nodes[i].status == 1 && (nodes[i].cpuLeft * 100 / nodes[i].cpu <= 2) -> 
			atomic{
				times ++;
				printf("[**]node %d kernel panic, times %d\n", i, times)
				nodes[i].status = 2;

				ncQueue[ncTail] = i;
				ncTail ++;
				
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

short cur_node_in_maintenance = 0;
// up to p node could be put down at the same time
// TODO: check on if we could enforce some kind of ordering of the process. maintenance should take times, and two consecutive maintenance job should not happen too soon than scheduling
// Now we do it by waiting for other controller's job to be fully dequeued. 
proctype maintenance(short p)
{
	short i = 1;
	for (i : 1 .. NODE_NUM) {
		if 
			:: nodes[i].status == 1 && nodes[i].maintained == 0 && cur_node_in_maintenance < p  ->
				cur_node_in_maintenance ++;
				printf("[***] %d node is in maintenance\n", cur_node_in_maintenance);
				run maintenanceNode(i);
		fi;
	}
}

proctype maintenanceNode(short i)
{
	atomic {
		printf("[**] Starting maintenance for node %d\n", i)
		nodes[i].status = 0;
		ncQueue[ncTail] = i;
		ncTail ++;
	}	// This condition is hard coded, meaning to wait for the node to fully shut down, and then put it back.
	if 
		:: nodes[i].numPod == 0 && sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail ->
			atomic {
				nodes[i].status = 1;
				nodes[i].maintained = 1;
				cur_node_in_maintenance --;
				printf("[**] End maintenance for node %d\n", i)
			}
	fi;
}

proctype nodeFailure(short i)
{
	nodes[i].status = 0;
	ncQueue[ncTail] = i;
	ncTail ++;
	nodes[i].status = 1;
}

proctype podCpuChangeWithPattern(short i)
{
	short cur_pod_template_id = pods[i].podTemplateId;
	do 
		::  pods[i].status == 1 && pods[i].curCpuIndex < podTemplates[cur_pod_template_id].maxCpuChange ->
			atomic{
				short cpu_change = podTemplates[cur_pod_template_id].curCpuRequest[pods[i].curCpuIndex] - pods[i].cpu
				updatePodCpuUsageOnNode(i, cpu_change);
				pods[i].curCpuIndex ++;

				if 
					:: pods[i].workloadType == 1 ->
						hpaQueue[hpaTail] = pods[i].workloadId;
						hpaTail ++;
					:: else ->;
				fi;
			}
	od;
}

proctype eventCpuChange(short targetDeployment)
{
	short cpu_change = 0, pod_selected = 0, index_selected = 0;
	bit direction = 0;
	short i = 0, j = 0, k = 0;

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
			
			updatePodCpuUsageOnNode(pod_selected, cpu_change)

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