

inline test_duplication()
{
	atomic {
	short m = 1; 
	do
	:: m < NODE_NUM + 1 ->
		if
			:: node[m].pod_num > MAX_DUPLICATE_REPLICA -> break;
			:: else->;
		fi;
		m++
	:: else -> goto L4;
	od;
	}
}


// a = min(b,c)
inline min(a, b, c)
{
	atomic {
		a = b;
		if
		:: b > c -> a = c;
		:: else->;
		fi;
	}
}

inline replicasetAddPod(replicaset, curPod)
{
	atomic{
		// short m = 0;

		// do
		// :: m < MAX_POD*10 ->
		// 	if
		// 		:: (replicaset.podIds[m] == 0) || (pods[replicaset.podIds[m]].status == 0)
		// 			printf("[***]Adding curPod %d to index %d in replicaset %d\n", curPod, m, replicaset.id)
		// 			replicaset.podIds[m] = curPod;
		// 			break;
		// 		:: else ->;
		// 	fi;
		// 	m++;
		// :: else->
		// 	printf("[*Warning]Max number of pod reached in pod list of replicaset\n");
		// od;
		replicaset.podIds[replicaset.replicas] = curPod;
		replicaset.replicas++;
		printPodIds(replicaset)
	}
}

inline replicasetDeletePod(replicaset, curPod)
{
	atomic{
		d_step{
			short m = 0;

			do 
				:: m < replicaset.replicas -> 
					if 
						:: replicaset.podIds[m] == curPod->
							for(m : m .. replicaset.replicas-2) {
								replicaset.podIds[m] = replicaset.podIds[m+1];
							}
							break;
						:: else->
					fi;
					m++
				:: else->
					printf("[*error] Problematic pod Id updates!\n")
			od;			

			replicaset.replicas--;
			printPodIds(replicaset)
		}
	}
}

inline printPodIds(replicaset)
{
	atomic{
		d_step{
			printf("[*****] Updated Replicaset %d with %d replicas, podIds: ", replicaset.id, replicaset.replicas);
			short _i = 0
			for(_i : 0 .. replicaset.replicas-1) {
				printf("%d ", replicaset.podIds[_i])
			}
			printf("\n");
		}
	}
}

inline copyDeploymentInfoToPod(pod, curD)
{
	atomic{
		// pod.status = 1;
		pod.workloadType = 1;
		pod.workloadId = curD;
		pod.loc = 0;
		pod.score = 0;
		pod.cpu = podTemplates[d[curD].podTemplateId].cpuRequested;
		pod.memory = podTemplates[d[curD].podTemplateId].memRequested;
		pod.important = 0;
		pod.podTemplateId = d[curD].podTemplateId;
		pod.curCpuIndex = 0;
	}
}

inline printfNodeScore()
{
	atomic{
		printf("[****]Printing score for the current plugin...\n");

		short m = 1;

		for (m : 1 .. NODE_NUM) {
		   printf("[****]Node %d, score: %d, curScore: %d\n", m, nodes[m].score, nodes[m].curScore)
		}
	}
}

// We do a round on the log result; the source code mentioned: Since <size> is at least 1 (all nodes that passed the Filters are in the
// same topology), and k8s supports 5k nodes, the result is in the interval <1.09, 8.52>.
inline logTable(a, b)
{
	atomic{
		d_step{
			if 
				:: a == 1 -> b = 0;
				:: a >= 2 && a < 5 -> b = 1;
				:: a >= 5 && a < 13 -> b = 2;
				:: a >= 13 && a < 34 -> b = 3;
				:: a >= 34 && a < 91 -> b = 4;
				:: a >= 91 && a < 245 -> b = 5;
				:: a >= 245 && a < 666 -> b = 6;
				:: a >= 666 && a < 1809 -> b = 7;
				:: a >= 1809 && a < 4915 -> b = 8;
				:: else -> b = 9;
			fi;
		}
	}
}

inline updatePodCpuUsageOnNode(pod_selected, cpu_change)
{
	atomic{
		d_step{
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
		}
	}
}

// update the queue without adding duplicated items
// Initially, all items in the queue is 0
// The queue is a rotation queue. and can only store the event of MAX_QUEUE_SIZE
inline updateQueue(queue, tail, index, item)
{
	atomic{
		d_step {
			if 
				:: item == 0 ->
					printf("[*Internal error] Item put to queue shoudn't be 0!")
					assert(false)
				:: else->
			fi;

			short _tail;
			if 
				:: tail == 0 -> 
					_tail = MAX_QUEUE_SIZE-1
				:: else->
					_tail = tail - 1
			fi;
			if
				:: queue[_tail] != item ->
					queue[tail] = item
					if
						:: tail == MAX_QUEUE_SIZE-1->
							tail = 0
						:: else->
							tail ++
					fi
					if 
						:: tail == index ->
							printf("[*Internal error] Queue is full, increase queue size!")
							assert(false)
						:: else->
					fi
				:: else->
			fi

		}
	}
}




