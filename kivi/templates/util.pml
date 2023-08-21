

inline test_duplication()
{
	atomic {
	short _m = 1; 
	do
	:: _m < NODE_NUM + 1 ->
		if
			:: node[_m].pod_num > MAX_DUPLICATE_REPLICA -> break;
			:: else->;
		fi;
		_m++
	:: else -> goto L4;
	od;
	}
	_m = 0;
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

// Note: need to add () to the variables, as they are just replaced directly by the compiler and can cause mistakes if without the ().
// a = b/c + 0.99
inline ceilEst(a, b, c)
{
	atomic{
		a = (99*(c)+100*(b))/(100*(c))
	}
}

// a = b/c
inline ceil(a, b, c)
{
	atomic{
		if 
			:: (b)%(c) == 0 ->
				a = (b)/(c)
			:: else->
				a = ((b)/(c)) + 1
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
		d[pods[curPod].workloadId].replicas++;
		//printPodIds(replicaset)
	}
}

inline replicasetDeletePod(replicaset, curPod)
{
	atomic{
		d_step{
			short _m = 0;
			_m = 0;
			do 
				:: _m < replicaset.replicas -> 
					if 
						:: replicaset.podIds[_m] == curPod->
							for(_m : _m .. replicaset.replicas-2) {
								replicaset.podIds[_m] = replicaset.podIds[_m+1];
							}
							replicaset.replicas--;
							d[pods[curPod].workloadId].replicas --;
							flag = 1
							break;
						:: else->
					fi;
					_m++
				:: else->;
					// Note: this may not be very rubust way. If not found the replica, the pod may be in pending
					if 
						:: d[pods[curPod].workloadId].replicasInCreation > 0 ->
							d[pods[curPod].workloadId].replicasInCreation --
							break
						:: else->
							printf("[*] Problematic pod Id updates!\n")
					fi;
			od;			
			
			_m = 0;
	
			// printPodIds(replicaset)
		}
	}
}

inline printPodIds(replicaset)
{
	atomic{
		d_step{
			short _m = 0;
			printf("[*****] Updated Replicaset %d with %d replicas, podIds: ", replicaset.id, replicaset.replicas);
			for(_m : 0 .. replicaset.replicas-1) {
				printf("%d ", replicaset.podIds[_m])
			}
			printf("\n");
			_m = 0;
		}
	}
}

inline copyDeploymentInfoToPod(pod, curD)
{
	atomic{
		d_step{
			// pod.status = 1;
			pod.workloadType = 1;
			pod.workloadId = curD;
			pod.loc = 0;
			pod.score = 0;
			if 
				:: podTemplates[d[curD].podTemplateId].maxCpuChange == 0 ->
					pod.cpu = podTemplates[d[curD].podTemplateId].cpuRequested;
				:: else->
					pod.cpu = podTemplates[d[curD].podTemplateId].curCpuRequest[0]
			fi;
			// The initial CPU value has been used. 
			pod.curCpuIndex = 1;

			// TBD: the memory may need also to have a change pattern. Assuming it's the request for now as we haven't model memory runtime behavior.
			pod.memory = podTemplates[d[curD].podTemplateId].memRequested;

			pod.important = 0;
			pod.podTemplateId = d[curD].podTemplateId;
			
			short _m = 0;
			for(_m : 0 .. MAX_LABEL-1) {
				pod.labelKeyValue[_m] = podTemplates[d[curD].podTemplateId].labelKeyValue[_m]
			}
			_m = 0;
		}
	}
}

inline printfNodeScore()
{
	atomic{
		printf("[*****]Printing score for the current plugin...\n");

		short _m = 1;
		for (_m : 1 .. NODE_NUM) {
		   printf("[*****]Node %d, score: %d, curScore: %d\n", _m, nodes[_m].score, nodes[_m].curScore)
		}
		_m = 0;
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

			printf("[*][CPU Change] cpu_change; %d; %d; CPU change %d on pod %d, now %d, and node %d, now %d\n",  pod_selected, cpu_change, cpu_change, pod_selected, pods[pod_selected].cpu, pods[pod_selected].loc, nodes[pods[pod_selected].loc].cpuLeft);
		}
	}
}

inline checkDuplicate(queue, tail, index, item, max_queue_size)
{
	short _index = 0;
	_index = index

	do 
		:: _index == tail -> break
		:: else ->
			if 
				:: queue[_index] == item -> 
					_flag = 1
					break
				:: else->
			fi

			if
				:: _index == max_queue_size-1->
					_index = 0
				:: else->
					_index ++
			fi
	od
	_index = 0
}

// update the queue without adding duplicated items
// Initially, all items in the queue is 0
// The queue is a rotation queue. and can only store the event of MAX_QUEUE_SIZE
inline updateQueue(queue, tail, index, item, max_queue_size)
{
	atomic{
		d_step {

			if 
				:: item == 0 ->
					printf("[*Internal error] Item put to queue shoudn't be 0!")
					assert(false)
				:: else->
			fi;

			// Disabling print out to save for system states
			// printQueue(queue, tail)
			// printf("[******] tail %d, index %d, item %d\n", tail, index, item)

			short _m = 0;
			if 
				:: tail == 0 -> 
					_m = max_queue_size-1
				:: else->
					_m = tail - 1
			fi;

			bit _flag = 0;
			_flag = 0;
			checkDuplicate(queue, tail, index, item, max_queue_size)
			if
				:: index == tail || _flag != 1 ->
					queue[tail] = item
					if
						:: tail == max_queue_size-1->
							tail = 0
						:: else->
							tail ++
					fi
					if 
						:: tail == index ->
							printf("[*Warning] Queue is full! Halt this process for now!")
							tail != index;
							printf("[*Warning] Queue size decreased!")
							// printf("[*Internal error] Queue is full, increase queue size!")
							// assert(false)
						:: else->
					fi
				:: else->
			fi
			 _m = 0;
			 _flag = 0;
	

			printQueue(queue, tail)
			// printf("[******] tail %d, index %d, item %d\n", tail, index, item)
		}
	}
}

inline printQueue(queue, tail) 
{
	atomic{
		d_step {
			printf("[******] Printing queue: ")
			for(_m : 0 .. tail) {
				printf("%d ", queue[_m])
			}
			printf("\n")
			_m = 0
		}
	}
}

inline updateQueueIndex(index, max_queue_size)
{
	atomic{
		d_step {
			if
				:: index == max_queue_size-1->
					index = 0
				:: else->
					index ++
			fi
		}
	}
}

inline clearArray(arrary, size)
{
	atomic{
		d_step{
			short _m = 0;
			for(_m : 0 .. size - 1){
				arrary[_m] = 0;
			}
			_m = 0;
		}
	}
}

// inline queueItemSize()
// {

// }




