

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

inline updatePodIds(replicaset, curPod)
{
	atomic{
		short m = 0;

		do
		:: m < MAX_POD*10 ->
			if
				:: (replicaset.podIds[m] == 0) || (pods[replicaset.podIds[m]].status == 0)
					printf("[***]Adding curPod %d to index %d in replicaset %d", curPod, m, replicaset.id)
					replicaset.podIds[m] = curPod;
					break;
				:: else ->;
			fi;
			m++;
		:: else->
			printf("[*Warning]Max number of pod reached in pod list of replicaset");
		od;
	}
}

inline copyDeploymentInfoToPod(pod, curD)
{
	atomic{
		pod.status = 1;
		pod.workloadType = 1;
		pod.workloadId = curD;
		pod.loc = 0;
		pod.score = 0;
		pod.cpu = podTemplates[d[curD].podTemplateId].cpuRequested;
		pod.memory = podTemplates[d[curD].podTemplateId].memRequested;
		pod.important = 0;
		pod.podTemplateId = d[curD].podTemplateId;
	}
}

inline printfNodeScore()
{
	printf("[****]Printing score for the current plugin...\n");

	i = 1;

	do
	:: i < NODE_NUM + 1 ->
	   printf("[****]Node %d, score: %d, curScore: %d\n", i, nodes[i].score, nodes[i].curScore)
	   i++;
	:: else->break;
	od;
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




