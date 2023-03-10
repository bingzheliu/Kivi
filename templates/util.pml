

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
					printf("[****]Adding curPod %d to index %d in replicaset %d", curPod, m, replicaset.id)
					replicaset.podIds[m] = curPod;
					break;
				:: else ->;
			fi;
			m++;
		:: else->
			printf("[****]Max number of pod reached in pod list of replicaset");
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




