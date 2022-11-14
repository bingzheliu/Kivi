// scheduler
#define SCHEDULER_THRE_NODE 1
#define SCHEDULER_THRE_ZONE 1




proctype scheduler()
{
	short pod_selected, j, i;
	short node_selected;
	bit flag;
	int max;

	do
	:: (pod_num_exp>pod_total) -> 
		printf("Starting scheduler, %d, %d\n", pod_num_exp, pod_total)
		atomic{
			// assign a pod data structure to the new pod
			i = 1;
			do
			:: i < POD_NUM+1 ->
				if 
					:: pod[i].status == 0 ->
						pod_selected = i;
						break;
					:: else->;
				fi;
				i++
			:: else -> break;
			od;
			// TODO: not implement when there's no pod avaiable

			// score all the node
			i = 1;
			do
			:: i < NODE_NUM+1 ->
				flag = 0;

				if 
				:: node[i].cpu_left < pod[pod_selected].cpu ->
					flag = 1;
					goto L2;
				:: else->;
				fi;

				j = 1;
				do 
				:: j < NODE_NUM+1 ->
						if
						:: (node[i].pod_num - node[j].pod_num >= SCHEDULER_THRE_NODE)  ->
								flag = 1;
								goto L2;
						:: else->;
						fi;
						j++;
				:: else -> break;
				od

				j = 1;
				do 
				:: j < ZONE_NUM+1 ->
						if
						:: zone_num_pod[node[i].zone] - zone_num_pod[j] >= SCHEDULER_THRE_ZONE ->
								flag = 1;
								goto L2;
						:: else->;
						fi;
						j++;
				:: else -> break;
				od


L2:				if 
				:: flag > 0 ->
						node[i].score = 0;
				:: else ->
						node[i].score = node[i].cpu_left*5 - node[i].pod_num*1;
				fi;

				i++
			:: else -> break;
			od;

			// find the node with the max score
			max = 0;
			i = 1;
			do
			:: i < NODE_NUM+1 ->
				if 
				:: node[i].status > 0 && node[i].score > max ->
						max = node[i].score;
				:: else->;
				fi
				i++;
			:: else -> break;
			od
			
			assert(max > 0);

			node_selected = 0;
			i = 1;
			do
			:: i < NODE_NUM+1 ->
				if 
				:: node[i].status > 0 && node[i].score == max ->
						node_selected = i;
						break;
				:: else->;
				fi;
				i++;
			:: else -> break;
			od
			// not deal with no node meeting with expectation

			printf("Pod %d is scheduled on node %d, with score %d\n", pod_selected, node_selected, max);

			node[node_selected].pod_num++;
			node[node_selected].cpu_left = node[node_selected].cpu_left - pod[pod_selected].cpu;
			pod[pod_selected].loc = node[node_selected].id;
			pod[pod_selected].status = 1;
			pod_total++;
			zone_num_pod[node[node_selected].zone]++;

			pod_cpu_change_status = 1;


			i = 0;
			pod_selected = 0;
			j = 0;
			node_selected = 0;
			flag = 0;
			max = 0;
		}
	od;
}
