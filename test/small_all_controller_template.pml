#define POD_NUM [$POD_NUM]
#define NODE_NUM [$NODE_NUM]
#define ZONE_NUM 2
#define DEBUG 0

// descheduler
#define MAX_DUPLICATE_REPLICA 1

// hpa
#define HPA_THRE 4
#define HPA_TOLERANCE 1
#define POD_CPU_THRE 12
#define MIN_REPLICAS 2
#define MAX_REPLICAS [$MAX_REPLICAS]

// scheduler
#define SCHEDULER_THRE_NODE 1
#define SCHEDULER_THRE_ZONE 1

/*
c_code {
	\#include <math.h>
}
*/

typedef node_type {
	short id;
	short zone;
	unsigned cpu : 6;
	unsigned cpu_left : 6;
	short score;
	bit status;
	short pod_num;
}

typedef pod_type {
	short id;
	short loc;
	bit status;
	short cpu;
	short score;
	short num_deschedule;
}

int zone_num_pod[ZONE_NUM+1];
node_type node[NODE_NUM+1];
pod_type pod[POD_NUM+1];
// int event_choice;
bit pod_cpu_change_status;
//short expected_cpu_change;
//unsigned num_pod_to_schedule : 3;
short pod_total;
short pod_num_exp;

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

			printf("[****]CPU change %d on pod %d\n", cpu_change, pod_selected);

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


proctype hpa()
{
	int i;
	int pod_total_thre, pod_total_thre_tolence_upper, pod_total_thre_tolence_lower;
	int cpu_usage_total;

	do
	:: (pod_cpu_change_status == 1) ->
		atomic{
			// let's keep everything in int for now. in fact, the HPA_TOLERENCE can be float
			pod_total_thre = pod_total*HPA_THRE;
			pod_total_thre_tolence_upper = pod_total*(HPA_THRE+HPA_TOLERANCE);
			pod_total_thre_tolence_lower = pod_total*(HPA_THRE-HPA_TOLERANCE);

			i = 1;
			cpu_usage_total = 0;

			do
			:: i < POD_NUM + 1 ->
				cpu_usage_total = cpu_usage_total + (pod[i].cpu * pod[i].status);
				i++;
			:: else ->
				break;
			od;

			printf("[****]cpu_usage_total %d\n", cpu_usage_total);

			if 
			:: cpu_usage_total > pod_total_thre ->
				printf("[****]cpu_usage_total: %d\n", cpu_usage_total);

				if 
				:: cpu_usage_total > pod_total_thre_tolence_upper ->
						 pod_num_exp = cpu_usage_total/HPA_THRE;
						 printf("[****]HPA capture pod number change: %d %d\n", pod_num_exp, pod_total);
				:: else -> pod_num_exp = pod_total;
				fi;

						 // TODO: 1) divide  2) think about pod_exp_change v.s. num_pod_to_schedule
			:: cpu_usage_total < pod_total_thre ->
				if
				:: cpu_usage_total < pod_total_thre_tolence_lower ->
						 pod_num_exp = (cpu_usage_total/HPA_THRE)+1;
						 printf("[****]HPA capture pod number change: %d %d\n", pod_num_exp, pod_total);
				:: else -> pod_num_exp = pod_total;
				fi;
			:: else -> pod_num_exp = pod_total;
			fi;

			if
			:: pod_num_exp < MIN_REPLICAS -> pod_num_exp = MIN_REPLICAS;
			:: pod_num_exp > MAX_REPLICAS -> pod_num_exp = MAX_REPLICAS;
			:: else -> ;
			fi;

			printf("[****][HPA] pod_exp, pod_total: %d, %d\n", pod_num_exp, pod_total);
			pod_cpu_change_status = 0;

			i = 0;
			pod_total_thre = 0;
			pod_total_thre_tolence_upper = 0;
			pod_total_thre_tolence_lower = 0;
			cpu_usage_total = 0;
		}
	od;
}

proctype scheduler()
{
	short pod_selected, j, i;
	short node_selected;
	bit flag;
	int max;

	do
	:: (pod_num_exp>pod_total) -> 
		printf("[****]Starting scheduler, %d, %d\n", pod_num_exp, pod_total)
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

			printf("[****]Pod %d is scheduled on node %d, with score %d\n", pod_selected, node_selected, max);

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

inline test_duplication()
{
	atomic {
	i = 1; 
	do
	:: i < NODE_NUM + 1 ->
		if
			:: node[i].pod_num > MAX_DUPLICATE_REPLICA -> break;
			:: else->;
		fi;
		i++
	:: else -> goto L4;
	od;
	}
}


proctype descheduler()
{
	short pod_selected, i, max;

	// not to implement more complicated pod filtering for now; 
L4:	do
	:: 	test_duplication() -> 
		printf("[****]There's duplicated pods more than %d on node.\n", MAX_DUPLICATE_REPLICA);
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
			printf("[****][descheduler] removing pod %d from node %d...\n", pod_selected, pod[pod_selected].loc)
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


proctype deployment_controller()
{
	short pod_selected, i, max;

	// not to implement other functionality for deployment controller for now

	// not to implement more complicated pod filtering for now; 
	// delete one pod at one time, can't do batch now
	do
	:: (pod_num_exp<pod_total) -> 
		printf("[****]Starting the deployment controller to delete pods, %d, %d\n", pod_num_exp, pod_total);
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
						printf("[****]pod score %d: %d; max: %d", i, pod[i].score, max);
					:: else->;
				fi;
				i++
			:: else -> break;
			od;

			// not processed the case where there's no pod left, which should be elimited becase of the pre-condition pod_num_exp<pod_total
			// deleting the pod
			printf("[****][deployment] removing pod %d from node %d...\n", pod_selected, pod[pod_selected].loc)
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

init {
	short i = 0;
	atomic {

		// initialize node
		node[0].status = 0;

		i = 1;
		do 
		:: i < NODE_NUM + 1 ->
			node[i].id = i;
			node[i].cpu_left = 12;
			node[i].cpu = 12;
			node[i].score = 0;
			node[i].status = 1;
			node[i].pod_num = 0;
			node[i].zone = 0;
			i++;
		:: else -> break
		od

		i = 1;
		do
		:: i < NODE_NUM / 2 + 1 ->
			node[i].zone = 1;
			i++;
		:: else -> break
		od

		do
		:: i < NODE_NUM + 1 ->
			node[i].zone = 2;
			i++;
		:: else -> break
		od

		// initialize pod
		pod[0].status = 0;

		i = 1;
		do
		:: i < POD_NUM+1 -> 
			pod[i].id = i;
			pod[i].status = 1;
			pod[i].cpu = 3;
			pod[i].score = 0;
			pod[i].num_deschedule = 0;
			i++;
		:: else -> break
		od

		//// init location
		pod[1].loc = NODE_NUM / 2 + 1
		i = 2;
		do
		:: i <= POD_NUM / 2 -> 
			pod[i].loc = i/2;
			i++;
		:: else -> break
		od

		do
		:: i < POD_NUM -> 
			pod[i].loc = i/2+1;
			i++;
		:: else -> break
		od

		do
		:: i < POD_NUM+1 ->
			pod[i].status = 0;
			// now all the new request the same CPU
			pod[i].cpu = 2;
			pod[i].loc = 0;
			i++;
		::else -> break;
		od;

		pod_total = POD_NUM - 1;
		pod_num_exp = POD_NUM - 1;

		// initialize pod number on zone and node
		i = 1;
		do 
		:: i < ZONE_NUM + 1 ->
			zone_num_pod[i] = 0;
			i++;
		:: else -> break;
		od;

		i = 1;
		do
		:: i < POD_NUM + 1 ->
			node[pod[i].loc].pod_num++;
			node[pod[i].loc].cpu_left = node[pod[i].loc].cpu_left - pod[i].cpu;
			i++;
		:: else -> break;
		od;

		i = 1;
		do
		:: i < NODE_NUM + 1 ->
			zone_num_pod[node[i].zone] = node[i].pod_num + zone_num_pod[node[i].zone];
			i++;
		:: else -> break;
		od;


		pod_cpu_change_status = 1;
		// expected_cpu_change = 1;
		// num_pod_to_schedule = 0;


		printf("[****]After init...\n");
		i = 1;
		do 
		:: i < ZONE_NUM + 1 ->
			printf("[****]zone %d: %d\n", i, zone_num_pod[i]);
			i++;
		:: else -> break;
		od;

		i = 1;
		do
		:: i < NODE_NUM + 1 ->
			printf("[****]Node %d: %d, cpu left %d\n", i, node[i].pod_num, node[i].cpu_left);
			i++;
		:: else -> break;
		od;
	}

	run event_cpu_change();
	run hpa();
	run scheduler();
	// run deployment_controller();
	//run descheduler()
}

// ltl {(<>[](env_change == 0)) -> (<>[](stable == 1))}
