// from small_all_controller_template

#define POD_NUM [$POD_NUM]
#define NODE_NUM [$NODE_NUM]
#define ZONE_NUM 2
#define DEBUG 0



int zone_num_pod[ZONE_NUM+1];
node_type node[NODE_NUM+1];
pod_type pod[POD_NUM+1];
// int event_choice;
bit pod_cpu_change_status;
//short expected_cpu_change;
//unsigned num_pod_to_schedule : 3;
short pod_total;
short pod_num_exp;



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


		printf("After init...\n");
		i = 1;
		do 
		:: i < ZONE_NUM + 1 ->
			printf("zone %d: %d\n", i, zone_num_pod[i]);
			i++;
		:: else -> break;
		od;

		i = 1;
		do
		:: i < NODE_NUM + 1 ->
			printf("Node %d: %d, cpu left %d\n", i, node[i].pod_num, node[i].cpu_left);
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
