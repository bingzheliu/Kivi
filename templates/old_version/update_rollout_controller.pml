#define EDGE_NUM 5
#define NODE_NUM 5
#define MAX_SURGE 1
#define LINK_FAILURE 2
#define MIN_NODE 1


typedef node_type {
	short id;
	short zone;
	unsigned cpu : 6;
	unsigned cpu_left : 6;
	short score;
	bit status;
	short pod_num;
	bit updated;
}

typedef edge_type {
	short id;
	short node_id[2];
	bit status;
	bit can_fail;
}

edge_type edge[EDGE_NUM+1];
node_type node[NODE_NUM+1];


inline need_update() {
	atomic {
		i = 1;
		do 
		:: i < NODE_NUM + 1 ->
			if
			:: node[i].updated == 0 -> break;
			:: else ->;
			fi;
			i++;
		:: else -> goto UC1;
		od;

		i = 0;
	}
}

proctype update_rollout() {
	short i = 0, index = 0;
	short node_to_update[MAX_SURGE];

UC1:	do
		:: need_update() ->
			atomic {
				index = 0;
				i = 1;

				do 
				:: i < NODE_NUM + 1 ->
					if
					:: index >= MAX_SURGE -> break;
					:: else->;
					fi;

					if
					:: node[i].updated == 0 ->
						node_to_update[index] = i;
						index++;
					:: else ->;
					fi;
					i++;
				:: else -> break;
				od;

				i = 0;
				do
				:: i < MAX_SURGE -> 
					node[node_to_update[i]].status = 0;
					printf("Taking down node %d\n", node_to_update[i]);
					i++;
				:: else -> break;
				od;


				i = 0;
				index = 0;
			}

			atomic {
				do
				:: i < MAX_SURGE -> 
					node[node_to_update[i]].updated = 1;
					printf("Updating node %d\n", node_to_update[i]);
					i++;
				:: else -> break;
				od;
				i = 0;
			}

			do
			:: i < MAX_SURGE -> 
				node[node_to_update[i]].status = 1;
				printf("Starting node %d\n", node_to_update[i]);
				i++;
			:: else -> break;
			od;

			i = 0;
		od;
}

inline link_can_fail() {
	atomic {
		i = 1;
		link_failure_count = 0;
		do
		:: i < EDGE_NUM + 1 -> 
			if
			:: edge[i].status == 0->
				link_failure_count++;
			:: else->;
			fi;
			i++;
		:: else -> break;
		od;

		if
		:: link_failure_count >= LINK_FAILURE -> goto LF1;
		:: else ->;
		fi;


		i = 0;
		link_failure_count = 0;
	}

}

proctype link_failure() {
	short i = 0, link_failure_count = 0, selected_edge = 0;

LF1:	do
		:: link_can_fail() -> 
			atomic {
				// TODO: if the code continue to select an edge that already down, we may go into a loop. 
				select(selected_edge : 1 .. EDGE_NUM);

				if
				:: edge[selected_edge].status == 1 && edge[selected_edge].can_fail == 1 ->
					edge[selected_edge].status = 0;
				:: else ->;
				fi;

				printf("Taking down link %d\n", selected_edge);

				selected_edge = 0;
				link_failure_count = 0;
				i = 0;
			}
		od;
}

// using this could make the result hard to read!
proctype monitor() {
	do
	:: (edge[2].status & node[3].status) + (edge[3].status & node[4].status) + ((edge[4].status & edge[2].status) | (edge[5].status & edge[3].status) & node[5].status) + (edge[1].status & node[1].status) < MIN_NODE -> assert(false);
	:: else;
	od;
}

init {
	short i = 0;
	atomic {
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
			node[i].updated = 0;
			i++;
		:: else -> break;
		od;

		i = 1;
		do 
		:: i < EDGE_NUM + 1 ->
			edge[i].id = i;
			edge[i].status = 1;
			edge[i].can_fail = 1;
			i++;
		:: else -> break;
		od;

		// topology looks like the following, 1 is the entrance of the requests:
		//    1
		//    |
		//    2
		//   / \
		//  3   4
		// 	 \ /
		//    5 
		edge[1].node_id[0] = 1;
		edge[1].node_id[1] = 2;
		edge[2].node_id[0] = 2;
		edge[2].node_id[1] = 3;
		edge[3].node_id[0] = 2;
		edge[3].node_id[1] = 4;
		edge[4].node_id[0] = 3;
		edge[4].node_id[1] = 5;
		edge[5].node_id[0] = 4;
		edge[5].node_id[1] = 5;

		run monitor();
	}

	run update_rollout();
	run link_failure();

}

