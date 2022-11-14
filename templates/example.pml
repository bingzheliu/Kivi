







typedef pod_type {
	short id;
	short location;
	bit status;
	short cpu;
	...
}



proctype event_cpu_change() {
	...
}

proctype scheduler(){
	do
	:: (pod_num_exp>pod_total) -> 
		...
		assert(..);
	::
	od
	...
}


node_type node[NODE_NUM+1];
pod_type pod[POD_NUM+1];
init {
	...
	run scheduler();
	run event_cpu_change();
}
