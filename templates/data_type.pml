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