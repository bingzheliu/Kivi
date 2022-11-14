// This is the accurate LB model without the division estimation

#define A 3
#define THRE 22

int a_load, b_load;
bit changed;
int w_a_s1, w_a_s2, w_b_s2, w_b_s3;
int steps;

int w_a_s1_temp, w_a_s2_temp, w_b_s2_temp, w_b_s3_temp;
int a_s1_load, a_s2_load, b_s2_load, b_s3_load;
int next_w_a_s1, next_w_a_s2, next_w_b_s2, next_w_b_s3;

int a_s1_latency, a_s2_latency, b_s2_latency, b_s3_latency;

init {
	select(a_load:12..30);
	select(b_load:12..30);
	changed = 1;

	w_a_s1 = 50;
	w_a_s2 = 50;
	w_b_s2 = 50;
	w_b_s3 = 50;


	steps = 1;
	do
	:: changed == 1  ->
			a_s1_load = (a_load*w_a_s1)/100;
			a_s2_load = a_load - a_s1_load;
			b_s2_load = (b_load*w_b_s2)/100;
			b_s3_load = b_load - b_s2_load;

			
			a_s1_latency = 3 * a_s1_load + b_s2_load + 3;
			a_s2_latency = 3 * a_s2_load + b_s2_load + 3;
			b_s2_latency = 3 * b_s2_load + a_s1_load + a_s2_load + 3;
			b_s3_latency = 3 * b_s3_load + 3;

			w_a_s1_temp = (w_a_s1 + A * (1 - a_s1_latency + THRE));
			w_a_s2_temp = (w_a_s2 + A * (1 - a_s2_latency + THRE));
			w_b_s2_temp = (w_b_s2 + A * (1 - b_s2_latency + THRE));
			w_b_s3_temp = (w_b_s3 + A * (1 - b_s3_latency + THRE));

			if
			:: a_s1_latency > THRE -> 
				if
				:: w_a_s1_temp < 0 -> w_a_s1_temp = 0;
				:: else ->;
				fi;
			:: else -> w_a_s1_temp = w_a_s1;
			fi;

			if
			:: a_s2_latency > THRE -> 
				if
				:: w_a_s2_temp < 0 -> w_a_s2_temp = 0;
				:: else ->;
				fi;
			:: else -> w_a_s2_temp = w_a_s2;
			fi;

			if
			:: b_s2_latency > THRE -> 
				if
				:: w_b_s2_temp < 0 -> w_b_s2_temp = 0;
				:: else ->;
				fi;
			:: else -> w_b_s2_temp = w_b_s2;
			fi;

			if
			:: b_s3_latency > THRE -> 
				if
				:: w_b_s3_temp < 0 -> w_b_s3_temp = 0;
				:: else ->;
				fi;
			:: else -> w_b_s3_temp = w_b_s3;
			fi;

			// w_a_s1_temp = a_s1_latency > THRE? (w_a_s1_temp >= 0? w_a_s1_temp : 0) : w_a_s1;
			// w_a_s2_temp = a_s2_latency > THRE? (w_a_s2_temp >= 0? w_a_s2_temp : 0) : w_a_s2;
			// w_b_s2_temp = b_s2_latency > THRE? (w_b_s2_temp >= 0? w_b_s2_temp : 0) : w_b_s2;
			// w_b_s3_temp = b_s3_latency > THRE? (w_b_s3_temp >= 0? w_b_s3_temp : 0) : w_b_s3;

			next_w_a_s1 = w_a_s1_temp*100/(w_a_s1_temp+w_a_s2_temp);
			next_w_a_s2 = 100-next_w_a_s1;
			next_w_b_s2 = w_b_s2_temp*100/(w_b_s2_temp+w_b_s3_temp);
			next_w_b_s3 = 100-next_w_b_s2;

			if 
			:: ((next_w_a_s1-w_a_s1) > 1 || (next_w_a_s2-w_a_s2) > 1 || (next_w_b_s2-w_b_s2) > 1 || (next_w_b_s3-w_b_s3) > 1 || (w_a_s1-next_w_a_s1) > 1 || (w_a_s2-next_w_a_s2) > 1 || (w_b_s2-next_w_b_s2) > 1 || (w_b_s3-next_w_b_s3) > 1) -> changed = 1;
			:: else -> changed = 0;
			fi;

			w_a_s1 = next_w_a_s1;
			w_a_s2 = next_w_a_s2;
			w_b_s2 = next_w_b_s2;
			w_b_s3 = next_w_b_s3;

			steps++;
			printf("%d: %d, %d, %d, %d, %d\n", steps, w_a_s1, w_a_s2, w_b_s2, w_b_s3, changed);
	:: else -> break;
	od
}

// ltl {(<>[](changed == 0))}