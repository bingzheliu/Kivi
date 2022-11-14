// hpa

#define HPA_THRE 4
#define HPA_TOLERANCE 1
#define POD_CPU_THRE 12
#define MIN_REPLICAS 2
#define MAX_REPLICAS [$MAX_REPLICAS]


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

			printf("cpu_usage_total %d\n", cpu_usage_total);

			if 
			:: cpu_usage_total > pod_total_thre ->
				printf("cpu_usage_total: %d\n", cpu_usage_total);

				if 
				:: cpu_usage_total > pod_total_thre_tolence_upper ->
						 pod_num_exp = cpu_usage_total/HPA_THRE;
						 printf("HPA capture pod number change: %d %d\n", pod_num_exp, pod_total);
				:: else -> pod_num_exp = pod_total;
				fi;

						 // TODO: 1) divide  2) think about pod_exp_change v.s. num_pod_to_schedule
			:: cpu_usage_total < pod_total_thre ->
				if
				:: cpu_usage_total < pod_total_thre_tolence_lower ->
						 pod_num_exp = (cpu_usage_total/HPA_THRE)+1;
						 printf("HPA capture pod number change: %d %d\n", pod_num_exp, pod_total);
				:: else -> pod_num_exp = pod_total;
				fi;
			:: else -> pod_num_exp = pod_total;
			fi;

			if
			:: pod_num_exp < MIN_REPLICAS -> pod_num_exp = MIN_REPLICAS;
			:: pod_num_exp > MAX_REPLICAS -> pod_num_exp = MAX_REPLICAS;
			:: else -> ;
			fi;

			printf("[HPA] pod_exp, pod_total: %d, %d\n", pod_num_exp, pod_total);
			pod_cpu_change_status = 0;

			i = 0;
			pod_total_thre = 0;
			pod_total_thre_tolence_upper = 0;
			pod_total_thre_tolence_lower = 0;
			cpu_usage_total = 0;
		}
	od;
}