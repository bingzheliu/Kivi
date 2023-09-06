// This need to be automatically populated according to user's intents
// Check for H2
// never {
// 	do
// 	:: d[1].replicas < d[1].hpaSpec.minReplicas -> break
// 	:: else
// 	od;
// }


// never {
// 	do
// 	:: maxSkewNode > 1 -> break;
// 	od;
// }

// An issue: the init stage also would look into this never, which can cause unexpected problem


// Check for H1
proctype checkOscillation(byte did)
{
endCH11:	if 
			:: d[did].hpaSpec.maxReplicas != d[did].hpaSpec.minReplicas && d[did].replicas == d[did].hpaSpec.maxReplicas && !loadChange ->
		 	printf("[**] Entering stage 2 for check!\n")
endCH12:	if 
		 		:: d[did].replicas == d[did].hpaSpec.minReplicas || d[did].replicas <= d[did].hpaSpec.maxReplicas - 3 ->
		 			printf("[*] The number of replicas was oscillating, now %d\n", d[did].replicas)
		 			assert(false)
		 		fi;
			fi;
}

proctype checkMinReplicas(byte did)
{
	if 
		// if it's invalid end state at the following sentence, it's a violation as well, meaning the replicas is never more than the minReplicas
		:: init_status == 1 && ((d[did].hpaSpec.isEnabled && d[did].replicas >= d[did].hpaSpec.minReplicas) || (!d[did].hpaSpec.isEnabled && d[did].replicas >= d[did].specReplicas)) ->
			printf("[**] Entering stage 2 for check! The deployment is table...\n")
endCMR1:	if 
				:: ((d[did].hpaSpec.isEnabled && d[did].replicas < d[did].hpaSpec.minReplicas) || (!d[did].hpaSpec.isEnabled && d[did].replicas < d[did].specReplicas)) ->
					printf("[*] The number of replicas in deployment %d is less than the minium/spec replicas! Now %d.\n", did, d[did].replicas);
					assert(false)
			fi;
	fi;
}

proctype checkExpReplicas(byte did)
{
	if 
		// if it's invalid end state at the following sentence, it's a violation as well, meaning the replicas is never more than the minReplicas
		:: init_status == 1 && (d[did].replicas >= [$expReplicas]) ->
			printf("[**] Entering stage 2 for check! The deployment is table...\n")
endCER1:	if 
				::d[did].replicas < [$expReplicas] ->
					printf("[*] The number of replicas in deployment %d is less than the expected replicas! Now %d, expected %d.\n", did, d[did].replicas, [$expReplicas]);
					assert(false)
			fi;
	fi;
}

// if no enviromental change, the # of replicas should not reach the upper bound.
// This can be checked for H1
// never  {    /* ([](!q -> !p))  q-> envchange, p -> (d[1].replicas == d[1].maxReplicas)*/
// accept_init:
// T0_init:
// 	do
// 	:: ((!envChange) || (d[1].replicas == d[1].hpaSpec.maxReplicas)) -> goto T0_init
// 	od;
// }



// check for S6
// proctype checkS6()
// {
// endCS61:	if 
// 			::  init_status == 1 && d[1].replicas == d[1].specReplicas ->
// 		 		printf("[*] Entering stage 2 for check!\n")
// endCS62:		if 
// 			 		:: d[1].replicas < d[1].specReplicas - 1 ->
// 			 			printf("[*] The number of replicas %d below the (spec - 1) %d\n", d[1].replicas, d[1].specReplicas)
// 			 			assert(false)
// 			 	fi;
// 	fi;
// }

// check for H2
// proctype checkH2()
// {
// endCH21:	if 
// 			::  init_status == 1 && d[1].replicas == d[1].hpaSpec.maxReplicas && d[1].hpaSpec.maxReplicas != d[1].hpaSpec.minReplicas->
// 		 		printf("[**] Entering stage 2 for check!\n")
// endCH22:		if 
// 			 		::d[1].replicas < d[1].hpaSpec.maxReplicas ->
// 			 			printf("[**] Entering stage 3 for check!\n")
// endCH23:			 	if 
// 			 				:: d[1].replicas == d[1].hpaSpec.maxReplicas ->
// 					 			// printf("[*] The number of replicas %d below the minReplicas %d\n", d[1].replicas, d[1].hpaSpec.minReplicas)
// 					 			printf("[*] The number of replicas was oscillating, now %d\n", d[1].replicas)
// 					 			assert(false)
// 					 	fi;
// 			 	fi;
// 	fi;
// }

proctype checkS1()
{
	byte count = 0;
endCS11: if 
			:: d[1].replicasInDeletion > 0 ->
endCS12:		if 
					:: d[1].replicasInCreation > 0 ->
						count ++
endCS13:				if 
							:: count >= LOOP_TIMES ->
								printf("[*] Pods are being scheduled and descheduled in deployment 1!\n")
								assert(false)
							:: else->;
						fi;
endCS14:				if 
							:: d[1].replicasInDeletion == 0 ->
								goto endCS11;
						fi;
				fi;
		 fi
}

proctype checkEvictionCycle(short i)
{
	byte count = 0;
	short last_in_deletion, last_in_creation;
	last_in_deletion = 0
	last_in_creation = 0
endCS11: if 
			:: d[i].replicasInDeletion > last_in_deletion ->
				last_in_deletion = d[i].replicasInDeletion;
endCS12:		if 
					:: d[i].replicasInCreation > last_in_creation ->
					    last_in_creation = d[i].replicasInCreation
					    printf("[*] Pods are being scheduled and descheduled in deployment 1, %d %d!\n", last_in_deletion, last_in_creation)
						count ++
endCS13:				if 
							:: count >= LOOP_TIMES ->
								printf("[*] Pods are being scheduled and descheduled in deployment 1!\n")
								assert(false)
							:: else->;
						fi;
endCS14:				if 
							:: d[i].replicasInDeletion < last_in_deletion && d[i].replicasInCreation < last_in_creation  ->
							 	printf("[*] Recount checkEvictionCycle, %d %d\n", last_in_deletion, last_in_creation)
								last_in_deletion = d[i].replicasInDeletion
								last_in_creation = d[i].replicasInCreation
								goto endCS11;
						fi;
				fi;
		 fi
	last_in_deletion = 0
	last_in_creation = 0
}

// // Previous check for H2, and this version only look into the mismatch between minReplicas of HPA and current replicas
// proctype checkH2()
// {
// endCH21:	if 
// 			::  init_status == 1 && d[1].replicas == d[1].specReplicas ->
// 		 		printf("[*] Entering stage 2 for check!\n")
// endCH22:		if 
// 			 		:: d[1].replicas < d[1].hpaSpec.minReplicas ->
// 			 			printf("[*] The number of replicas %d below the minReplicas %d\n", d[1].replicas, d[1].hpaSpec.minReplicas)
// 			 			assert(false)
// 			 	fi;
// 	fi;
// }