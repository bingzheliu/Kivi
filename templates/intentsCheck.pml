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
proctype checkH1()
{
endCH11:	if 
			:: d[1].hpaSpec.maxReplicas != d[1].hpaSpec.minReplicas && d[1].replicas == d[1].hpaSpec.maxReplicas ->
		 	printf("[*] Entering stage 2 for check!\n")
endCH12:		if 
		 		:: d[1].replicas == d[1].hpaSpec.minReplicas || d[1].replicas < d[1].hpaSpec.maxReplicas - 5 ->
		 			printf("[*] The number of replicas was oscillating, now %d\n", d[1].replicas)
		 			assert(false)
		 	fi;
	fi;
}

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
proctype checkH2()
{
endCH21:	if 
			::  init_status == 1 && d[1].replicas == d[1].hpaSpec.maxReplicas && d[1].hpaSpec.maxReplicas != d[1].hpaSpec.minReplicas->
		 		printf("[*] Entering stage 2 for check!\n")
endCH22:		if 
			 		::d[1].replicas < d[1].hpaSpec.maxReplicas ->
			 			printf("[*] Entering stage 3 for check!\n")
endCH23:			 	if 
			 				:: d[1].replicas == d[1].hpaSpec.maxReplicas ->
					 			// printf("[*] The number of replicas %d below the minReplicas %d\n", d[1].replicas, d[1].hpaSpec.minReplicas)
					 			printf("[*] The number of replicas was oscillating, now %d\n", d[1].replicas)
					 			assert(false)
					 	fi;
			 	fi;
	fi;
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