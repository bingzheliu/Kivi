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
endCH1:	if 
			:: d[1].hpaSpec.maxReplicas != d[1].hpaSpec.minReplicas && d[1].replicas == d[1].hpaSpec.maxReplicas ->
		 	printf("[*] Entering stage 2 for check!\n")
endCH2:		if 
		 		:: d[1].replicas == d[1].hpaSpec.minReplicas || d[1].replicas < d[1].hpaSpec.maxReplicas - 5 ->
		 			printf("[*] The number of replicas was oscillating, now %d\n", d[1].replicas)
		 			assert(false)
		 	fi;
	fi;
}