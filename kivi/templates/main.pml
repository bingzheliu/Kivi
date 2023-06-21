#include "config.pml"

#include "[$FILE_BASE]/include.pml"

#include "event.pml"

#include "intentsCheck.pml"

init{
	[$INIT_SETUP]

	// init finished
	init_status = 1
	short i = 0;

	run deploymentController();
	run scheduler();
	run hpa();
	run nodeController();
	run kubelet();

	[$EVENT_AND_USER_COMMAND]
	
	[$CONTROLLERS]

	// for (i : 1 .. NODE_NUM) {
	// 	run podCpuChangeWithPattern(i);
	// }

	// run podCpuChangeWithPattern()

	// TODO: check on if the order of running the following actually matter or not
	// Intent check for H1
	// run checkH1();

	[$INTENTS]

	[$AUTO_GENERATE_EVENT]


	for (i : 1 .. DEP_NUM) {
		updateQueue(hpaQueue, hpaTail, hpaIndex, i, MAX_HPA_QUEUE);
	}

	if 
		:: (ncIndex == ncTail && hpaTail == hpaIndex && sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail) ->
			[$PROC_AFTER_STABLE]
			skip
	fi;

}