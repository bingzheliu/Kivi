#include "[$CONFIG_FILENAME]"

#include "[$FILE_BASE]/templates/include.pml"

#include "[$EVENT_FILENAME]"

#include "[$INTENT_FILENAME]"

init{
	[$INIT_SETUP]

	// init finished
	init_status = 1

	run deploymentController();
	run scheduler();
	run hpa();
	run nodeController();
	run kubelet();
	
	[$CONTROLLERS]

	[$USER_COMMAND]

	// for (i : 1 .. NODE_NUM) {
	// 	run podCpuChangeWithPattern(i);
	// }

	// run podCpuChangeWithPattern()

	[$EVENT]

	// TODO: check on if the order of running the following actually matter or not
	// Intent check for H1
	// run checkH1();

	[$INTENTS]

}