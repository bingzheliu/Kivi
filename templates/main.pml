#include "[$CONFIG_FILENAME]"

#include "../../templates/include.pml"

#include "[$INTENT_FILENAME]"

init{
	[$INIT_SETUP]

	// init finished
	init_status = 1
	
	// TODO: check on if the order of running the following actually matter or not
	//run check();

	run deploymentController();
	run scheduler();
	run hpa();
	run nodeController();
	run kubelet();
	
	[$CONTROLLERS]

	[$USER_COMMAND]

	int i = 1;
	for (i : 1 .. NODE_NUM) {
		run kernelPanic(i);
	}

	for (i : 1 .. POD_NUM) {
		run podCpuChangeWithPattern(i);
	}

}