
#include "../templates/include.pml"

init{

	[$INIT_SETUP]
	
	run deploymentController();
	run scheduler();
	run hpa();
	
	[$CONTROLLERS]

	[$USER_COMMAND]

	int i = 1;
	for (i : 1 .. NODE_NUM) {
		run nodeController(i);
		run kernelPanic(i);
	}
}