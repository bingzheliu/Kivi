
#include "../templates/include.pml"

init{

	[$INIT_SETUP]
	
	run deployment_controller();
	run scheduler();
	run hpa();
	
	[$CONTROLLERS]
}