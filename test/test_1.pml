
#include "../templates/include.pml"


init {
	run deployment_controller();
	run scheduler();
	run hpa();

	run createDeployment(3);
	run event_cpu_change();
}