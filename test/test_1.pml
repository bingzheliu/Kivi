

#include "../templates/config.pml"
#include "../templates/dataType.pml"
#include "../templates/util.pml"



deploymentType d[100];
podType pod[100];

#include "../templates/event.pml"
#include "../templates/userCommand.pml"

#include "../templates/deployment.pml"
#include "../templates/scheduler.pml"
#include "../templates/hpa.pml"





init {
	run deployment_controller();
	run scheduler();
	run hpa();

	run createDeployment(3);
	run event_cpu_change();
}