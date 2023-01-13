

#include "../templates/config.pml"
#include "../templates/dataType.pml"
#include "../templates/util.pml"


deploymentType d[100];
podType pod[100];


#include "../templates/deployment.pml"





init {
	run deployment_controller();
}