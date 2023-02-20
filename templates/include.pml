#include "../templates/config.pml"
#include "../templates/dataType.pml"

// in controller_utils 
short sQueue[SCHEDULER_QUEUE_SIZE];
short sTail = 0;
short sIndex = 0;

short dcQueue[DEPLOYMENT_QUEUE_SIZE];
short dcTail = 0;
short dcIndex = 0;

short hpaQueue[HPA_QUEUE_SIZE];
short hpaTail = 0;
short hpaIndex = 0;


deploymentType d[100];
podType pods[100];
nodeType nodes[100];

short pod_total;

#include "../templates/util.pml"

#include "../templates/deployment.pml"
#include "../templates/scheduler.pml"
#include "../templates/hpa.pml"

#include "../templates/event.pml"
#include "../templates/userCommand.pml"
