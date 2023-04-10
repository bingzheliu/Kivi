#include "../templates/dataType.pml"

// in controller_utils 
short sQueue[MAX_QUEUE_SIZE];
short sTail = 0;
short sIndex = 0;

short dcQueue[MAX_QUEUE_SIZE];
short dcTail = 0;
short dcIndex = 0;

short hpaQueue[MAX_QUEUE_SIZE];
short hpaTail = 0;
short hpaIndex = 0;

short ncQueue[MAX_QUEUE_SIZE];
short ncTail = 0;
short ncIndex = 0;

short kblQueue[MAX_QUEUE_SIZE];
short kblTail = 0;
short kblIndex = 0;

// All these arrays start at index 1
deploymentType d[MAX_DEPLOYMENT];
podType pods[MAX_POD];
nodeType nodes[NODE_NUM+1];
podTemplateType podTemplates[POD_TEMPLATE_NUM];
deploymentType deploymentTemplates[DEP_TEMPLATE_NUM];

short podTotal;

short init_status = 0;

#include "../templates/util.pml"

#include "../templates/deployment.pml"
#include "../templates/scheduler.pml"
#include "../templates/hpa.pml"
#include "../templates/nodeController.pml"
#include "../templates/kubelet.pml"

#include "../templates/event.pml"
#include "../templates/userCommand.pml"


