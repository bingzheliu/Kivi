#include "../templates/dataType.pml"

// in controller_utils 
short sQueue[MAX_SCHEDULER_QUEUE];
short sTail = 0;
short sIndex = 0;

short dcQueue[MAX_DEP_QUEUE];
short dcTail = 0;
short dcIndex = 0;

short hpaQueue[MAX_HPA_QUEUE];
short hpaTail = 0;
short hpaIndex = 0;

short ncQueue[MAX_NODE_CONTROLLER_QUEUE];
short ncTail = 0;
short ncIndex = 0;

short kblQueue[MAX_KUBELET_QUEUE];
short kblTail = 0;
short kblIndex = 0;

// All these arrays start at index 1
deploymentType d[DEP_NUM+1];
podType pods[POD_NUM+1];
nodeType nodes[NODE_NUM+1];

// These would be read-only and not affecting the states
hidden podTemplateType podTemplates[POD_TEMPLATE_NUM+1];
hidden deploymentType deploymentTemplates[DEP_TEMPLATE_NUM+1];

// short podTotal;

short init_status = 0;

// // This is a counter that could be used for all the forloop in nested functions
// hidden short gi = 0;

#include "../templates/util.pml"

#include "../templates/deployment.pml"
#include "../templates/scheduler.pml"
#include "../templates/hpa.pml"
#include "../templates/nodeController.pml"
#include "../templates/kubelet.pml"

#include "../templates/event.pml"
#include "../templates/userCommand.pml"


