#include "../templates/dataType.pml"

// in controller_utils 
byte sQueue[MAX_SCHEDULER_QUEUE];
short sTail = 0;
short sIndex = 0;

// descheduler now enqueues 1, which is just a trigger and descheduler will check all pods/nodes now.
byte dsQueue[MAX_DESCHEDULER_QUEUE];
short dsTail = 0;
short dsIndex = 0;

byte dcQueue[MAX_DEP_QUEUE];
short dcTail = 0;
short dcIndex = 0;

byte hpaQueue[MAX_HPA_QUEUE];
short hpaTail = 0;
short hpaIndex = 0;

byte ncQueue[MAX_NODE_CONTROLLER_QUEUE];
short ncTail = 0;
short ncIndex = 0;

byte kblQueue[MAX_KUBELET_QUEUE];
short kblTail = 0;
short kblIndex = 0;

// All these arrays start at index 1
deploymentType d[DEP_NUM+1];
podType pods[POD_NUM+1]
nodeType nodes[NODE_NUM+1];

// These would be read-only and not affecting the states
// TODO: seperate the deploymentTye and define a new deploymentTemplate type 
hidden podTemplateType podTemplates[POD_TEMPLATE_NUM+1];
hidden deploymentType deploymentTemplates[DEP_TEMPLATE_NUM+1];
hidden deschedulerProfileType deschedulerProfiles[DES_PROFILE_NUM];
hidden nodeTypeStable nodesStable[NODE_NUM+1]
hidden podTypeStable podsStable[POD_NUM+1]

// short podTotal;

bit init_status = 0;
bit first_proc = 0
short time = 0;

// // This is a counter that could be used for all the forloop in nested functions
// hidden short gi = 0;

#include "../templates/util.pml"

#include "../templates/deployment.pml"
#include "../templates/scheduler.pml"
#include "../templates/hpa.pml"
#include "../templates/nodeController.pml"
#include "../templates/kubelet.pml"

#include "../templates/descheduler.pml"

#include "../templates/event.pml"
#include "../templates/userCommand.pml"


