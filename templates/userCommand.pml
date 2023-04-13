
/*
	[Limitation]
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/

proctype applyDeployment(short deploymentTemplateId)
{
	atomic {
		d_step{
			short i = 1;
			for (i : 1 .. DEP_NUM) {
				if
					:: d[i].name == deploymentTemplates[deploymentTemplateId].name ->
						printf("[**][applyDeployment] Applying the template %d to deployment {Id %d, index %d}\n", deploymentTemplateId, d[i].id, i);
						// [Limitation] We only support the following fields for updates for now. 
						// If replicas is not specified, then it's the default value 1. https://github.com/kubernetes/kubernetes/issues/67135
						d[i].specReplicas = (deploymentTemplates[deploymentTemplateId].specReplicas == -1 -> 1 : deploymentTemplates[deploymentTemplateId].specReplicas);
						d[i].maxSurge = (deploymentTemplates[deploymentTemplateId].maxSurge == -1 -> d[i].maxSurge : deploymentTemplates[deploymentTemplateId].maxSurge);
						d[i].maxUnavailable = (deploymentTemplates[deploymentTemplateId].maxUnavailable == -1 -> d[i].maxUnavailable : deploymentTemplates[deploymentTemplateId].maxUnavailable);
						d[i].strategy = (deploymentTemplates[deploymentTemplateId].strategy == -1 -> d[i].strategy : deploymentTemplates[deploymentTemplateId].strategy);
						break;
					:: else->;
				fi;
			}

			updateQueue(dcQueue, dcTail, dcIndex, i, MAX_DEP_QUEUE)	
			i = 0;
		}	
	}
}

proctype createDeployment(short maxDeploymentId)
{
	atomic{
		short curD;
		select(curD : 0 .. maxDeploymentId);

		updateQueue(dcQueue, dcTail, dcIndex, curD, MAX_DEP_QUEUE)		
	}
}

proctype createTargetDeployment(short deploymentId)
{
	atomic{
		d_step{
			if 
				:: d[deploymentId].status == 0 ->
					d[deploymentId].status = 1;
					updateQueue(dcQueue, dcTail, dcIndex, deploymentId, MAX_DEP_QUEUE)		
					printf("[***][createTargetDeployment] Created deployment %d\n", deploymentId)
				:: else ->;
			fi;
		}
	}
}

/*
// label selector updates is not recommend and hence not modeled
proctype updateDeployment()
{
	
}
*/

// [Limitation] At the current phase, we don't consider scale and update rollout happen at the same time. 
proctype scaleDeployment(short maxDeploymentId)
{
	atomic {
		short curD;
		select(curD : 0..maxDeploymentId);
		short ranScale;
		select(ranScale : -3..3)

		d[curD].specReplicas = d[curD].specReplicas + ranScale;

		updateQueue(dcQueue, dcTail, dcIndex, curD, MAX_DEP_QUEUE)		
	}
}