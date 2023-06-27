
/*
	[Limitation]
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/

// We don't assign a time for user command now, and assume each command won't take much time, as they just enqueue the events. 
// https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/kubectl/pkg/cmd/apply/apply.go#L488
proctype applyDeployment(short deploymentTemplateId)
{
	atomic {
		//printf("[***] priority applyDeployment %d\n", _priority, get_priority(_pid))
		d_step{
			short i = 1;
			for (i : 1 .. DEP_NUM) {
				if
					:: d[i].name == deploymentTemplates[deploymentTemplateId].name ->
						printf("[*][applyDeployment] apply; %d; Applying the template %d to deployment {Id %d, index %d}\n", i, deploymentTemplateId, d[i].id, i);
						/* 
							1. [Limitation] We only support the following fields for updates for now. 
							2. If replicas is not specified, then it's the default value. Replica default is 1. https://github.com/kubernetes/kubernetes/issues/67135
							3. TODO: double check on the code level on the apply behavior about how it process default and if it will overwrite for all the field:
							   https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/kubectl/pkg/cmd/apply/apply.go
							   Seems that the default will be applied if it's not defined in the yaml. Because buiding the objects will call Default(), which assign the default values to the resources.
							4. Following has been commented out because we processed it in model_generator.
								d[i].specReplicas = (deploymentTemplates[deploymentTemplateId].specReplicas == -1 -> 1 : deploymentTemplates[deploymentTemplateId].specReplicas);
								d[i].maxSurge = (deploymentTemplates[deploymentTemplateId].maxSurge == -1 -> d[i].maxSurge : deploymentTemplates[deploymentTemplateId].maxSurge);
								d[i].maxUnavailable = (deploymentTemplates[deploymentTemplateId].maxUnavailable == -1 -> d[i].maxUnavailable : deploymentTemplates[deploymentTemplateId].maxUnavailable);
								d[i].strategy = (deploymentTemplates[deploymentTemplateId].strategy == -1 -> d[i].strategy : deploymentTemplates[deploymentTemplateId].strategy);
						*/
						d[i].specReplicas  = deploymentTemplates[deploymentTemplateId].specReplicas
						d[i].maxSurge = deploymentTemplates[deploymentTemplateId].maxSurge
						d[i].maxUnavailable = deploymentTemplates[deploymentTemplateId].maxUnavailable
						d[i].strategy = deploymentTemplates[deploymentTemplateId].strategy 
						updateQueue(dcQueue, dcTail, dcIndex, i, MAX_DEP_QUEUE)	

						break;
					:: else->;
				fi;
			}
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
		//printf("[***] priority createTargetDeployment %d\n", _priority, get_priority(_pid))
		d_step{
			if 
				:: d[deploymentId].status == 0 ->
					d[deploymentId].status = 1;
					printf("[******] Enqueue in createTargetDeployment\n")
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