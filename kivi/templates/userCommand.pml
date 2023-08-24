
/*
	[Limitation]
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/


// TODO: to simiply this, we could remove the deploymentTemplate, and just store it as a normal deployment. So the only thing to do is to switch the status from 0 to 1.
inline copyDeploymentWithTemplate(i, deploymentTemplateId, overwrite)
{
	/*
		Following has been commented out because we processed it in model_generator.
			d[i].specReplicas = (deploymentTemplates[deploymentTemplateId].specReplicas == -1 -> 1 : deploymentTemplates[deploymentTemplateId].specReplicas);
			d[i].maxSurge = (deploymentTemplates[deploymentTemplateId].maxSurge == -1 -> d[i].maxSurge : deploymentTemplates[deploymentTemplateId].maxSurge);
			d[i].maxUnavailable = (deploymentTemplates[deploymentTemplateId].maxUnavailable == -1 -> d[i].maxUnavailable : deploymentTemplates[deploymentTemplateId].maxUnavailable);
			d[i].strategy = (deploymentTemplates[deploymentTemplateId].strategy == -1 -> d[i].strategy : deploymentTemplates[deploymentTemplateId].strategy);
	*/
	// podTemplate must be defined for a new deployment; but can be 0, which means it will be kept for the existing deployment. 
	d[i].podTemplateId = (deploymentTemplates[deploymentTemplateId].podTemplateId == 0 -> d[i].podTemplateId : deploymentTemplates[deploymentTemplateId].podTemplateId)
	d[i].maxSurge = deploymentTemplates[deploymentTemplateId].maxSurge
	d[i].maxUnavailable = deploymentTemplates[deploymentTemplateId].maxUnavailable
	d[i].strategy = deploymentTemplates[deploymentTemplateId].strategy 
	d[i].specReplicas = deploymentTemplates[deploymentTemplateId].specReplicas

	// if existing deployment does not define HPA, we will keep the original defined HPA. Becase in the actually k8s kubectl apply, the HPA does not really be applied. 
	// We here simply the HPA apply into this same procedure. Will need to add a new command line to apply HPA if user considers to apply HPA at runtime.
	if 
		:: deploymentTemplates[deploymentTemplateId].hpaSpec.isEnabled == 0 && overwrite == 0 ->
			skip
		:: else ->
			d[i].hpaSpec.isEnabled = deploymentTemplates[deploymentTemplateId].hpaSpec.isEnabled
			d[i].hpaSpec.minReplicas = deploymentTemplates[deploymentTemplateId].hpaSpec.minReplicas
			d[i].hpaSpec.maxReplicas = deploymentTemplates[deploymentTemplateId].hpaSpec.maxReplicas
			d[i].hpaSpec.numMetrics = deploymentTemplates[deploymentTemplateId].hpaSpec.numMetrics
			for (j : 0 .. d[i].hpaSpec.numMetrics-1) {
				d[i].hpaSpec.metricNames[j] = deploymentTemplates[deploymentTemplateId].hpaSpec.metricNames[j]
				d[i].hpaSpec.metricTypes[j] = deploymentTemplates[deploymentTemplateId].hpaSpec.metricTypes[j]
			}
	fi;
}

// We don't assign a time for user command now, and assume each command won't take much time, as they just enqueue the events. 
// https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/kubectl/pkg/cmd/apply/apply.go#L488
proctype applyDeployment(short deploymentTemplateId)
{
	atomic {
		//printf("[***] priority applyDeployment %d\n", _priority, get_priority(_pid))
		d_step{
			short i = 1, j = 0;
			bit exists = 0;
			for (i : 1 .. DEP_NUM) {
				if
					:: d[i].status == 1 && d[i].name == deploymentTemplates[deploymentTemplateId].name ->
						exists = 1;
						printf("[*][applyDeployment] apply; %d; Applying the template %d to existing deployment {Id %d, index %d}\n", i, deploymentTemplateId, d[i].id, i);
						/* 
							1. [Limitation] We only support the following fields for updates for now. These update behavior can be configured when there's conflict.
							   Now, we assume if a field has not been defined, then we put the default value to it (except HPA and podTemeplate); otherwise, we overwrite the old one with the new one. This may not be the right behavior, see #2 below.
							2. If replicas is not specified, then it's the default value. Replica default is 1. https://github.com/kubernetes/kubernetes/issues/67135
							3. TODO: double check on the code level on the apply behavior about how it process default and if it will overwrite for all the field:
							   https://github.com/kubernetes/kubernetes/blob/master/staging/src/k8s.io/kubectl/pkg/cmd/apply/apply.go
							   Seems that the default will be applied if it's not defined in the yaml. Because buiding the objects will call Default(), which assign the default values to the resources.
						*/
						copyDeploymentWithTemplate(i, deploymentTemplateId, 0)
						updateQueue(dcQueue, dcTail, dcIndex, i, MAX_DEP_QUEUE)	
						break;
					:: else->;
				fi;
			}
			if 
				:: exists == 0 ->
					bit spared = 0;
					for (i : 1 .. DEP_NUM) {
						if
							:: d[i].status == 0 ->
								printf("[*][applyDeployment] apply; %d; Applying the template %d to new deployment {Id %d, index %d}\n", i, deploymentTemplateId, d[i].id, i);
								spared = 1
								d[i].status = 1
								d[i].replicasInDeletion = 0
								d[i].replicasInCreation = 0
								copyDeploymentWithTemplate(i, deploymentTemplateId, 1)
								updateQueue(dcQueue, dcTail, dcIndex, i, MAX_DEP_QUEUE)	
								break;
							:: else->;
						fi;
					}
					if 
						:: spared == 0 ->
							printf("[*Warning] Deployment object is not enough!\n")
						:: else->;
					fi;
				:: else->;
			fi;

			exists = false;
			i = 0;
			j = 0
		}	
	}
}

// kubectl create cannot create an existing object.
proctype createDeployment(short deploymentTemplateId)
{
	atomic{
		//printf("[***] priority createTargetDeployment %d\n", _priority, get_priority(_pid))
		d_step{
			short i = 1, j = 0;
			bit exists = 0;
			for (i : 1 .. DEP_NUM) {
				if
					:: d[i].status == 1 && d[i].name == deploymentTemplates[deploymentTemplateId].name ->
						exists = 1;
					:: else->;
				fi
			}
			if 
				:: exists == 1 ->
					printf("[*][createDeployment] %d deployment exists!\n", deploymentTemplateId);
					assert(false)
				:: else -> 
					bit spared = 0;
					for (i : 1 .. DEP_NUM) {
						if
							:: d[i].status == 0 ->
								printf("[*][createDeployment] create; %d; Create the template %d to new deployment {Id %d, index %d}\n", i, deploymentTemplateId, d[i].id, i);
								spared = 1
								d[i].status = 1
								d[i].replicasInDeletion = 0
								d[i].replicasInCreation = 0
								copyDeploymentWithTemplate(i, deploymentTemplateId, 1)
								updateQueue(dcQueue, dcTail, dcIndex, i, MAX_DEP_QUEUE)	
								break;
							:: else->;
						fi;
					}
					if 
						:: spared == 0 ->
							printf("[*Warning] Deployment object is not enough!\n")
						:: else->;
					fi;
			fi;
		}
	}
}

// This command is an easy way to put an existing deployment, which are defined as in d instead of deploymentTemplate, to alive. Mostly used in bootstrapping to simplified the process.
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
					printf("[*][createTargetDeployment] Created deployment %d\n", deploymentId)
				:: else ->;
			fi;
			first_proc = 1;
		}
	}
}

// proctype createDeployment(short maxDeploymentId)
// {
// 	atomic{
// 		short curD;
// 		select(curD : 0 .. maxDeploymentId);

// 		updateQueue(dcQueue, dcTail, dcIndex, curD, MAX_DEP_QUEUE)		
// 	}
// }



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