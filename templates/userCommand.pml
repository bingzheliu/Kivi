
/*
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/

proctype createDeployment(short maxDeploymentId)
{
	atomic{
		short curD;
		select(curD : 0 .. maxDeploymentId);

		dcQueue[dcTail] = curD;
		dcTail++;
	}
}

proctype createTargetDeployment(short deploymentId)
{
	atomic{
		if 
			:: d[deploymentId].status == 0 ->
				d[deploymentId].status = 1;
				dcQueue[dcTail] = deploymentId;
				dcTail++;
			:: else ->;
		fi;
	}
}

/*
// label selector updates is not recommend and hence not modeled
proctype updateDeployment()
{
	
}
*/

// At the current phase, we don't consider scale and update rollout happen at the same time. 
proctype scaleDeployment(short maxDeploymentId)
{
	atomic {
		short curD;
		select(curD : 0..maxDeploymentId);
		short ranScale;
		select(ranScale : -3..3)

		d[curD].specReplicas = d[curD].specReplicas + ranScale;

		dcQueue[dcTail] = curD;
		dcTail++;
	}
}