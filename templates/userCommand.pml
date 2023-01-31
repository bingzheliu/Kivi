
/*
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/

proctype createDeployment(maxDeploymentId)
{
	atomic{
		short curD = select(0,maxDeploymentId)

		dcQueue[dcTail].add(curD);
		dcTail++;
	}
}

// label selector updates is not recommend and hence not modeled
proctype updateDeployment()
{
	
}

// At the current phase, we don't consider scale and update rollout happen at the same time. 
proctype scaleDeployment(maxDeploymentId)
{
	atomic {
		short curD = select(0, maxDeploymentId);

		d[curD].expReplicas += select(-3, 3);

		dcQueue[dcTail].add(curD);
		dcTail++;
	}
}