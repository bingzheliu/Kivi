
/*
	1. User can't change their PodSpec (Affinity spec) afterwards for now. Because we need to pre-process the regex in affinity.
	2. User can't add new node if they are using the affinity spec. Same reason as 1. 
*/

proctype createDeployment()
{
	
}

// label selector updates is not recommend and hence not modeled
proctype updateDeployment()
{
	
}

// At the current phase, we don't consider scale and update rollout happen at the same time. 
proctype scaleDeployment()
{
	atomic {
		curD = select(0, m);

		dcQueue[dcTail].add(d);
	}
}