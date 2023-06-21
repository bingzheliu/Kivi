/*
	 HPA controller. Author: Bingzhe Liu. 02/20/2023.
	 1. HPA object is created per deployment/resource. In the implementation, all the HPA objects are maintained by an HPA controller. 
	 HPA controller is implemented with a queue of events. But these events are actually periodically (default 15 seconds) added to the HPA (by controller-manager). 
	 So instead of implemeting the period events, we just make it triggered by any resource changes, to simplify and make it scale better by avoiding unuseful execuation. 
	 TODO: I have not figured out how controller-manager enqueue the events for HPA. 
	 2. HPA look into all the desired state in a stablizationWindows and choose the largest one for scale down. We currently don't model this. 
	 3. HPA has different types of config for metrics, and we currently don't distingish between them, rather, we directly use the metric name. 
		config examples:
					PodsMetricSourceType: use metricSpec.Pods.Target.AverageValue.MilliValue(), non-utlization
						- We don't model the case there exists unready and missing pods for now
 					ResourceMetricSourceType: resource target. 
	 4. We currently do not support "behavior" for HPA.
*/


// 1. We don't consider unreadyPods and missingPods for now
// 2. For metrics, we just get the current raw metrics, rather than within a timewindows (i.e., GetRawMetric)
// 3. TargetValue must be more than 1; if it's utlization, should be 100-based value. 
// 4. The resource request should be stored as per container. As we don't model container, we got the request from the Pod spec instead.
// 5. We only model PodMetricSourceType and ResourceMetricSourceType for now.
inline computeReplicasForMetric(curMetricName, curMetricTarget, curMetricType)
{
	metricNameProposal = curMetricName;
	j = 0;
	k = 0;
	p = 0;
	// use status replicas for calculating the actual usage.
	short metricsTotal = 0, requestTotal = 0, totalReplicas = d[curD].replicas;
	do
		:: p < totalReplicas ->

			k = d[curD].replicaSets[d[curD].curVersion].podIds[j];
			printf("[******][HPA] curD %d, j %d, d[curD].curVersion %d, k %d, pods[k].status %d \n", curD, j, d[curD].curVersion, k, pods[k].status)

			// TODO: now that we added the unreadyPod status, we consider the pod being terminiated still part of the calcluation. Need to check on the code.
			if 
				:: k == 0 || (pods[k].status != 1 && pods[k].status != 3) -> 
					goto hpa2;
				:: else->
					p++;
			fi;
			printf("[*****][HPA] Calculating metrics for pod %d (status %d), totalReplicas %d\n", k, pods[k].status, totalReplicas)

			// assuming all the pods are good. Can add the code to process unready pods here. 
			if 
				// values
				:: curMetricType == 0 ->
					if
						// CPU usage
						:: curMetricName == 0 ->
							metricsTotal = metricsTotal + pods[k].cpu;
						// Mem usage
						:: curMetricName == 1 ->
							metricsTotal = metricsTotal + pods[k].memory;
						:: else->
							printf("[*Internal error][HPA] Invalid metric name\n");
							assert(false);
					fi;
				// utlization
				:: curMetricType == 1 ->
					 if
						// CPU usage
						:: curMetricName == 0->
							metricsTotal = metricsTotal + pods[k].cpu;
							requestTotal = requestTotal + podTemplates[pods[k].podTemplateId].cpuRequested;
						// Mem usage
						:: curMetricName == 1->
							metricsTotal = metricsTotal + pods[k].memory;
							requestTotal = requestTotal + podTemplates[pods[k].podTemplateId].memRequested;
						:: else->
							printf("[*Internal error][HPA] Invalid metric name\n");
							assert(false);
					fi;
				:: else -> 
					printf("[*Internal error][HPA] Invalid metric type\n");
			fi;
hpa2:		j++;
		:: else->break;
	od;

	printf("[****][HPA] Computing metric, metricsTotal is %d, requestTotal is %d\n", metricsTotal, requestTotal)

	short currentUsage = 0;
	if
		:: curMetricType == 0 && totalReplicas != 0 ->
			currentUsage = metricsTotal / totalReplicas;
		:: curMetricType == 1 && requestTotal != 0 ->
			currentUsage = metricsTotal * 100 / requestTotal;
		:: else->
			printf("[*Internal error] Unknown metric types %d or 0 occur in variables (%d totalReplicas, %d requestTotal)", curMetricType, totalReplicas, requestTotal)
			assert(false)
	fi;
	printf("[****][HPA] Computing metric, currentUsage is %d\n", currentUsage)

	// math.Abs(1.0-usageRatio) <= c.tolerance
	// Warning: if exits equal sign, for the cases of large sets of nodes, they may be always within the tolerance, no matter of the TOLERANCE
	if
		:: ((curMetricTarget - currentUsage) <= (HPA_TOLERANCE*curMetricTarget/100)) && ((currentUsage - curMetricTarget) <= (HPA_TOLERANCE*curMetricTarget/100)) ->
			replicaCountProposal = d[curD].specReplicas;
		:: else -> 
			// estimate: this should be ceil, so we just add 1; meaning if it's exact equal to N, then it would become N+1
			// newReplicas := int32(math.Ceil(newUsageRatio * float64(len(metrics))))
			// TODO: this way of calculation can result in slow-growing "issue", should be double checked on this
			printf("[**][HPA] Exceed the HPA tolerence\n")
			printf("[****][HPA] Current curMetricType %d, currentUsage %d, metricsTotal %d, totalReplicas %d, curMetricTarget %d\n", curMetricType, currentUsage, metricsTotal, totalReplicas, curMetricTarget)
			if
				:: curMetricType == 0 ->
					replicaCountProposal = metricsTotal / curMetricTarget + 1;
				:: curMetricType == 1 ->
					replicaCountProposal = currentUsage * totalReplicas / curMetricTarget + 1;
			fi;
			
	fi;

	metricsTotal = 0;
	requestTotal = 0;
	totalReplicas = 0;
	currentUsage = 0;
}

inline computeReplicasForMetrics()
{
	i = 0;
	short replicaCountProposal = 0, metricNameProposal = 0, timestampProposal = 0;

	do
		:: i < d[curD].hpaSpec.numMetrics->
			computeReplicasForMetric(d[curD].hpaSpec.metricNames[i], d[curD].hpaSpec.metricTargets[i], d[curD].hpaSpec.metricTypes[i]);
			if
				:: (replicas == 0) || (replicaCountProposal > replicas) ->
					timestamp = timestampProposal;
					replicas = replicaCountProposal;
					metric = metricNameProposal;
				:: else->;
			fi;
			i++;
		:: else -> break;
	od;

	replicaCountProposal = 0;
	metricNameProposal = 0;
	timestampProposal = 0;
/*
	for (i : 0 .. d[curD].hpaSpec.numMetrics) {
		computeReplicasForMetric(d[curD].hpaSpec.metricNames[i], d[curD].hpaSpec.metricTargets[i], d[curD].hpaSpec.metricTypes[i]);
		if
			:: (replicas == 0) || (replicaCountProposal > replicas) ->
				timestamp = timestampProposal;
				replicas = replicaCountProposal;
				metric = metricNameProposal;
			:: else->;
		fi;
	}
*/
	// We assume all the metrics are valid for now, and we don't do the post-processing
}

inline convertDesiredReplicasWithRules()
{
	short scaleUpLimit = HPA_SCALE_UP_LIMIT_FACTOR * currentReplicas;
	if
		:: HPA_SCALE_UP_LIMIT_MIN > scaleUpLimit->
			scaleUpLimit = HPA_SCALE_UP_LIMIT_MIN;
		:: else->;
	fi;

	short maximumAllowedReplicas = d[curD].hpaSpec.maxReplicas;
	if
		:: maximumAllowedReplicas > scaleUpLimit->
			maximumAllowedReplicas = scaleUpLimit;
		:: else->;
	fi;

	short minimumAllowedReplicas = d[curD].hpaSpec.minReplicas;
	if 
		:: desiredReplicas < minimumAllowedReplicas ->
			desiredReplicas = minimumAllowedReplicas;
		:: desiredReplicas > maximumAllowedReplicas ->
			desiredReplicas = maximumAllowedReplicas;
		:: else->;
	fi;

	scaleUpLimit = 0;
	maximumAllowedReplicas = 0;
	minimumAllowedReplicas = 0;
}	

inline normalizeDesiredReplicas()
{
	// skipping the stabilizeRecommendation for now
	convertDesiredReplicasWithRules();
}

// logic in func reconcileAutoscaler. 

// TODO:
//	 1. Need to deal with multiple deployment for timestamp, where multiple deployment may be working concurrently rather than wait for a period of time; 
// in particular, for the enqueue sentence in main for HPA, the deployment always start at #1, and may actually fail to consider other orders of deployment. 
proctype hpa()
{
	short i = 0, j = 0, k = 0, p = 0;
	short local_last_time = 0;
endHPA:	do
		:: (hpaIndex != hpaTail) && (time-local_last_time >= HPA_WAIT_TIME || (sIndex == sTail && kblIndex == kblTail && dcIndex == dcTail && ncIndex == ncTail))-> 
			atomic{
				d_step{
					// TODO: check, potentially can have issue because the curD can be shared acrose the controller
					short curD = hpaQueue[hpaIndex];
					short currentReplicas = d[curD].specReplicas;
					short desiredReplicas = 0, rescaleMetric = 0;
					// [NS] Timestamp is not actually implemented.
					short replicas = 0, timestamp = 0, metric = 0;

					printf("[**][HPA] HPA working on deployment %d\n", curD)

					if
						// TODO: check on this condition -- now we add this because HPA should not start to calculate if there's no replicas
						::d[curD].hpaSpec.isEnabled == 0 || d[curD].replicas == 0 ->
							skip
						::else->;
							if
								:: currentReplicas == 0 ->
									desiredReplicas = 0;
								:: else -> 
									if
										// TODO: double check if the below is >= or >, it could affect the logic
										::currentReplicas > d[curD].hpaSpec.maxReplicas ->
											printf("[**][HPA] Current number of replicas above Spec.MaxReplicas\n");
											desiredReplicas = d[curD].hpaSpec.maxReplicas;
										::currentReplicas < d[curD].hpaSpec.minReplicas ->
											printf("[**][HPA] Current number of replicas below Spec.MinReplicas\n");
											desiredReplicas = d[curD].hpaSpec.minReplicas;
										::else->
											computeReplicasForMetrics()
											if 
												:: replicas > desiredReplicas -> 
													desiredReplicas = replicas;
													rescaleMetric = metric;
												:: else ->;
											fi;
											printf("[**][HPA] Got new desiredReplicas %d, was %d\n", desiredReplicas, currentReplicas)
											// not modeling normalizeDesiredReplicasWithBehaviors for now.
											normalizeDesiredReplicas();
											printf("[***][HPA] After normalizing, got new desiredReplicas %d, was %d\n", desiredReplicas, currentReplicas)
									fi;
							fi;

							if 
								:: desiredReplicas != currentReplicas ->
									printf("[*][HPA]rescale; %d; %d; %d; Need to rescale, scale metric is %d, orgional is %d, now is %d.\n", curD, currentReplicas, desiredReplicas, rescaleMetric, currentReplicas, desiredReplicas);
									// in k8s, it will trigger client-go.scale. Here we do it directly by writing into the deployment.
									d[curD].specReplicas = desiredReplicas;
									updateQueue(dcQueue, dcTail, dcIndex, curD, MAX_DEP_QUEUE)						
									// dcQueue[dcTail] = curD;
									// dcTail++;
								:: else->;
							fi;
					fi;

					printf("[**][HPA] HPA finished on deployment %d\n", curD)
					updateQueueIndex(hpaIndex, MAX_HPA_QUEUE);

					if 
						:: local_last_time + HPA_WAIT_TIME + HPA_RUN_TIME > time->
							time = local_last_time + HPA_WAIT_TIME + HPA_RUN_TIME
						:: else-> 
							time = time+HPA_RUN_TIME;
					fi;
					local_last_time = time;
					printf("[****]time %d, local_last_time %d\n", time, local_last_time)

					i = 0;
					j = 0;
					k = 0;
					p = 0;
					currentReplicas = 0;
					curD = 0;
					desiredReplicas = 0;
					rescaleMetric = 0;
					replicas = 0;
					timestamp = 0;
					metric = 0;
				}
			}
	od;
}
