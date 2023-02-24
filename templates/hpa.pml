/*
	 HPA controller. Author: Bingzhe Liu. 02/20/2023.
	 1. HPA object is created per deployment/resource. In the implementation, all the HPA objects are maintained by an HPA controller. HPA controller is implemented with a queue of events. But these events are actually periodically added to the HPA (by controller-manager). So instead of implemeting the period events, we just make it triggered by any resource changes, to simplify and make it scale better by avoiding unuseful execuation. TODO: I have not figured out how controller-manager enqueue the events for HPA. 
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
			printf("%d\n",j);
			if 
				:: k == 0 || pods[k].status == 0 -> 
					goto hpa2;
				:: else->
					p++;
			fi;

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
							printf("Invalid metric name\n");
							assert(false);
					fi;
				// utlization
				:: curMetricType == 1 ->
					 if
						// CPU usage
						:: curMetricName == 0->
							metricsTotal = metricsTotal + pods[k].cpu;
							requestTotal = requestTotal + d[pods[k].deploymentId].cpuRequested;
						// Mem usage
						:: curMetricName == 1->
							metricsTotal = metricsTotal + pods[k].memory;
							requestTotal = requestTotal + d[pods[k].deploymentId].memRequested;
						:: else->
							printf("Invalid metric name\n");
							assert(false);
					fi;
				:: else -> 
					printf("Invalid metric type\n");
			fi;
hpa2:		j++;
		:: else->break;
	od;

	printf("Computing metric, metricsTotal is %d, requestTotal is %d\n", metricsTotal, requestTotal)

	short currentUsage = 0;
	if
		:: curMetricType == 0 ->
			currentUsage = metricsTotal / totalReplicas;
		:: curMetricType == 1 ->
			currentUsage = metricsTotal * 100 / requestTotal;
	fi;
	printf("Computing metric, currentUsage is %d\n", currentUsage)

	//  math.Abs(1.0-usageRatio) <= c.tolerance
	if
		:: ((curMetricTarget - currentUsage) <= (HPA_TOLERANCE*curMetricTarget/100)) && ((currentUsage - curMetricTarget) <= (HPA_TOLERANCE*curMetricTarget/100)) ->
			replicaCountProposal = d[curD].specReplicas;
		:: else -> 
			// estimate: this should be ceil, but we estimate as floor
			if
				:: curMetricType == 0 ->
					replicaCountProposal = metricsTotal / curMetricTarget;
				:: curMetricType == 1 ->
					replicaCountProposal = currentUsage * totalReplicas / curMetricTarget
			fi;
			
	fi;
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

	short maximumAllowedReplicas = HPA_MAX_REPLICAS;
	if
		:: maximumAllowedReplicas > scaleUpLimit->
			maximumAllowedReplicas = scaleUpLimit;
		:: else->;
	fi;

	short minimumAllowedReplicas = HPA_MIN_REPLICAS;
	if 
		:: desiredReplicas < minimumAllowedReplicas ->
			desiredReplicas = minimumAllowedReplicas;
		:: desiredReplicas > maximumAllowedReplicas ->
			desiredReplicas = maximumAllowedReplicas;
		:: else->;
	fi;
}	

inline normalizeDesiredReplicas()
{
	// skipping the stabilizeRecommendation for now
	convertDesiredReplicasWithRules();
}

// logic in func reconcileAutoscaler. 
proctype hpa()
{
	short i = 0, j = 0, k = 0, p = 0;
	do
		:: (hpaIndex < hpaTail) -> 
			atomic{
				// TODO: check, potentially can have issue because the curD can be shared acrose the controller
				short curD = hpaQueue[hpaIndex];
				short currentReplicas = d[curD].specReplicas;
				short desiredReplicas = 0, rescaleMetric = 0;
				// [NS] Timestamp is not actually implemented.
				short replicas = 0, timestamp = 0, metric = 0;

				if
					::d[curD].hpaSpec.isEnabled == 0 ->
						goto hpa1;
					::else->;
				fi;

				if
					:: currentReplicas == 0 ->
						desiredReplicas = 0;
					:: else -> 
						if
							::currentReplicas > HPA_MAX_REPLICAS ->
								printf("Current number of replicas above Spec.MaxReplicas\n");
								desiredReplicas = HPA_MAX_REPLICAS;
							::currentReplicas < HPA_MIN_REPLICAS ->
								printf("Current number of replicas below Spec.MinReplicas\n");
								desiredReplicas = HPA_MIN_REPLICAS;
							::else->
								computeReplicasForMetrics()
								if 
									:: replicas > desiredReplicas -> 
										desiredReplicas = replicas;
										rescaleMetric = metric;
									:: else ->;
								fi;
								printf("Got new desiredReplicas %d\n", desiredReplicas)
								// not modeling normalizeDesiredReplicasWithBehaviors for now.
								normalizeDesiredReplicas();
						fi;
				fi;

				if 
					:: desiredReplicas != currentReplicas ->
						printf("Need to rescale, scale metric is %d, orgional is %d, now is %d.\n", rescaleMetric, currentReplicas, desiredReplicas);
						// in k8s, it will trigger client-go.scale. Here we do it directly by writing into the deployment.
						d[curD].specReplicas = desiredReplicas;
						dcQueue[dcTail] = curD;
						dcTail++;
					:: else->;
				fi;

hpa1:			hpaIndex ++;
			}
	od;
}
