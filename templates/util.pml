inline test_duplication()
{
	atomic {
	i = 1; 
	do
	:: i < NODE_NUM + 1 ->
		if
			:: node[i].pod_num > MAX_DUPLICATE_REPLICA -> break;
			:: else->;
		fi;
		i++
	:: else -> goto L4;
	od;
	}
}
