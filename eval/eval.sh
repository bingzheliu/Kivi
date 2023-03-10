#!/bin/bash

path=$(cd ..;pwd)
echo $path

for case in "s3" 
do
	echo "Working on case $case"
	for i in 3 10 20 50 80 100 
	do
		echo "Working on node scale $i..."
		echo "../src/model_generator.py $case $i"
		# TODO: do nano sec instead
		start_time="$(date -u +%s)"
		python3 ../src/model_generator.py $path $case $i
		../libs/Spin/Src/spin -a ../temp/main.pml
		gcc -o pan pan.c -DVECTORSZ=450000
		end_time="$(date -u +%s)"
		elapsed1="$(bc <<<"$end_time-$start_time")"
		./pan -m10000000 >> "results/pan_exec_$case._$i._$1"
		./pan -r main.pml.trail >> "results/pan_error_trail_$case._$i._$1"

		end_time="$(date -u +%s)"
		elapsed2="$(bc <<<"$end_time-$start_time")"
		echo "Total of $elapsed1 seconds elapsed for process"
		echo "$i $elapsed1 $elapsed2" >> "results/exec_time_$case._$1 "
	done
done

