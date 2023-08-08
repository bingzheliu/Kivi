#!/bin/bash

path=$(cd ..;pwd)
echo $path

case_scale=(3 5 10 20 30 50 80 100)
case_id=(s3 s4 h1 h2 s6 s1 s9)
# case_scale=(3 5)
# case_id=(s3 s4)

mkdir "eval/results/"
for case in "${case_id[@]}"	
do
	cur_per_file="eval/results/$case"
	> $cur_per_file
	echo "Working on case $case"
	for i in "${case_scale[@]}"
	do
		echo "Working on node scale $i..."
		echo "python3 kivi_runner.py -f -c $case -s $i >> 'eval/results/output_$case'"
		# mac support gdate; for linux, may need to change to date
		start_time="$(gdate -u +%s.%N)"
		python3 kivi_runner.py -f -c $case -s $i >> eval/results/output_$case
		end_time="$(gdate -u +%s.%N)"
		elapsed1="$(bc <<<"$end_time-$start_time")"
		echo "$i $elapsed1" >> $cur_per_file

		# echo "../src/model_generator.py $case $i"
		
		# python3 ../src/model_generator.py $path $case $i
		# ../libs/Spin/Src/spin -a ../temp/main.pml
		# gcc -o pan pan.c -DVECTORSZ=450000
		
		# ./pan -m10000000 >> "results/pan_exec_$case._$i._$1"
		# ./pan -r main.pml.trail >> "results/pan_error_trail_$case._$i._$1"

		# end_time="$(date -u +%s)"
		# elapsed2="$(bc <<<"$end_time-$start_time")"
		# echo "Total of $elapsed1 seconds elapsed for process"
		# echo "$i $elapsed1 $elapsed2" >> "results/exec_time_$case._$1 "
	done
done

