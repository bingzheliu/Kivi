#!/bin/bash

path=$(cd ..;pwd)
echo $path

case_scale=(3 5 10 20 30 50 80 100)
#case_id=(s3 s4 h1 h2 s6 s1 s9)
count=1
#case_scale=(5)
case_id=(h1)

mkdir "eval/results/"
for case in "${case_id[@]}"	
do
	cur_per_file="eval/results/$case"
	> $cur_per_file
	> eval/results/output_$case
	> eval/results/output_non_violation_$case
	echo "========================="
	echo "Working on case $case"
	for i in "${case_scale[@]}"
	do
		echo "-------------------------"
		echo "Working on (case $case, scale $i)..."
		elapsed_all=0
		elapsed_non_violation_all=0
		for j in $(seq $count)
		do
			echo "Times $j..."
			echo "python3 kivi_runner.py -f -c $case -s $i >> 'eval/results/output_$case'"
			# mac support gdate; for linux, may need to change to date
			start_time="$(gdate -u +%s.%N)"
			python3 kivi_runner.py -f -c $case -s $i >> eval/results/output_$case
			end_time="$(gdate -u +%s.%N)"
			elapsed="$(bc <<<"$end_time-$start_time")"
			elapsed_all="$(bc <<<"$elapsed+$elapsed_all")"
			echo "Runtime #$j $elapsed"

			if [ $1 -gt 0 ]
			then
				echo "Working on non-violation cases"
				echo "python3 kivi_runner.py -f -c $case -s $i -cn > 'eval/results/output_non_violation_$case"
				start_time="$(gdate -u +%s.%N)"
				python3 kivi_runner.py -f -c $case -s $i -cn >> eval/results/output_non_violation_$case
				end_time="$(gdate -u +%s.%N)"
				elapsed="$(bc <<<"$end_time-$start_time")"
				elapsed_non_violation_all="$(bc <<<"$elapsed+$elapsed_non_violation_all")"
				echo "Runtime non-violation #$j $elapsed"
			fi

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
		elapsed_avg=$(echo "scale=5; $elapsed_all / $count" | bc)
		echo "Avg runtime $elapsed_avg"
		if [ $1 -gt 0 ]
		then
			elapsed_non_violation_avg=$(echo "scale=5; $elapsed_non_violation_all / $count" | bc)
			echo "Avg runtime $elapsed_non_violation_avg"
			echo "$i $elapsed_avg $elapsed_non_violation_avg" >> $cur_per_file
		else
			echo "$i $elapsed_avg" >> $cur_per_file
		fi
	done
done

cd eval
gnuplot eval/plot.plt
