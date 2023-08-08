reset

load './style_small.gnu'
set termoption dash

#set terminal pdf

set xlabel 'Scale'
set ylabel 'Time (s)'

set xrange [0:110]

#set ytics 1,1,3

set grid x y

#set key at 14.2, 0.98
set key top left

set output './results/performance_violation.eps'
plot 'results/s3' using 1:2  with lp linewidth 6 linecolor 1 linetype 7 title 's3', \
	 'results/s4' using 1:2  with lp linewidth 6 linecolor 2 linetype 1 title 's4', \
	 'results/s6' using 1:2  with lp linewidth 6 linecolor 3 linetype 3 title 's6', \
	 'results/s1' using 1:2  with lp linewidth 6 linecolor 4 linetype 5 title 's1', \
	 'results/s9' using 1:2  with lp linewidth 6 linecolor 5 linetype 6 title 's9', \
	 'results/h1' using 1:2  with lp linewidth 6 linecolor 6 linetype 8 title 'h1', \
	 'results/h2' using 1:2  with lp linewidth 6 linecolor 7 linetype 2 title 'h2'

exit