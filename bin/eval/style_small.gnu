set macro


#####  Color Palette by Color Scheme Designer

   blue_000 = "#A9BDE6" # = rgb(169,189,230)
   blue_025 = "#7297E6" # = rgb(114,151,230)
   blue_050 = "#1D4599" # = rgb(29,69,153)
   blue_075 = "#2F3F60" # = rgb(47,63,96)
   blue_100 = "#031A49" # = rgb(3,26,73)

   green_000 = "#A6EBB5" # = rgb(166,235,181)
   green_025 = "#67EB84" # = rgb(103,235,132)
   green_050 = "#11AD34" # = rgb(17,173,52)
   green_075 = "#2F6C3D" # = rgb(47,108,61)
   green_100 = "#025214" # = rgb(2,82,20)

   red_000 = "#F9B7B0" # = rgb(249,183,176)
   red_025 = "#F97A6D" # = rgb(249,122,109)
   red_050 = "#E62B17" # = rgb(230,43,23)
   red_075 = "#8F463F" # = rgb(143,70,63)
   red_100 = "#6D0D03" # = rgb(109,13,3)

   brown_000 = "#F9E0B0" # = rgb(249,224,176)
   brown_025 = "#F9C96D" # = rgb(249,201,109)
   brown_050 = "#E69F17" # = rgb(230,159,23)
   brown_075 = "#8F743F" # = rgb(143,116,63)
   brown_100 = "#6D4903" # = rgb(109,73,3)

   black_025 = "#222222"

   grid_color = "#d5e0c9"
   text_color = "#6a6a6a"


   # change line width if necessary
   my_line_width = "7"
   my_ps = "1.2"


set pointsize my_ps

set style line 1  lc rgb "black" linewidth @my_line_width lt 1 pt 13
set style line 2  lc rgb "black" linewidth @my_line_width lt 0 pt 11
set style line 3  lc rgb "black" linewidth @my_line_width lt 3 pt 7

set style line 4  linecolor rgbcolor red_050 linewidth @my_line_width pt 13
set style line 5  linecolor rgbcolor blue_050  linewidth @my_line_width pt 11
set style line 6  linecolor rgbcolor brown_025 linewidth @my_line_width pt 7
set style line 7  linecolor rgbcolor black_025   linewidth @my_line_width pt 5
set style line 8  linecolor rgbcolor red_050 linewidth @my_line_width pt 9
set style line 9  linecolor rgbcolor red_050  linewidth @my_line_width pt 13
set style line 10 linecolor rgbcolor green_075 linewidth @my_line_width pt 11
set style line 11 linecolor rgbcolor brown_050   linewidth @my_line_width pt 7
set style line 12 linecolor rgbcolor brown_075 linewidth @my_line_width pt 5
set style line 13 linecolor rgbcolor blue_100  linewidth @my_line_width pt 9
set style line 14 linecolor rgbcolor green_100 linewidth @my_line_width pt 13
set style line 15 linecolor rgbcolor red_100   linewidth @my_line_width pt 11
set style line 16 linecolor rgbcolor brown_100 linewidth @my_line_width pt 7
set style line 17 linecolor rgbcolor "#224499" linewidth @my_line_width pt 5
set style line 18  linecolor rgbcolor blue_050  linewidth @my_line_width pt 7
set style line 19 linecolor rgbcolor green_025 linewidth @my_line_width pt 5
set style line 20 linecolor rgbcolor red_025   linewidth @my_line_width pt 9

#set terminal postscript eps color enhanced  "Helvetica" 26
set terminal postscript eps color enhanced  "Helvetica" 26
set size 1, 0.8


#set style line 1 lt 1 pt 2 lw 7 ps 2
#set style line 2 lt rgb "black" pt 4 lw 10 ps 2
#set style line 3 lt 3 pt 7 lw 7 ps 2
#set style line 4 lt 1 pt 9 lw 7 ps 2

#set style line 5 lt 1 lw 7
#set style line 6 lt rgb "black" lw 7
#set style line 7 lt rgb "blue" lw 7
#set style line 8 lt 4 lw 7
#set style line 9 lt 2 lw 7
#set style line 10 lt 8 lw 7
#set style line 11 lt 7 lw 7


unset title
unset logscale
unset key
unset grid
