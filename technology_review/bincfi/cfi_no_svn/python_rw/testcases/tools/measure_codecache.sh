#!/bin/bash
rm abc
exe=$@;
echo "dollar at is $@"
base=`echo $((0x100000))`
largest=$(($base*5))
base=$largest
largest=$(($base*7))
echo $base
echo $largest
for  (( c=$base; c<=$largest; c=$(($c+$base)) ))
do 
	echo "codecache: $c. test begin" 
	echo "codecache: $c" >> abc
	/usr/bin/time -o abc -a pin -follow-execv -limit_code_cache $c  -- $@
done
