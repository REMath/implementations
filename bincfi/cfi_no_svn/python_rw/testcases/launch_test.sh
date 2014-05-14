#!/bin/bash
pwd=$PWD
file=$1
config=$2
cmp=$3
cmp_file=$4
	
fname=`basename $file`
cd ..
#translating the file
echo "tranforming $file"
echo "config file: $config"
./modify_elf.py $file -c $config >$pwd/$fname/transform_output 2>$pwd/$fname/transform_error
cd $pwd

#copying all the related files
cd $fname
rm -rf origin
rm -rf trans
mkdir -p origin
mkdir -p trans
cp -a `cat related_files` ./trans #2>/dev/null #cp -a will perserve the file permission
cp -a `cat related_files` ./origin 2>/dev/null
cd ..

#starting the test
param=`cat $fname/params`
echo -e "testing $file"

if [ $cmp != 0 ] && [ $cmp != 5 ]
then
	#copying the original file
	cp $file $fname/origin/$fname
	echo "starting original program"
	cd $fname/origin
	./$fname $param >stdoutput 2>stderror
	orig_res=$?
	echo $orig_res >res
	echo "result is $orig_res";
	cd $pwd
fi

#copying the transformed file 
cp ../target_elf/$fname/${fname}_final $fname/trans/$fname


echo "starting transformed program"
cd $fname/trans
if [ $cmp == 0 ]
then
	#echo ${fname}
	#echo ${param}
	./${fname} ${param} 2>stderror #no need to care about stdout
elif [ $cmp == 5 ]
then
	./$cmp_file $param #>stdoutput 2>stderror
else
	./${fname} $param >stdoutput 2>stderror
fi

res=$?
echo "result is $res";
echo $res > result;
cd $pwd

if [ $cmp == 1 ] 
then
	diff $fname/trans/stdoutput $fname/origin/stdoutput >$fname/diff_stdout 2>&1
	stdout_diff=$?
	diff $fname/trans/stderror $fname/origin/stderror >$fname/diff_stderr 2>&1
	stderr_diff=$?
	diff $fname/trans/result $fname/origin/res >$fname/diff_res 2>&1
	res_diff=$?
	echo "stdout_diff $stdout_diff; stderr_diff: $stderr_diff; res_diff: $res_diff"
	#if [ $stdout_diff != 0 ] || [ $stderr_diff != 0 ] || [ $res_diff != 0 ]
	if [ $stdout_diff != 0 ]
	then
	
		echo -e "FAIL\t$file\t$param\tin config: $config">>test_results
		echo "FAIL"
	else
		if [ $res != 0 ]
		then
			echo -e "SUCCESS\t$file\t$param\tin config: $config\talthough the transformed program does not run correctly">>test_results
			echo "SUCCESS"
		else
			echo -e "SUCCESS\t$file\t$param\tin config: $config">>test_results
			echo "SUCCESS"
		fi
	fi
elif [ $cmp == 2 ]
then
	diff $fname/trans/$cmp_file $fname/origin/$cmp_file >$fname/diff_special 2>&1
	res_diff=$?
	echo "res_diff: $res_diff"
	if [ $res_diff == 0 ]
	then
		echo -e "SUCCESS\t$file\t$param\tin config: $config">>test_results
		echo "SUCCESS"
	else
		echo -e "FAIL\t$file\t$param\tin config: $config">>test_results
		echo "FAIL"
	fi
elif [ $cmp == 3 ]
then
	cd $fname/origin
	./$cmp_file
	res_diff=$?
	echo "res_diff: $res_diff"
	cd $pwd
	if [ $res_diff == 0 ]
	then
		echo -e "SUCCESS\t$file\t$param\tin config: $config">>test_results
		echo "SUCCESS"
	else
		echo -e "FAIL\t$file\t$param\tin config: $config">>test_results
		echo "FAIL"
	fi
elif [ $cmp == 5 ]
then
	if [ $res == 0 ]; then
		echo -e "SUCCESS\t$file\t$param\tin config: $config">>test_results
		echo "SUCCESS"
	else
		echo -e "FAIL\t$file\t$param\tin config: $config">>test_results
		echo "FAIL"
	fi
else
	if [ $res != 0 ]
	then
		echo -e "FAIL\t$file\t$param\tin config: $config">>test_results
		echo "FAIL"
	else
		echo -e "SUCCESS\t$file\t$param\tin config: $config">>test_results
		echo "SUCCESS"
	fi
fi
