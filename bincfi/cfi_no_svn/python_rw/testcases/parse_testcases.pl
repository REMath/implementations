#!/usr/bin/perl -w 
use File::Basename;

$match_string = '^\s*([^:]*):([^:]*):([^:]*):([^:]*):([^:]*):([^\n]*)$';
sub launch_test {
	$str = $_[0];
	if($str =~ m/$match_string/){
		#print $_;
		my $config_file = $1;
		my $exe_file = $2;
		my $related_files = $3;
		my $param = $4;
		my $cmp=$5;
		my $cmp_file=$6;
		my $exe_name = basename($exe_file);
		#if($cmp_file eq ""){
	#		$cmp_file = "None";
	#	}
		print "config file: $config_file\n";
		print "cmp file: $cmp_file\n";
		system("mkdir $exe_name 2>/dev/null");
		open($RELATED, ">./$exe_name/related_files") or die("cannot open related_files: $!\n");
		open($PARAM, ">./$exe_name/params") or die("cannot open params: $!\n");
		print $RELATED $related_files;
		print $PARAM $param;
		if($config_file eq "ALL"){
			test_all_configs($exe_file, $cmp, $cmp_file);
		}else{
			system("./launch_test.sh $exe_file $config_file $cmp $cmp_file ");
		}
	}else{
		print "line cannot be recognized\n";
	}
}

sub test_all_configs {
	my $exe_file = shift;
	my $cmp = shift;
	my $cmp_file = shift;
	open($C, "<../configlist") or die("cannot open file: ../configlist, $!\n");
	while(<$C>){
		#my $config_file = chomp($_);
		$config_file = $_;
		$config_file =~ s/\s*$//g; 
		system("./launch_test.sh $exe_file $config_file $cmp $cmp_file ");
	}
}

system("rm ./test_results");
system("touch ./test_results");

if(@ARGV > 0){
	$s = join(' ', @ARGV);
	launch_test($s);

}else{
	open($TEST, '<'."./testlist.txt") or die("cannot open file testlist.txt: $!\n");
	while(<$TEST>){
		if($_ =~ m/^\s*#/){#comments, skip
			next;
		}elsif($_ =~ m/^\s*$/){#empty line, skip
			next;
		}elsif($_ =~ m/$match_string/){
			launch_test($_);
		}else{
			print "unrecognized line: $_";
		}
	}
}
	print "All test results:\n";
	system("cat test_results");

