#!/usr/bin/perl -w

use File::Basename;
require "./dependency_check.pl";
sub instrument {
	my $log = $_[0];
	my $trans = "";
	my $c = "";
	if(not defined $_[1]){
		$trans = "";
	}else{
		$trans = $_[1];
	}
	my $path = '/home/mingwei/Downloads/eglibc-2.13/build/../installdir/lib/';
	my $cmd = "cat $log|".'grep "loading an object"|sed \'s/^.*loading an object\s*//g\'|awk \'{print $1}\'|';
	open(FILE,$cmd) or die("cannot execute cmd: $cmd\t$!\n");
	while(<FILE>){
		$file = $_;
		$file =~ s/^\s+//;
		$file =~ s/\n+$//;
		if($file =~ m/^(\/|\.\.\/|\.\/)/){
			#print "this is a path name\n";
			$b = basename($file);
			$c = "ln -s ".$file." ".$path.$b;
			print "$c\n";
			system($c);
			$c = "./instrument_replace.py -I $b";
			print "$c\n";
			system($c);
		}else{
			if($trans eq "-re"){
				$c = "./instrument_replace.py -R $file";
				system($c);
				$c = "./instrument_replace.py -I $file";
				system($c);
			}else{
				if(check_translated_one($path.$file) == 1){
					print "$file is already translated\n"
				}else{
					$c = "./instrument_replace.py -R $file";
					system($c);
					my $c = "./instrument_replace.py -I $file";
					system($c);
				}
			}
			#print "$c\n";
			#print "this is a file name\n";
		}
	}
}

instrument(shift(@ARGV));
