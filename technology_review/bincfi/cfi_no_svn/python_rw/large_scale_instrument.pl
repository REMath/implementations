#!/usr/bin/perl -w

use File::Basename;
#require dependency_check.pl;
sub instrument {
	my $file = $_[0];
	my $log = $_[1];
	my $path = '/home/mingwei/Downloads/eglibc-2.13/build/../installdir/lib';
	my $cmd = "cat $log|".'grep "loading an object"|sed \'s/^.*loading an object\s*//g\'|awk \'{print $1}\'|';
	open(FILE,"<$cmd") or die("cannot execute cmd: $cmd\t$!\n");
	while(<FILE>){
		$file = $_;
		$file =~ s/^\s+//;
		if($file =~ m/^(\/|\.\.\/|\.\/)/){
			#print "this is a path name\n";
			$b = basename($file);
			my $c = "ln -s $file $path/$b";
			system($c);
			$c = "./instrument_replace.pl -RI $b";
			system($c);
		}else{	
			my $c = "./instrument_replace.pl -RI $b";
			#system($c);
			#print "this is a file name\n";
		}
	}
}
instrument(shift(@ARGV), shift(@ARGV));
