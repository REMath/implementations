#!/usr/bin/perl
sub check_translated_one {
	my $dep_bin = $_[0];
	my $c = "readelf -S $dep_bin|grep mytext |";
	open(DEP, $c) or die("cannot open file".$dep_bin.": $!");
	my $flag = 0;
	while(<DEP>){
		if($_ =~ m/^\s*\[([0-9]+)\].*$/){
			$flag = 1;
			last;
		}
	}
	close(DEP);
	return $flag;
}
sub check_translated {
	my $bin = $_[0];
	my $cmd = "/lib/linux-ld.so.4 --list $bin |";
	open(DEPLIST, $cmd) or die("cannot open file".$bin.": $!");
	while(<DEPLIST>){
		my $line = $_;
		if($line =~ m/^\s*([^\s]+)\s*=>\s*([^\s]+)\s*.*$/){
			my $dep_bin = $2;
			my $dep_name = $1;
			my $flag = check_translated_one($dep_bin);
			if($flag == 1){
				print "translated $line";
			}else{
				print "original   $line";
			}
		}else{
			print $line;
		}
	}
}
unless (caller) {
  print "This is the script being executed\n";
  check_translated(shift(@ARGV));
}

