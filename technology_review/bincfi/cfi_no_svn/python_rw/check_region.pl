#!/usr/bin/perl -w

$filename = shift(@ARGV);
$idx = 0;
@regions = ();
$pre_addr = -1;
$sum = 0;
open($F, "<$filename") or die("cannot open file:$filename, $!\n");
while(<$F>){
	if($_ =~ m/^([0-9a-f]+)$/){
		my $a = hex($1);
		my $a_str = $1;
		if($pre_addr == -1){
			$pre_addr = hex($a_str);
			$pre_addr_str = $a_str;
			next;
		}
		$region[$idx] = $a - $pre_addr;
		$sum += $region[$idx];
		print "$pre_addr_str\t$a_str\t$region[$idx]\n";
		$pre_addr = $a;
		$pre_addr_str = $a_str;
		$idx += 1;
	}
}
print "average length: ". ($sum/@region)."\n";
