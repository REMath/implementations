#!/usr/bin/perl -w

use strict;

die "Usage:\nrun_till_fix CNF_Filename [Num_Max_Iterations]" if (@ARGV < 1);
    
my $file = $ARGV[0];
my $max_iteration = @ARGV > 1 ? $ARGV[1] : 1000;
my $last_cls_count = 0; 
my $filename = $file."_itr_0";
$filename =~ s/.*\///;

system("cp $file $filename");

$file =~ s/.*\///;

for (my $i = 0; $i < $max_iteration; ++$i) {
  
  open INPUT, "<$filename" or die "$!\n";
  
  my @tokens;
  
  while (<INPUT>) {
    @tokens = split / /;
    last if ($tokens[0] eq "p");
  }
  
  last if $tokens[3] == $last_cls_count;
  
  $last_cls_count = $tokens[3];
  
  system("zchaff $filename");
  system("zverify_df $filename resolve_trace -core");
  my $j = $i + 1;
  $filename = $file."_itr_".$j;
  system("mv unsat_core.cnf $filename");
}
