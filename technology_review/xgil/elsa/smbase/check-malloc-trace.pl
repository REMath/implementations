#!/usr/bin/perl -w
# check the output of a malloc trace for malloc usage bugs

use strict 'subs';

$mallocs=0;
$frees=0;                           
$verbose=0;

if ($#ARGV >= 0 && $ARGV[0] eq "-v") {
  $verbose=1;
}

while ($line = <STDIN>) {
  if (($size, $addr) = ($line =~ /malloc\((\d+)\) yielded (0x.*)$/)) {
    #print ("malloc yielded $addr, size $size\n");
    $mallocs++;

    if (!$size) {
      print ("strange: malloc(0) at $addr\n");
    }

    if ($valid{$addr}) {
      print ("strange: malloc yielded already-valid $addr\n");
    }
    $valid{$addr} = $size;
  }

  elsif (($addr) = ($line =~ /free\((0x.*)\)$/)) {
    #print ("free of $addr\n");
    $frees++;

    if ($valid{$addr}) {
      $valid{$addr} = 0;     # not valid now
    }
    else {
      print ("free of invalid addr $addr\n");
    }
  }
}

if ($verbose) {
  # print all unfreed addresses
  foreach $addr (sort keys %valid) {          
    $size = $valid{$addr};
    if ($size) {
      print ("unfreed addr $addr, size was $size\n");
    }
  }
}

# for some reason, perl was complaining until I said 'STDOUT' too ..
print STDOUT ("saw $mallocs mallocs and $frees frees" .
              ($verbose? "" : " (-v to see unfreed)") . "\n");
