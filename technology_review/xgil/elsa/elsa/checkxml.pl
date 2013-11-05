#!/usr/bin/perl -w
use strict;

# run xml serialization tests

my @firstHundred_in = qw(
t0001.cc t0002.cc t0003.cc t0004.cc t0005.cc
t0006.cc t0007.cc t0008.cc t0009.cc t0010.cc
t0011.cc t0012.cc t0013.cc t0014.cc t0014a.cc
t0015.cc t0016.cc t0017.cc t0018.cc t0019.cc
t0020.cc t0021.cc t0022.cc t0023.cc t0024.cc
t0025.cc t0026.cc t0027.cc t0028.cc t0029.cc
t0030.cc t0030a.cc t0030b.cc t0031.cc t0032.cc
t0033.cc t0034.cc t0035.cc t0036.cc t0037.cc
t0038.cc t0039.cc t0040.cc t0041.cc t0042.cc
t0043.cc t0044.cc t0045.cc t0046.cc t0047.cc
t0048.cc t0049.cc t0050.cc t0051.cc t0052.cc
t0053.cc t0054.cc t0055.cc t0056.cc t0057.cc
t0058.cc t0059.cc t0060.cc t0061.cc t0062.cc
t0063.cc t0064.cc t0065.cc t0066.cc t0067.cc
t0068.cc t0069.cc t0070.cc t0071.cc t0072.cc
t0073.cc t0074.cc t0075.cc t0076.cc t0077.cc
t0078.cc t0079.cc t0080.cc t0081.cc t0082.cc
t0083.cc t0084.cc t0085.cc t0086.cc t0087.cc
t0088.cc t0089.cc t0090.cc t0091.cc t0092.cc
t0093.cc t0094.cc t0095.cc t0096.cc t0097.cc
t0098.cc t0099.cc t0100.cc
);

my @firstHundred = map {"in/$_"} @firstHundred_in;

my @typeTests_in = qw(
t0001.cc t0002.cc t0003.cc t0004.cc t0005.cc
t0006.cc t0007.cc t0008.cc t0009.cc t0010.cc
t0011.cc t0012.cc t0013.cc t0014.cc t0014a.cc
t0015.cc t0016.cc t0017.cc t0018.cc t0019.cc
t0020.cc t0021.cc t0022.cc t0023.cc t0024.cc
t0025.cc);

my @typeTests = map {"in/$_"} @typeTests_in;

sub runtest(@) {
  my (@args) = @_;
  print "**** running test: ", (join(" ", @args)), "\n";
  system(@args);
  if ($?) {
    exit 1;
  }
#    my $exit_value  = $? >> 8;
#    my $signal_num  = $? & 127;
#    my $dumped_core = $? & 128;
}

# test that we halt
#  runtest qw(false);

# update: this is subsumed by the next test
#
# just see if we can parse in the xml without failing
#
# runtest perl ./astxml_check -d outdir @firstHundred;

# just parse and typecheck, but don't elaborate: 1) pretty print, 2)
# render as xml, parse back in, pretty print, 3) diff 1 and 2.
runtest qw(perl ./astxml_check2 -d outdir), @firstHundred;

# Right now just print out the AST and the types; later we will try to
# parse the types back in.
runtest qw(perl ./astxml_check3 -d outdir), @typeTests;
