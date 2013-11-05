#!/usr/bin/perl -w
# test prevailing CRLF<->LF translation

use strict 'subs';

if (@ARGV == 0) {
  # start the test
  exec("$0 -test <crlf.txt >stdout.txt");
}

if ($ARGV[0] ne "-test") {
  die("wrong usage");
}

report("OS: $^O\n");

report("CRLF->LF on inputs NOT opened by perl: ");
$line = <STDIN>;
if (length($line) == 1) {
  report("yes\n");
}
elsif (length($line) == 2) {
  report("no\n");
}
else {
  die;
}

report("CRLF->LF on inputs opened by perl: ");
open(IN, "<crlf.txt") or die;
$line = <IN>;
close(IN);
if (length($line) == 1) {
  report("yes\n");
}
elsif (length($line) == 2) {
  report("no\n");
}
else {
  die;
}

report("LF->CRLF on outputs NOT opened by perl: ");
print("\n");
close(STDOUT);   # flushes too
$len = getFileSize("stdout.txt");
if ($len == 1) {
  report("no\n");
}
elsif ($len == 2) {
  report("yes\n");
}
else {
  die;
}

report("LF->CRLF on outputs opened by perl: ");
open(OUT, ">output.txt") or die;
print OUT ("\n");
close(OUT) or die;
$len = getFileSize("output.txt");
if ($len == 1) {
  report("no\n");
}
elsif ($len == 2) {
  report("yes\n");
}
else {
  die;
}

exit(0);


sub report {
  print STDERR (@_);
}

sub getFileSize {
  my ($fname) = @_;

  my @details = stat($fname);

  # how do I tell if 'stat' failed?

  return $details[7];
}

# EOF
