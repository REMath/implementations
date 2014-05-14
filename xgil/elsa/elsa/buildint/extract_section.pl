#!/usr/bin/perl -w
# See License.txt for copyright and terms of use

# Extract a section from an ELF file.

# By Ben Liblit and originally released as part of "The Cooperative
# Bug Isolation Project" http://http.cs.berkeley.edu/~liblit/sampler/

use strict;
#use 5.008;			# for safe pipe opens using list form of open

use Fcntl qw(SEEK_SET);
use FileHandle;


########################################################################

my $exit_value = 0;

die "Usage: $0 <section-name> [<executable> | <object> | <library>] ...\n" unless @ARGV >= 2;

my @argv1;
my $test_only;                  # just test for the existance of the section
my $quiet;

foreach my $name (@ARGV) {
  if ($name eq '-t') {
    $test_only++;
  } elsif ($name eq '-q') {
    $quiet++;
  } else {
    push @argv1, $name;
  }
}

my $sectionName = shift (@argv1);

foreach my $name (@argv1) {
    my $objdump = new FileHandle;
#      open $objdump, '-|', 'objdump', '-h', '-w', $name
    open($objdump, '-|', "objdump -h -w $name")
	or die "cannot run objdump: $!\n";

    my $size;
    my $offset;
    while (<$objdump>) {
	my @field = split;
	next unless @field >= 7;
	next unless $field[1] eq $sectionName;
	next unless $field[0] =~ /^\d+$/;
	$size = hex $field[2];
	$offset = hex $field[5];
	last;
    }

    unless (defined $offset) {
	warn "\"$sectionName\" section is missing\n" unless $quiet;
        $exit_value = 1;
	next;
    }

    unless ($size) {
	warn "\"$sectionName\" section is empty\n" unless $quiet;
        $exit_value = 1;
	next;
    }

    if (!$test_only && !$quiet) {
      my $buffer;
      my $executable = new FileHandle $name, 'r';
      $executable->seek($offset, &SEEK_SET);
      $executable->read($buffer, $size);
      $buffer =~ s/\0//g;
      print $buffer;
    }
}

exit $exit_value;
