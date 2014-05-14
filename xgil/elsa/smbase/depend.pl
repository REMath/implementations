#!/usr/bin/perl -w
# depend.pl
# given some compiler command-line args (including source file),
# output a Makefile line of dependencies for compiling that source file

# see
#   http://www.tip.net.au/~millerp/rmch/recu-make-cons-harm.html
#   http://www.cs.berkeley.edu/~smcpeak/autodepend/autodepend.html

if (@ARGV == 0) {
  print(<<"EOF");
usage: $0 -o file.o <gcc compilation arguments>

This script uses 'gcc -MM' to produce compilation dependency
Makefile rules, modifies them a little, and emits them to
stdandard output.

Use the '-o' option to tell this script to which target the rules
should add dependencies; it's not the name of this script's
own output file.
EOF
  exit(0);
}


# Get the output file name, by checking the first option.  If I
# don't find it there, then I won't make any changes to the gcc
# output.  If I *do* find the output file, I have to remove it from
# the argument list because otherwise gcc interprets it as the
# destination of the dependency output.
$outputName = '';
if ($ARGV[0] eq '-o') {
  # syntax where the name is in the next argument
  $outputName = $ARGV[1];
  shift @ARGV;
  shift @ARGV;
}
elsif (substr($ARGV[0], 0, 2) eq '-o') {
  # syntax where the name follows, in the same argument
  $outputName = substr($ARGV[0], 2);
  shift @ARGV;
}


# remove -Wall and add -w so that we don't see warnings when
# preprocessing to find dependencies
@ARGV = grep(!/^-Wall$/, @ARGV);    # remove -Wall
push @ARGV, "-w";                   # add -w

# icc hack: remove -wd too
@ARGV = grep(!/^-wd/, @ARGV);       # remove -wdXXX


# invoke gcc's preprocessor to discover dependencies:
#   -MM   output Makefile rule, ignoring "#include <...>" lines
#         (so as to avoid dependencies on system headers)
$args = join(' ', @ARGV);
#print STDERR ("running: gcc -MM $args\n");
@deps = `gcc -MM $args`;     # unfortunately this does shell interpretation again..
if ($? != 0) {
  # gcc failed, exit similarly
  if ($? >> 8) {
    exit($? >> 8);   # regular exit code
  }
  else {
    exit(&? & 127);  # signal
  }
}


# if we know the gcc output file name, insert that in the
# right place 
if ($outputName) {
  $deps[0] =~ s|.*:|$outputName:|;
}


# Now, for each file on which the target depends, we make a
# command-less, prerequiste-less rule with that file as the target.
# 'make' interprets this to mean that if the file is missing and
# cannot be remade, to regard it as changed but otherwise not an error
# condition.
#
# This is useful because if a .h file is deleted, and the .cc file
# changed to not refer to it, the .d file will still name the old file
# so if we didn't do this trick then 'make' would complain.
@extraRules = ();
for my $line (@deps) {
  @words = split(' ', $line);
  for my $word (@words) {
    if (!$word) {
      # it's an empty word because there was an extra space
      # somewhere; ignore it
    }
    elsif (substr($word, -1) eq ':') {
      # this is the target of the overall dependency list; don't
      # make a special rule for it
    }
    elsif ($word eq '\\') {
      # this is the continuation backslash that 'gcc -M' inserted
      # to try to make the lines fit into 80 columns
    }
    else {
      # make a special rule
      push @extraRules, "$word:\n";
    }
  }
}


print(@deps);
print(@extraRules);
exit(0);

