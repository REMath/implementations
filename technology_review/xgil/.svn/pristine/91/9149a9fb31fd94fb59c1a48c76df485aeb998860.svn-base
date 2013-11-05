#!/usr/bin/perl -w
# configure script for smbase

use strict 'subs';

require sm_config;

$SMBASE = ".";
get_sm_config_version();
$thisPackage = "smbase";

sub usage {
  standardUsage();

  print(<<"EOF");
package options:
  -prof              enable profiling
  -devel             add options useful while developing smbase
  -debugheap         turn on heap usage debugging
  -traceheap         print messages on each malloc and free
EOF
# this option is obscure, so I won't print it in the usage string
# -icc               turn on options for Intel's compiler
}

# defaults (also see sm_config.pm)
$DEBUG_HEAP = 0;
$TRACE_HEAP = 0;


# global variables holding information about the current command-line
# option being processed
$option = "";
$value = "";

# process command-line arguments
foreach $optionAndValue (@ARGV) {
  # ignore leading '-' characters, and split at first '=' (if any)
  ($option, $value) =
    ($optionAndValue =~ m/^-*([^-][^=]*)=?(.*)$/);
                      #      option     = value
                      
  my $arg = $option;

  if (handleStandardOption()) {
    # handled by sm_config.pm
  }

  elsif ($arg eq "prof") {
    push @CCFLAGS, "-pg";
  }

  elsif ($arg eq "devel") {
    push @CCFLAGS, "-Werror";
  }

  elsif ($arg eq "debugheap") {
    $DEBUG_HEAP = 1;
  }
  elsif ($arg eq "traceheap") {
    $TRACE_HEAP = 1;
  }

  # 9/19/04: I spent some time getting smbase to build under
  # the Intel C++ 8.1 compiler; these are the options I used.
  elsif ($arg eq "icc") {
    # compiler executables
    $CC = "icc";
    $CXX = "icpc";

    # diagnostic suppression:
    #  444: Wants virtual destructors
    #  1418: external definition with no prior declaration
    #  810: Conversion might lose sig.digs (can't suppress with cast!)
    #  271: trailing comma is nonstandard
    #  981: operands are evaluated in unspecified order
    #  279: controlling expression is constant
    #  383: value copied to temporary, reference to temporary used
    #  327: NULL reference is not allowed
    #  1419: external declaration in primary source file
    push @CCFLAGS, "-wd444,1418,810,271,981,279,383,327,1419";
  }
  
  else {
    print STDERR ("unknown option: $arg\n");
    exit(2);
  }
}

finishedOptionProcessing();


# -------------- external tools tests ---------------------
test_CXX_compiler();


# ------------------ config.summary -----------------
$summary = getStandardConfigSummary();

if ($DEBUG_HEAP) {
  $summary .= "echo \"  DEBUG_HEAP:  $DEBUG_HEAP\"\n";
}
if ($TRACE_HEAP) {
  $summary .= "echo \"  TRACE_HEAP:  $TRACE_HEAP\"\n";
}

writeConfigSummary($summary);


# ------------------- config.status ------------------
writeConfigStatus("DEBUG_HEAP" => "$DEBUG_HEAP",
                  "TRACE_HEAP" => "$TRACE_HEAP");


# ----------------- final actions -----------------
# run the output file generator
run("./config.status");

print("\nYou can now run make, usually called 'make' or 'gmake'.\n");

exit(0);


# silence warnings
pretendUsed($thisPackage);
pretendUsed($CC);
pretendUsed($CXX);


# the code below is never executed as part of smbase/configure.pl;
# it is here so it can be easily found to copy into the client
# configuration scripts

# -------------- BEGIN common block ---------------
# do an initial argument scan to find if smbase is somewhere else
for (my $i=0; $i < @ARGV; $i++) {
  my ($d) = ($ARGV[$i] =~ m/-*smbase=(.*)/);
  if (defined($d)) {
    $SMBASE = $d;
  }
}

# try to load the sm_config module
eval {
  push @INC, ($SMBASE);
  require sm_config;
};
if ($@) {
  die("$@" .     # ends with newline, usually
      "\n" .
      "I looked for smbase in \"$SMBASE\".\n" .
      "\n" .
      "You can explicitly specify the location of smbase with the -smbase=<dir>\n" .
      "command-line argument.\n");
}

# check version number
$smcv = get_sm_config_version();
if ($smcv < $req_smcv) {
  die("This package requires version $req_smcv of sm_config, but found\n" .
      "only version $smcv.\n");
}
# -------------- END common block ---------------

# -------------- BEGIN common block 2 -------------
# global variables holding information about the current command-line
# option being processed
$option = "";
$value = "";

# process command-line arguments
foreach $optionAndValue (@ARGV) {
  # ignore leading '-' characters, and split at first '=' (if any)
  ($option, $value) =
    ($optionAndValue =~ m/^-*([^-][^=]*)=?(.*)$/);
                      #      option     = value

  my $arg = $option;

  if (handleStandardOption()) {
    # handled by sm_config.pm
  }
  # -------------- END common block 2 -------------
}


# EOF
