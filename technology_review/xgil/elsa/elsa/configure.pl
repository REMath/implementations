#!/usr/bin/perl -w
# configure script for elsa

use strict 'subs';

# default location of smbase relative to this package
$SMBASE = "../smbase";
$req_smcv = 1.03;            # required sm_config version number
$thisPackage = "elsa";

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

# defaults
@LDFLAGS = ("-g -Wall");
$AST = "../ast";
$ELKHOUND = "../elkhound";
$USE_GNU = "1";
$USE_KANDR = "1";
$GCOV_MODS = "";


sub usage {
  standardUsage();

  print(<<"EOF");
package options:
  -prof              enable profiling
  -gcov=<mods>       enable coverage testing for modules <mods>
  -devel             add options useful while developing (-Werror)
  -gnu=[0/1]         enable GNU extensions? [$USE_GNU]
  -kandr=[0/1]       enable K&R extensions? [$USE_KANDR]
  -ast=<dir>:        specify where the ast system is [$AST]
  -elkhound=<dir>:   specify where the elkhound system is [$ELKHOUND]
  -useSerialNumbers: give serial numbers to some objects for debugging
EOF
}


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

  elsif ($arg eq "prof") {
    push @CCFLAGS, "-pg";
    push @LDFLAGS, "-pg";
  }

  elsif ($arg eq "gcov") {
    $GCOV_MODS = getOptArg();
  }

  elsif ($arg eq "devel") {
    push @CCFLAGS, "-Werror";
  }

  elsif ($arg eq "ast") {
    $AST = getOptArg();
  }
  elsif ($arg eq "elkhound") {
    $ELKHOUND = getOptArg();
  }

  elsif ($arg eq "gnu") {
    $USE_GNU = getBoolArg();
  }
  elsif ($arg eq "kandr") {
    $USE_KANDR = getBoolArg();
  }

  elsif ($arg eq "useSerialNumbers") {
    push @CCFLAGS, "-DUSE_SERIAL_NUMBERS=1";
  }

  else {
    die "unknown option: $arg\n";
  }
}

finishedOptionProcessing();


# ------------------ check for needed components ----------------
test_smbase_presence();

test_CXX_compiler();

# ast
if (! -f "$AST/asthelp.h") {
  die "I cannot find asthelp.h in `$AST'.\n" .
      "The ast system is required for elsa.\n" .
      "If it's in a different location, use the -ast=<dir> option.\n";
}

# elkhound
if (! -f "$ELKHOUND/glr.h") {
  die "I cannot find glr.h in `$ELKHOUND'.\n" .
      "The elkhound system is required for elsa.\n" .
      "If it's in a different location, use the -elkhound=<dir> option.\n";
}

$PERL = get_PERL_variable();


# ------------------ config.summary -----------------
$summary = getStandardConfigSummary();

$summary .= <<"OUTER_EOF";
cat <<EOF
  LDFLAGS:     @LDFLAGS
  SMBASE:      $SMBASE
  AST:         $AST
  ELKHOUND:    $ELKHOUND
  USE_GNU:     $USE_GNU
  USE_KANDR:   $USE_KANDR
EOF
OUTER_EOF

if ($GCOV_MODS) {
  $summary .= "echo \"  GCOV_MODS:   $GCOV_MODS\"\n";
}

writeConfigSummary($summary);


# ------------------- config.status ------------------
writeConfigStatus("LDFLAGS" => "@LDFLAGS",
                  "SMBASE" => "$SMBASE",
                  "AST" => "$AST",
                  "ELKHOUND" => "$ELKHOUND",
                  "PERL" => "$PERL",
                  "USE_GNU" => "$USE_GNU",
                  "USE_KANDR" => "$USE_KANDR",
                  "GCOV_MODS" => "$GCOV_MODS");


# ----------------- final actions -----------------
# run the output file generator
run("./config.status");

print("\nYou can now run make, usually called 'make' or 'gmake'.\n");

exit(0);


# silence warnings
pretendUsed($thisPackage);
