#!/usr/bin/perl -w
# configure script for elkhound

use strict 'subs';

# default location of smbase relative to this package
$SMBASE = "../smbase";
$req_smcv = 1.03;            # required sm_config version number
$thisPackage = "elkhound";

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
%flags = (
  "loc" => 1,

  "eef" => 0,
  "gcs" => 0,
  "gcsc" => 0,
  "crs" => 0,

  "subconfigure" => 1
);
$AST = "../ast";

# arguments to pass to sub-configures
@c_args = ();


# copy from %flags to individual global variables
sub copyFlagsToGlobals {
  $loc = $flags{loc};

  $eef = $flags{eef};
  $gcs = $flags{gcs};
  $gcsc = $flags{gcsc};
  $crs = $flags{crs};

  $subconfigure = $flags{subconfigure};

  # test consistency of configuration
  if ($gcs && !$eef) {
    die "GCS requires EEF\n";
  }
  if ($gcsc && !$gcs) {
    die "GCSC requires GCS\n";
  }
}
copyFlagsToGlobals();


sub usage {
  standardUsage();

  print(<<"EOF");
package options:
  -prof              enable profiling
  -devel             add options useful while developing
  -loc[=0/1]:        enable/disable source location tracking [enabled]
  -action:           enable use of "-tr action" to see parser actions
  -compression[=0/1]:  enable/disable all table compression options [disabled]
    -eef[=0/1]         enable/disable EEF compression [disabled]
    -gcs[=0/1]         enable/disable GCS compression [disabled]
    -gcsc[=0/1]        enable/disable GCS column compression [disabled]
    -crs[=0/1]         enable/disable CRS compression [disabled]
  -fastest:          turn off all Elkhound features that are not present
                     in Bison, for the purpose of performance comparison
                     (note that Elsa will not work in this mode)
  -nosub:            do not invoke subdirectory configure scripts
  -ast=<dir>:        specify where the ast library is [$AST]
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
    push @c_args, $arg;
  }

  elsif ($arg eq "devel") {
    push @CCFLAGS, "-Werror";
    push @c_args, $arg;
  }

  elsif ($arg eq "loc") {
    $flags{loc} = getBoolArg();
  }

  elsif ($arg eq "action") {
    push @CCFLAGS, "-DACTION_TRACE=1";
  }

  elsif ($arg eq "fastest") {
    # the idea is I can say
    #   $ ./configure -fastest
    #   $ make clean; make
    #   $ ./perf -tests c -iters 5
    # to verify that I'm still within 3% of Bison (at least
    # when compiled with gcc-2.95.3)
    $flags{loc} = 0;
    $flags{debug} = 0;
    push @CCFLAGS,
      ("-DUSE_RECLASSIFY=0",        # no token reclassification
       "-DUSE_KEEP=0",              # don't call keep() functions
       "-DNDEBUG_NO_ASSERTIONS",    # disable all xassert() calls
       "-DDO_ACCOUNTING=0",         # don't count stack nodes, etc.
       "-DENABLE_YIELD_COUNT=0");   # don't check for yield-then-merge at runtime
    push @c_args, "-DUSE_RECLASSIFY=0";
  }

  elsif ($arg eq "nosub") {
    $flags{subconfigure} = 0;
  }

  elsif ($arg eq "ast") {
    $AST = getOptArg();
    if ($AST !~ m|^/|) {
      push @c_args, "-ast=../$AST";
    }
    else {
      push @c_args, "-ast=$AST";
    }
  }

  elsif ($arg =~ "compression|eef|gcs|gcsc|crs") {
    my $value = getBoolArg();

    if ($arg eq "compression") {
      $flags{eef} = $value;
      $flags{gcs} = $value;
      $flags{gcsc} = $value;
      $flags{crs} = $value;
    }
    else {
      $flags{$arg} = $value;
    }
  }

  else {
    die "unknown option: $arg\n";
  }
}

copyFlagsToGlobals();
finishedOptionProcessing();

# summarize compression flags
@compflags = ();
for $k (keys %flags) {
  if ($k eq "eef" || $k eq "gcs" || $k eq "gcsc" || $k eq "crs") {
    if ($flags{$k}) {
      push @compflags, $k;
    }
  }
}
if (@compflags) {
  $compflags = join(',', @compflags);
}
else {
  $compflags = "<none>";
}



# ------------------ needed components ---------------
test_smbase_presence();

test_CXX_compiler();

# does the compiler want me to pass "-I."?  unfortunately, some versions
# of gcc-3 will emit an annoying warning if I pass "-I." when I don't need to
print("checking whether compiler needs \"-I.\"... ");
$cmd = "$CXX -c @CCFLAGS cc2/testprog.cc";
if (0!=system("$cmd >/dev/null 2>&1")) {
  # failed without "-I.", so try adding it
  $cmd = "$CXX -c -I. @CCFLAGS cc2/testprog.cc";
  if (0!=system("$cmd >/dev/null 2>&1")) {
    my $wd = `pwd`;
    chomp($wd);
    die "\n" .
        "I was unable to compile a simple test program.  I tried:\n" .
        "  cd $wd\n" .
        "  $cmd\n" .
        "Try it yourself to see the error message.  This needs be fixed\n" .
        "before Elkhound will compile.\n";
  }

  # adding "-I." fixed the problem
  print("yes\n");
  push @CCFLAGS, "-I.";
}
else {
  print("no\n");
}


# ast
if (! -f "$AST/asthelp.h") {
  die "I cannot find asthelp.h in `$AST'.\n" .
      "The ast library is required for elkhound.\n" .
      "If it's in a different location, use the -ast=<dir> option.\n";
}


$PERL = get_PERL_variable();


# ------------------ config.summary -----------------
$summary = getStandardConfigSummary();

$summary .= <<"OUTER_EOF";
cat <<EOF
  loc:         $loc
  compression: $compflags
EOF
OUTER_EOF

writeConfigSummary($summary);


# ------------------- config.status ------------------
writeConfigStatus("PERL" => "$PERL",
                  "AST" => "$AST");

# extend config.status
open(OUT, ">>config.status") or die("could not append to config.status: $!\n");
print OUT (<<"OUTER_EOF");

cat >glrconfig.h.tmp <<EOF
// glrconfig.h
// do not edit; generated by ./configure

EOF

sed -e "s|\@GLR_SOURCELOC\@|$loc|g" \\
    -e "s|\@eef\@|$eef|g" \\
    -e "s|\@gcs\@|$gcs|g" \\
    -e "s|\@gcsc\@|$gcsc|g" \\
    -e "s|\@crs\@|$crs|g" \\
  <glrconfig.h.in >>glrconfig.h.tmp

# see if the new glrconfig.h differs from the old; if not, then
# leave the old, so 'make' won't think something needs to be rebuilt
if diff glrconfig.h glrconfig.h.tmp >/dev/null 2>&1; then
  # leave it
  echo "glrconfig.h is unchanged"
else
  echo "creating glrconfig.h ..."

  # overwrite it, and make it read-only
  mv -f glrconfig.h.tmp glrconfig.h
  chmod a-w glrconfig.h
fi


OUTER_EOF

close(OUT) or die;
chmod 0755, "config.status";


# ----------------- final actions -----------------
# invoke sub-configures
if ($subconfigure) {
  chdir("c") or die;
  my $tmp = join(' ', ("./configure", @c_args));
  print("Invoking $tmp in 'c' directory..\n");
  run("./configure", @c_args);
  chdir("..") or die;
}

# run the output file generator
run("./config.status");

print("\nYou can now run make, usually called 'make' or 'gmake'.\n");


exit(0);


# silence warnings
pretendUsed($thisPackage);

# EOF
