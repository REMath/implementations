# sm_config.pm
# Perl module for package configuration
#
# For now, the idea is simply to have a common place to put
# a library of routines that my individual directory configure
# scripts can use.

# autoflush so progress reports work
$| = 1;

# smbase config version number; also serves as an
# initialization routine
sub get_sm_config_version {
  $main::CC = getEnvOrDefault("CC", "gcc");
  $main::CXX = getEnvOrDefault("CXX", "g++");
  @main::CCFLAGS = ("-g", "-Wall", "-Wno-deprecated", "-D__UNIX__");
  $main::debug = 0;
  $main::target = 0;
  $main::no_dash_g = 0;
  $main::no_dash_O2 = 0;
  $main::exe = "";

  return 1.04;

  # 1.01: first version
  #
  # 1.02: added the PERLIO=crlf stuff
  #
  # 1.03: 2005-04-23: moved a bunch of argument processing into sm_config
  #
  # 1.04: 2005-05-04: re-added -no-dash-g and -no-dash-O2
}

# standard prefix of the usage string
sub standardUsage {
  print(<<"EOF");
usage: ./configure [options]

influential environment variables:
  CC                 C compiler [$main::CC]
  CXX                C++ compiler [$main::CXX]

standard (sm_config) options:
  -h:                print this message
  -debug[=0/1]:      enable debugging options [$main::debug]
  -target=<target>:  cross compilation target, e.g., "i386-mingw32msvc"
  -no-dash-g:        disable -g
  -no-dash-O2:       disable -O2
EOF

  if ($main::thisPackage ne "smbase") {
    print("  -smbase=<dir>:     specify where the smbase library is [$main::SMBASE]\n");
  }
  print("\n");
}


# process standard command-line options; the option name is
# in $main::option, and its argument (if any) in $main::value;
# this returns true if it handles the argument
sub handleStandardOption {
  my $arg = $main::option;
  my $val = $main::value;

  if ($arg eq "h" ||
      $arg eq "help") {
    main::usage();
    exit(0);
  }

  elsif ($arg eq "debug") {
    $main::debug = getBoolArg();
    return 1;
  }

  elsif ($arg eq "target") {
    $main::target = getOptArg();
    if ($target eq "i386-mingw32msvc") {
      $main::exe = ".exe";
      @main::CCFLAGS = grep { $_ ne "-D__UNIX__" } @main::CCFLAGS;
      push @main::CCFLAGS, "-D__WIN32__";
      return 1;
    }
    else {
      die("at the moment, only the 'i386-mingw32msvc' cross target is supported\n");
    }
  }

  elsif ($arg eq "smbase") {
    $main::SMBASE = getOptArg();
  }
  
  elsif ($arg eq "no-dash-g") {
    $main::no_dash_g = 1;
  }
  
  elsif ($arg eq "no-dash-O2") {
    $main::no_dash_O2 = 1;
  }

  else {
    return 0;
  }
}


# run after all options have been processed
sub finishedOptionProcessing {
  if (!$main::debug) {
    push @CCFLAGS, ("-O2", "-DNDEBUG");
  }

  if (!$main::target) {
    my $os = `uname -s`;
    chomp($os);
    if ($os eq "Linux") {
      push @main::CCFLAGS, "-D__LINUX__";
    }
  }
  
  if ($main::no_dash_g) {
    @main::CCFLAGS = grep { $_ ne "-g" } @main::CCFLAGS;
  }

  if ($main::no_dash_O2) {
    @main::CCFLAGS = grep { $_ ne "-O2" } @main::CCFLAGS;
  }
}


# get a value from the environment, or use a supplied default
sub getEnvOrDefault {
  my ($var, $def) = @_;

  my $ret = $ENV{$var};
  if (!defined($ret)) {
    $ret = $def;
  }

  return $ret;
}

# use smbase's $BASE_FLAGS if I can find them
sub get_smbase_BASE_FLAGS {
  my $smbase_flags = `$main::SMBASE/config.summary 2>/dev/null | grep BASE_FLAGS`;
  if (defined($smbase_flags)) {
    ($main::BASE_FLAGS = $smbase_flags) =~ s|^.*: *||;
    chomp($main::BASE_FLAGS);
  }
}


# get smbase's compile flags, as a starting point
sub get_smbase_compile_flags {
  my $cfgsum = "$main::SMBASE/config.summary";
  if (! -x $cfgsum) {
    die("$cfgsum is not executable.\n" .
        "smbase should be configured first.\n");
  }
  my @lines = `$main::SMBASE/config.summary 2>/dev/null`;
  foreach my $line (@lines) {
    my ($name, $value) = ($line =~ m/^\s*(\S+)\s*:\s*(\S.*)$/);
                                 #       name    :   value
    if (!defined($value)) { next; }
    
    if ($name eq "CC") {
      $main::CC = $value;
    }
    elsif ($name eq "CXX") {
      $main::CXX = $value;
    }
    elsif ($name eq "CCFLAGS") {
      @main::CCFLAGS = split(' ', $value);
    }
    elsif ($name eq "CROSSTARGET") {
      $main::target = $value;
    }
    elsif ($name eq "EXE") {
      $main::exe = $value;
    }
  }
}


# get an argument to an option
sub getOptArg {
  if (!$value) {
    die("option $option requires an argument\n");
  }
  return $value;
}

# for a boolean option:
#   -foo       -> true
#   -foo=1     -> true
#   -foo=0     -> false
sub getBoolArg {
  if ($value eq "" || $value eq "1") {
    return 1;
  }
  elsif ($value eq "0") {
    return 0;
  }
  else {
    die("option $option expects either no argument, or arg 0 or 1\n");
  }
}


# detect whether we need PERLIO=crlf
sub getPerlEnvPrefix {
  # It's important to do this test on a file in the current
  # directory, since the behavior under cygwin can change
  # depending on the mount charactersics of the file's location.
  #
  # It is also important that the file be opened by the shell
  # instead of perl; when perl opens the file itself, things 
  # work differently.
  if (0!=system("perl -e 'print(\"a\\n\")' >tmp.txt")) {
    die;
  }

  my $sz1 = getFileSize("tmp.txt");
  if ($sz1 == 2) {
    # no LF->CRLF translation done on output, I think we're ok
    #print("(case 1) ");
    return "";
  }
  if ($sz1 != 3) {
    die("expected file size of 2 or 3");
  }

  open(TMP, "<tmp.txt") or die;
  my $line = <TMP>;
  close(TMP) or die;
  unlink("tmp.txt");

  if (length($line) == 2) {
    # reading did CRLF->LF, so again we're ok
    #print("(case 2) ");
    return "";
  }
  elsif (length($line) == 3) {
    # reading was raw, so if we wrote again then we'd have
    # CRCRLF; this is the condition that "PERLIO=crlf" fixes
    #print("(case 3) ");
    
    # make this the default for *this* perl session too;
    # but it does not work ...
    #use open OUT => ":crlf";

    return "PERLIO=crlf ";
  }
  else {
    die("expected line length of 2 or 3");
  }
}

sub getFileSize {
  my ($fname) = @_;

  my @details = stat($fname);

  # how do I tell if 'stat' failed?

  return $details[7];
}

sub get_PERL_variable {
  print("checking how to run perl... ");

  my $ret = getPerlEnvPrefix() . "perl";

  print($ret . "\n");
  return $ret;
}


sub run {
  my $code = system(@_);
  checkExitCode($code);
}

sub checkExitCode {
  my ($code) = @_;
  if ($code != 0) {
    # hopefully the command has already printed a message,
    # I'll just relay the status code
    if ($code >> 8) {
      exit($code >> 8);
    }
    else {
      exit($code & 127);
    }
  }
}

sub pretendUsed {
}


sub slurpFile {
  my ($fname) = @_;
  open(IN, "<$fname") or die("can't open $fname: $!\n");
  my @ret = <IN>;
  close(IN) or die;
  return @ret;
}


# -------------- does the C++ compiler work? --------------
sub test_CXX_compiler {
  my $wd = `pwd`;
  chomp($wd);

  my $testcout = "testcout" . $main::exe;
  print("Testing C++ compiler ...\n");
  my $cmd = "$main::CXX -o $testcout @main::CCFLAGS $main::SMBASE/testcout.cc";
  if (system($cmd)) {
    # maybe problem is -Wno-deprecated?
    printf("Trying without -Wno-deprecated ...\n");
    @main::CCFLAGS = grep { $_ ne "-Wno-deprecated" } @main::CCFLAGS;
    $cmd = "$main::CXX -o $testcout @main::CCFLAGS $main::SMBASE/testcout.cc";
    if (system($cmd)) {
      print(<<"EOF");

I was unable to compile a really simple C++ program.  I tried:
  cd $wd
  $cmd

Please double-check your compiler installation.

Until this is fixed, smbase (and any software that depends on it) will
certainly not compile either.
EOF
      exit(2);
    }
  }

  if (!$target) {
    if (system("./$testcout")) {
      print(<<"EOF");

I was able to compile testcout.cc, but it did not run.  I tried:
  cd $wd
  $cmd

and then
  ./$testcout      (this one failed)

A frequent cause for this error is a misconfiguration of the language
runtime libraries.

For example, by default g++ installs libstdc++ into /usr/local/lib,
but on many systems this directory is not searched by the loader.
Solutions would include symlinking or copying the files into /usr/lib,
adding /usr/local/lib to the library search path, or reinstalling g++
with a different --prefix argument to its configuration script.

Until this is fixed, smbase (and any software that depends on it) will
certainly not run either.
EOF
      exit(2);
    }

    print("C++ compiler seems to work\n");
  }
  else {
    print("because we are in cross mode, I will not try running '$testcout'\n",
          "but it might be a good idea to try that yourself\n");
  }

  # make a variant, CFLAGS, that doesn't include -Wno-deprecated
  @main::CFLAGS = grep { $_ ne "-Wno-deprecated" } @main::CCFLAGS;
}


# ------------------ config.summary -----------------
sub getStandardConfigSummary {
  print("\n");

  my $ret = (<<"EOF");
#!/bin/sh
# config.summary

echo "$main::thisPackage configuration summary:"
echo "  command:     ./configure @main::ARGV"
echo ""
echo "Compile flags:"
echo "  CC:          $main::CC"
echo "  CXX:         $main::CXX"
echo "  CCFLAGS:     @main::CCFLAGS"
EOF

  if ($main::target) {
    $ret .= "echo \"  CROSSTARGET: $main::target\"\n";
  }
  if ($exe) {
    $ret .= "echo \"  EXE:         $main::exe\"\n";
  }

  return $ret;
}


sub writeConfigSummary {
  my ($summary) = @_;
  
  open (OUT, ">config.summary") or die("cannot write config.summary: $!\n");

  print OUT ($summary);
  print OUT ("echo \"\"\n");

  close(OUT) or die;
  chmod 0755, "config.summary";
}


# ------------------- config.status ------------------
sub writeConfigStatus {
  my @pairs = @_;

  # create a program which will create the Makefile
  open(OUT, ">config.status") or die("can't make config.status");

  # preamble
  print OUT (<<"OUTER_EOF");
#!/bin/sh
# config.status

# this file was created by ./configure

if [ "\$1" = "-reconfigure" ]; then
  # re-issue the ./configure command
  exec ./configure @main::ARGV
fi

# report on configuration
./config.summary

echo "creating Makefile ..."

# overcome my chmod below
rm -f Makefile

cat >Makefile <<EOF
# Makefile for smbase
# NOTE: generated by ./configure, do not edit

EOF

# variable substitution
sed -e "s|\@CCFLAGS\@|@main::CCFLAGS|g" \\
    -e "s|\@CFLAGS\@|@main::CFLAGS|g" \\
    -e "s|\@CC\@|$main::CC|g" \\
    -e "s|\@CXX\@|$main::CXX|g" \\
    -e "s|\@CROSSTARGET\@|$main::target|g" \\
    -e "s|\@EXE\@|$main::exe|g" \\
    -e "s|\@SMBASE\@|$main::SMBASE|g" \\
OUTER_EOF

  # package-specific substitution
  for ($i=0; $i < @pairs; $i += 2) {
    my $a = $pairs[$i];
    my $b = $pairs[$i+1];
    #           -e  "s|@foo@|bar|g" \           (example)
    print OUT ("-e \"s|\@$a\@|$b|g\" \\\n");
  }

  # postamble
  print OUT (<<"EOF");
  <Makefile.in >>Makefile

# discourage editing ..
chmod a-w Makefile


EOF

  close(OUT) or die;
  chmod 0755, "config.status";
}


sub test_smbase_presence {
  if (! -f "$main::SMBASE/nonport.h") {
    die "I cannot find nonport.h in `$main::SMBASE'.\n" .
        "The smbase library is required for $thisPackage.\n" .
        "If it's in a different location, use the -smbase=<dir> option.\n";
  }
}


1;
# EOF
