#!/usr/bin/perl -w
# intercept a build tool invocation, do some processing, and
# then run the real program

use strict 'subs';

# 0: quiet
# 1: write to log file
# 2: write to terminal
$verbose = 1;

# under what directory should all my output be placed?
$outputDir = $ENV{"BUILDINT_DEST"};
if (!defined($outputDir)) {
  $outputDir = $ENV{"HOME"} . "/preproc";
}

$cwd = `pwd`;
chomp($cwd);

# where is this script?
($scriptDir, $progName) = ($0 =~ m|^(.*)/([^/]*)$|);    # divide at last '/'
if (!defined($scriptDir)) {     # no '/' at all
  $scriptDir = $cwd;
  $progName = $0;
}

sub isCompilerDriver {
  my ($s) = @_;
  return $s eq "gcc" || $s eq "g++" || $s eq "cc" || $s eq "c++";
}
if (isCompilerDriver($progName) && $verbose == 1) {
  # an extra newline before each invocation of the driver program helps
  # to mark the groups of related lines
  writeToLog("\n");
}

diagnostic("invoked with args: " . join(' ', @ARGV));

# where is the real program?
$realProgram = "";
if ($progName eq "cc1" ||
    $progName eq "cc1plus") {
  # these are just the original invocation name plus "-real"
  $realProgram = $0 . "-real";
}
else {
  # search for first occurrence of the program in the path *after* the
  # one which caused (a symlink to) this script to be found
  my @path = split(':', $ENV{"PATH"});
  foreach my $p (@path) {
    if ($p eq $scriptDir) { next; }

    if (-x "$p/$progName") {
      # found it
      $realProgram = "$p/$progName";
      last;
    }
  }
}
if (!$realProgram) {
  die("$0: could not find the real $progName in the path\n");
}

# copy the arguments; the wrapper code can modify them before execution
@av = @ARGV;

# what program am I emulating?
if (isCompilerDriver($progName)) {
  gcc_wrapper();
}
elsif ($progName eq "cpp") {
  cpp_wrapper();
}
elsif ($progName eq "cc1" ||
       $progName eq "cc1plus") {
  cc1_wrapper();
}
elsif ($progName eq "ld") {
  ld_wrapper();
}
elsif ($progName eq "as") {
  # nop; this is a placeholder; the only effect of the wrapper
  # will have been to log the call if $verbose != 0
}
else {
  die("$0: I do not know how to wrap $progName\n");
}

# run the real program
diagnostic("invoking: $realProgram " . join(' ', @av));
exec($realProgram, @av);


sub diagnostic {
  if ($verbose == 1) {
    writeToLog("$0: ", @_, "\n");
  }
  elsif ($verbose == 2) {
    print("$0: ", @_, "\n");
  }
}

sub writeToLog {
  # open and close the logfile each time so that I do not hold it
  # open across the invocation of some other program that might also
  # want to write to it (in *theory* if everyone uses append mode,
  # and unix append semantics are implemented correctly, and no one
  # accidentally buffers something, then it would not matter; but I
  # play it safe)
  open(LOG, ">>$outputDir/interceptor.log")
    or die("cannot write $outputDir/interceptor.log: $!\n");
  print LOG (@_);
  close(LOG);
}

# "a/b/c" -> "a/b/"
# "/a" -> "/"
# "a" -> ""
sub dirname {
  my ($str) = @_;

  if ($str =~ m|^(.*/)[^/]*$|) {
    return $1;
  }
  else {
    return "";
  }
}


# make the given directory plus any needed parent directories
sub mkdirParents {
  my ($d) = @_;

  if (0!=system("mkdir -p '$d'")) {
    die("failed to mkdir -p");
  }
}


# backtick but no shell interpretation and capture stderr;
# child's exit status available in $? upon return
sub betterBacktick {
  # @_ has the program + args, first element is the program

  # fork a child process
  my $childPid = open(CHILD, "-|");
  if (!defined($childPid)) {
    die("cannot fork: $!\n");
  }

  # child
  if (!$childPid) {
    # send stderr to same place as stdout, namely the pipe to
    # the parent
    close(STDERR);
    open(STDERR, ">&STDOUT");

    # exec the program
    if (!exec(@_)) {
      # this error message will go to stdout, but oh well
      print("exec: $!\n");
      exit(40);
    }
    else {
      die("not reached");  # this conditional exists only to pacify perl -w
    }
  }

  # parent
  my @ret = <CHILD>;
  close(CHILD);      # child's exit status goes into $?
  return @ret;
}


# ----------------------- gcc --------------------------
sub gcc_wrapper {
  # find out its version number and where its spec file lives
  @gccInfo = `"$realProgram" -v 2>&1`;
  if ($? != 0) {
    die("$0: $realProgram -v failed\n");
  }
  $gccSpecDir = "";
  $gccVersion = "";
  foreach $line (@gccInfo) {
    my ($s) = ($line =~ m|specs from (.*)/specs$|);
    if (defined($s)) {
      $gccSpecDir = $s;
      next;
    }

    ($s) = ($line =~ m|version (\d+\.\d+\.\d+)|);
    if (defined($s)) {
      $gccVersion = $s;
      next;
    }
  }
  if (!$gccSpecDir || !$gccVersion) {
    die("$0: failed to parse output of $realProgram -v\n");
  }
  if ($gccSpecDir !~ m|^/|) {
    die("$0: gccSpecDir should be an absolute path\n");
  }

  # get the gcc version components; we are playing with gcc internals
  # here, and those change over time
  my ($major, $minor, $patch) = ($gccVersion =~ m|(\d+)\.(\d+)\.(\d+)|);
  if (!defined($patch)) {
    die("wtf?");
  }

  # make a symlink copy of the gcc spec directory
  #
  # I am naming the copy according to how the original spec was named,
  # so that it will not collide with a spec copy of another installed
  # compiler.
  $copyOfSpecDir = $outputDir . "/specdirs" . $gccSpecDir;
  if (-f "$copyOfSpecDir/cc1") {
    # the directory and link already exists; assume it is good to go
  }
  else {
    # create it, etc.
    diagnostic("creating $copyOfSpecDir");

    # link the existing contents
    my $cmd = <<"EOF";
rm -rf '$copyOfSpecDir'       &&
mkdir -p '$copyOfSpecDir'     &&
cd '$copyOfSpecDir'           &&
ln -s '$gccSpecDir'/* .
EOF
    if (0!=system($cmd)) {
      die("failed to make $copyOfSpecDir\n");
    }

    # did we get cc1?
    if (-f "$copyOfSpecDir/cc1") {
      $cmd = <<"EOF";
cd '$copyOfSpecDir'           &&
mv cc1 cc1-real               &&
mv cc1plus cc1plus-real
EOF
      if (0!=system($cmd)) {
        die("failed to move cc1\n");
      }
    }
    elsif ($gccSpecDir =~ m|^(.*)/\.\./lib/gcc/(.*)$|) {
      # in gcc >=3.4, cc1 does not live in the spec directory,
      # and I do not know the proper way to find it, but this
      # seems to work
      #
      # example spec dir:
      #   /slack8/home/scott/opt/gcc-3.4.0/bin/../lib/gcc/i686-pc-linux-gnu/3.4.0
      # example corresponding libexec dir:
      #   /slack8/home/scott/opt/gcc-3.4.0/bin/../libexec/gcc/i686-pc-linux-gnu/3.4.0/cc1
      my $gccLibexecDir = "$1/../libexec/gcc/$2";
      if (-f "$gccLibexecDir/cc1") {
        $cmd = <<"EOF";
cd '$copyOfSpecDir'                          &&
ln -s '$gccLibexecDir/cc1' cc1-real          &&
ln -s '$gccLibexecDir/cc1plus' cc1plus-real
EOF
        if (0!=system($cmd)) {
          die("failed to symlink cc1[plus] from $gccLibexecDir\n");
        }
      }
      else {
        die("could not find cc1 in $copyOfSpecDir or $gccLibexecDir\n");
      }
    }
    else {
      die("could not find cc1 in $copyOfSpecDir\n");
    }

    # finally, put links to the script directory, pointing
    # at links to this script
    $cmd = <<"EOF";
cd '$copyOfSpecDir'           &&
ln -s '$scriptDir'/cc1 .      &&
ln -s '$scriptDir'/cc1plus .
EOF
    if (0!=system($cmd)) {
      die("failed to symlink cc1 from $scriptDir\n");
    }
  }

  # point gcc at the new spec directory
  #
  # I had been using GCC_EXEC_PREFIX, but for some reason I can't get
  # it to work with gcc-3.4; gcc just seems to ignore the value when
  # it is searching for subprocess executables.  So, use -B instead.
  unshift(@av, "-B${copyOfSpecDir}/");

  # tell gcc to do preprocessing separately
  if ($major >= 3) {
    unshift(@av, "--no-integrated-cpp");
  }

  # decided it was not worth the hassle
  if (0) {
    # pass it a special spec file too
    if ("$major.$minor" >= 3.4) {
      unshift(@av, "-specs=$scriptDir/interceptor.specs.gcc-3.4");
    }
    elsif ($major <= 2) {
      unshift(@av, "-specs=$scriptDir/interceptor.specs.gcc-2");
    }
    else {
      unshift(@av, "-specs=$scriptDir/interceptor.specs.gcc-3");
    }
  }
}


# ----------------------- cpp ------------------------
sub cpp_wrapper {
  # Get rid of any -P arguments.
  #
  # -P tells the preprocessor not to emit "#" line markers into the
  # preprocessed output.  We assume that if it is specified, it is
  # because someone was trying to make the build process faster; but
  # the premise of build interception is that we want as much info as
  # possible, whatever the cost, so we remove -P.
  #
  # Note that this is *also* done by the gcc specs file above, for
  # when gcc invokes its own private 'cpp'; the wrapper here is for
  # the public one usually sitting in /usr/bin.
  @av = grep {!/^-P$/} @av;
}


# ----------------------- cc1 -----------------------
sub cc1_wrapper {
  # gcc-3 invokes cc1 with -E when it wants to only do preprocessing;
  # just pass that case through
  if (grep {/^-E$/} @av) {
    return;
  }

  # make a unique id; this will be incorporated into the name of the
  # file that contains the intercepted data; this ensures that no data
  # is lost, but that also means that intercepted files from old runs
  # will hang around indefinitely
  my $unique = sprintf("$$-%d", time());

  # scan the argument list for input filenames
  my $origFname = "";      # name of .c file preprocessed to get $inputFname
  my $inputFname = "";     # name of .i file about to be compiled
  @av = grep {
    # the actual command-line argument syntax to cc1 is somewhat
    # complicated; we just assume that if the argument ends with ".i"
    # or ".ii" then it is the input file we want
    if ($_ =~ m|\.ii?$|) {
      $inputFname = $_;

      # discard this element of the list because when we run cc1
      # we will be passing the name of the *intercepted* file,
      # not the original input file
      0;
    }

    # this argument comes from the special spec file given to gcc
    elsif ($_ =~ m|^---build_interceptor-orig_filename=(.*)$|) {
      $origFname = $1;
      0;         # discard
    }

    else {
      1;         # keep
    }
  } @av;

  my $dumpBase = "";       # name of .c file supplied with -dumpbase
  for (my $i=0; $i < @av; $i++) {
    # in gcc-3, this is the original input filename without its
    # directory component; gcc-2 does not pass this
    if ($av[$i] eq "-dumpbase") {
      $dumpBase = $av[$i+1];
    }
  }

  # construct the name of the file where we will save the
  # intercepted preprocessor input
  my $interceptFname = "STDIN.i";
  {
    if ($origFname) {
      $interceptFname = $origFname;
    }

    elsif ($dumpBase) {
      $interceptFname = $dumpBase;
    }

    elsif ($inputFname) {
      $interceptFname = $inputFname;
    }

    # change the extension to .i or .ii
    my $ext = ($progName eq "cc1"? ".i" : ".ii");
    $interceptFname =~ s|\.[^.]*$|$ext|;

    # attach the $unique string
    $interceptFname =~ s|\.([^.]*)$|-$unique.$1|;

    # make the name absolute
    if ($interceptFname !~ m|^/|) {
      $interceptFname = "$cwd/$interceptFname";
    }

    # put it under $outputDir
    $interceptFname = $outputDir . $interceptFname;
  }

  # create the parent directories of $interceptFname
  mkdirParents(dirname($interceptFname));

  # create the intercepted file
  if ($inputFname) {
    if (0!=system("cp '$inputFname' '$interceptFname'")) {
      die("cp failed");
    }
    diagnostic("saved input file to $interceptFname");
  }
  else {
    # read the input from stdin, save it in the intercepted file, and
    # then we will give that filename explicitly to cc1
    diagnostic("saving stdin to $interceptFname");
    open (INTER, ">$interceptFname") or die("cannot write $interceptFname: $!\n");
    my $line;
    while (defined($line = <STDIN>)) {
      print INTER ($line);
    }
    close (INTER) or die;
  }

  # specify it as the input file for cc1
  unshift @av, $interceptFname;

  # search argument list for output file name and the dumpbase
  # (whatever that is)
  my $outputFname = "";
  my $dumpbase = "";
  for (my $i=0; $i < @av; ++$i) {
    if ($av[$i] =~ /^-o/) {
      if ($av[$i] eq '-o') {
        $outputFname = $av[$i+1];
        ++$i;
      }
      else {
        ($outputFname) = ($av[$i] =~ /^-o(.*)$/);
      }
    }

    elsif ($av[$i] eq '-dumpbase') {
      $dumpbase = $av[$i+1];
    }
  }

  # input file specified but no output file: output file name is
  # $inputFname with .s extension
  if (!$outputFname && $inputFname) {
    $outputFname = $inputFname;
    $outputFname =~ s|\.[^.]*$|.s|;
  }

  # run cc1
  {
    # prefix with the name of the program we are calling
    unshift @av, $realProgram;

    diagnostic("invoking: " . join(' ', @av));
    system(@av);
    if ($?) {
      my $exit_value  = $? >> 8;
      my $signal_num  = $? & 255;
      if ($exit_value) {
        exit($exit_value);
      }
      die("$0: $progName died with signal $signal_num\n");
    }
  }

  # Compress the intercepted file.  This done because preprocessor
  # output is usually very big but *highly* (~80%) compressible.  It
  # is probably faster to uncompress the data than it would be to read
  # all of the disk blocks containing the uncompressed data.  (It is
  # slower to compress than to write, especially with write buffering,
  # but I still think it is worth it.)
  if (0!=system("gzip", $interceptFname)) {
    die("gzip failed");
  }

  # construct extra data to add to the generated assembly
  my $metadata = <<'END';         # do not interpolate
.section	.note.cc1_interceptor,"",@progbits
END

  # sm: I changed the format of this section significantly.  Here is
  # why:
  #
  # I removed the 'raw_args' output because I do not think it would be
  # very useful.  Furthermore, instead of 'run_args' as a
  # colon-separated string, I emit those commands as the multi-line
  # 'command' (the way 'raw_args' used to be emitted).  I envision
  # using 'command' to reconstruct the .o file from the intercepted .i
  # file.
  #
  # I also removed 'infile' because that often uselessly names a gcc
  # temporary file.  I renamed 'tmpfile' to 'intercepted' to make it
  # clear what its role is (in a build process, many things are
  # "temporary").  Finally, I added 'output' so this section is then
  # a self-contained transformation description:
  #
  #   To make 'output',
  #   run 'command',
  #   which reads (only) 'intercepted'.
  #
  # Note that 'output' is a .s file which is likely to be a gcc
  # temporary file too.  Therefore the consumer of this output may
  # want to search for 'output' in 'command' and replace it with a
  # different output filename.
  #
  # 'output' may also be an empty string, meaning that 'command'
  # writes to stdout.  Previously this script had used "-" to mean
  # stdout, but that seems like pointless ambiguity in this context.
  # (Some programs' command line syntax uses such a convention, but
  # that is only because it is awkward to pass empty string as a
  # command line argument.)

  $metadata .= <<"END";
	.ascii "("
	.ascii "\\n\\tpwd:${cwd}"
	.ascii "\\n\\tdollar_zero:$0"
	.ascii "\\n\\tcommand: ("
END

  foreach my $a (@av) {
    $metadata .= <<"END";
	.ascii "\\n\\t\\t${a}"
END
  }

  $metadata .= <<"END";
	.ascii "\\n\\t)"
	.ascii "\\n\\tdumpbase:${dumpbase}"
	.ascii "\\n\\tintercepted:${interceptFname}"
	.ascii "\\n\\toutput:${outputFname}"
	.ascii "\\n)\\n"
END

  # append the constructed data to the output
  if (!$outputFname) {
    print STDOUT ($metadata);
  }
  else {
    open(OUT, ">>$outputFname") or die("cannot append to $outputFname: $!\n");
    print OUT ($metadata);
    close(OUT) or die;
  }

  # do not return; the default action of the common part of the script
  # above would invoke cc1 again
  exit(0);
}


# --------------------------- ld --------------------------
# The purpose of this wrapper is to remember the set of files that got
# used in the construction of an executable, to allow later
# reconstruction.
#
# The primary technique here is to pass the --trace option so that
# 'ld' will print out the files it uses.  However, this is complicated
# by the fact that it is not easy to tell which output lines are from
# --trace and which are other things.  So we use some simple
# heuristics.
sub ld_wrapper {
  # has the trace flag already been passed?
  my $traceAlready = 0;
  if (grep {m/^(-t|--trace)$/} @av) {
    # yes, already present
    $traceAlready = 1;
  }
  else {
    # add it
    unshift @av, "--trace";
  }

  # run the real ld and capture its output
  diagnostic("invoking: $realProgram " . join(' ', @av));
  my @output = betterBacktick($realProgram, @av);
  my $ld_exit_value  = $? >> 8;
  my $ld_signal_num  = $? & 255;

  # search among the output lines for trace output; remove them
  # from @output unless $traceAlready
  my @trace = ();
  @output = grep {
    my $line = $_;
    chomp($line);

    # heuristic #1: if $line is the name of a file, assume it is
    # tracing output
    if (-f $line) {
      push @trace, ($line);
      $traceAlready;    # keep only if --trace already specified
    }

    # heuristic #2: if it is of the form "(string1.a)string2" and
    # "string1.a" is the name of a file, it is tracing output
    elsif ($line =~ m|^\((.*).a\).*$|) {
      if (-f "$1.a") {
        push @trace, ($line);
        $traceAlready;
      }
      else {
        1;      # keep
      }
    }

    elsif ($line =~ m|$progName: mode |) {
      # this is not tracing output I want, but *is* caused by
      # the --trace flag; drop it unless the user said --trace
      $traceAlready;
    }

    else {
      1;        # keep
    }
  } @output;

  # print the remaining output lines; this should be exactly what
  # the user would have seen if we didn't mess with the command line,
  # except it is all going to stdout
  print STDOUT (@output);

  # did 'ld' fail?
  if ($ld_exit_value) {
    exit($ld_exit_value);
  }
  if ($ld_signal_num) {
    die("$0: $progName died with signal $ld_signal_num\n");
  }

  # were we merely getting the version?
  if (grep {m/^(-v|-V|--version)$/} @av) {
    exit(0);
  }

  # find the output file name
  my $outfile = "";
  for (my $i=0; $i < @av; ++$i) {
    if ($av[$i] =~ m|^-o(.*)$|) {
      if ($1) {
        $outfile = $1;
      }
      else {
        $outfile = $av[$i+1];
        ++$i;
      }
    }
  }
  if (!$outfile) {
    $outfile = "a.out";
  }

  # make it absolute
  if ($outfile !~ m|^/|) {
    $outfile = "$cwd/$outfile";
  }

  # write a temporary file containing the text of the section
  # to add to the exectuable
  my $tmpfile = "$outputDir/tmp/ld-interceptor-$$";
  mkdirParents(dirname($tmpfile));
  open(TMP, "> $tmpfile") or die("cannot write $tmpfile: $!");

  print TMP (<<"END");
(
\tpwd:$cwd
\tdollar_zero:$0
\toutfile:$outfile
\tcommand: (
\t\t$realProgram
END

  # this is saved to aid reconstruction of $outfile from binary sources
  for my $a (@av) {
    print TMP ("\t\t$a\n");
  }

  print TMP (<<"END");
\t)
\ttrace: (
END

  # this is saved to aid reconstruction from intercepted source code
  for my $t (@trace) {
    print TMP ("\t\t$t\n");
  }

  print TMP (<<"END");
\t)
)
END

  close(TMP) or die $!;

  # attach the section text to the executable
  if (0!=system("objcopy", $outfile, '--add-section', ".note.ld_interceptor=$tmpfile")) {
    die("objcopy failed");
  }
  unlink($tmpfile);

  # do not return; the default action of the common part of the script
  # above would invoke cc1 again
  exit(0);
}


# EOF
