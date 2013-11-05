#!/usr/bin/perl -w
# reconstruct an executable from the intercepted inputs

use strict 'subs';


use FileHandle;                # FileHandle
use Fcntl qw(SEEK_SET);        # for FileHandle random seeks
use Fcntl ':mode';             # for S_IFDIR

$verbose = 0;

for (; @ARGV > 0 && $ARGV[0] =~ m/^-/; shift @ARGV) {
  my $opt = $ARGV[0];

  if ($opt eq "-v") {
    $verbose = 1;
  }
  else {
    die("unknown option: $opt\n");
  }
}

if (@ARGV == 0) {
  print(<<"EOF");
usage: $0 [-v] executable-file
EOF
  exit(0);
}

$execFname = $ARGV[0];

$origCwd = `pwd`;
chomp($origCwd);
         
$fqExecFname = $execFname;
if ($execFname !~ m|^/|) {
  $fqExecFname = $origCwd . "/" . $execFname;
}

# ------------------- 1. read the executable -------------------
# read the ELF sections we care about
$cc1Notes = "";
$ldNotes = "";
{
  # get extents of all sections
  my $objdump = new FileHandle;
  if (!open($objdump, '-|', "objdump -h -w '$execFname'")) {
    die("cannot run objdump: $!\n");
  }
  
  # for reading the section contents
  my $executable = new FileHandle $execFname, 'r';

  # search for info about the relevant ones
  while (<$objdump>) {
    my @field = split(' ', $_);

    if (!( @field >= 7 &&
           $field[0] =~ m|^\d+$| )) {
      # line is a header line, or some other non-section information
      next;
    }

    my $size = hex($field[2]);
    my $offset = hex($field[5]);

    if ($field[1] eq ".note.cc1_interceptor") {
      $cc1Notes = readFilePart($executable, $offset, $size);
    }

    elsif ($field[1] eq ".note.ld_interceptor") {
      $ldNotes = readFilePart($executable, $offset, $size);
    }
  }
  
  if (!$objdump->close()) {
    die("objdump failed (code $?)\n");
  }
  $executable->close() or die;
}


# ------------------- 2. parse ld section -------------------
# parse the ld section to figure out how this executable was made
$ldCwd = "";
$ldOutfile = "";
@ldCommand = ();
@ldTrace = ();
{
  my @ldNotes = split('\n', $ldNotes);
  my $state = 1;
  for (my $i=0; $i < @ldNotes; $i++) {
    my $line = $ldNotes[$i];

    if ($state == 1) {
      if ($line =~ m|^\tcommand:|) {
        $state = 2;
      }
      elsif ($line =~ m|\ttrace:|) {
        $state = 3;
      }
      elsif ($line =~ m|\toutfile:(.*)$|) {
        $ldOutfile = $1;
      }
      elsif ($line =~ m|\tpwd:(.*)$|) {
        $ldCwd = $1;
      }
    }

    elsif ($state == 2) {
      if ($line =~ m|^\t\t(.*)$|) {
        push @ldCommand, ($1);
      }
      elsif ($line =~ m|^\t\)|) {
        $state = 1;
      }
      else {
        die("malformed line in ld command section: $line\n");
      }
    }

    elsif ($state == 3) {
      if ($line =~ m|^\t\t(.*)$|) {
        push @ldTrace, ($1);
      }
      elsif ($line =~ m|^\t\)|) {
        $state = 1;
      }
      else {
        die("malformed line in ld trace section: $line\n");
      }
    }
  }

  if (!$ldCwd) {
    die("missing ld pwd\n");
  }
  if (!$ldOutfile) {
    die("missing ld outfile\n");
  }
  if (@ldCommand == 0) {
    die("missing ld command section\n");
  }
  if (@ldTrace == 0) {
    die("missing ld trace section\n");
  }
}

#print("ldCommand: @ldCommand\n");
#print("ldTrace: @ldTrace\n");
#print("ldOutfile: $ldOutfile\n");



# ------------------- 3. analyze trace data -------------------
# chdir into the link directory so that relative paths might work
$inLdCwd = chdir($ldCwd);

# process the trace
@unintercepted = ();
foreach my $line (@ldTrace) {
  # Three cases:
  #   1. The file $line does not exist anymore.  Then either we
  #      intercepted its construction and so we will reconstruct it
  #      and the link will work, or else the final link will have
  #      undefined symbols.
  #   2. The file $line exists but does not have interception info.
  #      Then it is reported as an unintercepted file but linking
  #      should work.
  #   3. The file $line exists and has interception info.  We will
  #      ignore it, since it got intercepted so it will be
  #      reconstructed.
  #
  # For archives, if the archive exists but some member lacks 
  # interception info, then regard the whole archive as unintercepted.
  # Consequently, (1) it will be reported as such at the end, and (2)
  # the reconstruction link will link the archive as a unit, which
  # should satisfy the needed symbols.

  if (fileExists($line, $inLdCwd)) {
    if (!objHasInterceptionInfo($line)) {
      push @unintercepted, ($line);
    }
  }

  # (archive.a)obj format?
  elsif ($line =~ m|^\((.*\.a)\)(.*)$|) {
    my $archive = $1;
    my $obj = $2;

    if (fileExists($archive, $inLdCwd)) {
      # already decided this archive was unintercepted?
      if (grep {$_ eq $archive} @unintercepted) {
        # yes, no point in testing
      }
      else {
        # no; check this member
        if (!archiveMemberHasInterceptionInfo($archive, $obj)) {
          push @unintercepted, ($archive);
        }
      }
    }
  }
}

# how many of the unintercepted files appear to *not* come from
# some standard system library?
$nonstandard = 0;
foreach my $u (@unintercepted) {
  if ($u !~ m,(^(/usr|/lib))|gcc-lib,) {
    $nonstandard++;
  }
}

if ($verbose) {
  print("unintercepted ($nonstandard nonstandard):\n");
  foreach my $u (@unintercepted) {
    print("  $u\n");
  }
}


# ------------------- 4. reconstruct object files -------------------
# process the cc1 interception data, rebuilding one .o file for
# each section
@rebuiltObjs = ();
eval {
  my $state = 1;               # state of parsing the notes
  my $counter = 0;             # number of objs rebuilt so far

  my $rebuiltAsmFname = "";    # .s file to rebuild
  my $rebuiltObjFname = "";    # .o file to rebuild
  my $origAsmFname = "";       # .s file built during original build
  my $interceptedFname = "";   # .i file intercepted
  my @command = ();            # command used to build .s file

  my @cc1Notes = split('\n', $cc1Notes);
  for (my $i=0; $i < @cc1Notes; $i++) {
    my $line = $cc1Notes[$i];

    if ($state == 1) {              # between sections
      if ($line =~ m|^\(|) {
        $state++;

        $counter++;
        $rebuiltAsmFname = getTemporaryFname("rebuilt-obj-$counter", "s");
        $rebuiltObjFname = getTemporaryFname("rebuilt-obj-$counter", "o");
        
        # if either file exists, remove it so that later I can test
        # for existence to confirm that a program did what I expect
        if (-f $rebuiltAsmFname) {
          unlink($rebuiltAsmFname) or die;
        }
        if (-f $rebuiltObjFname) {
          unlink($rebuiltObjFname) or die;
        }

        # reset per-objfile stats so we don't get accidental contamination
        $origAsmFname = "";
        $interceptedFname = "";
        @command = ();
      }
    }

    elsif ($state == 2) {           # in a section
      if ($line =~ m|^\tintercepted:(.*)$|) {
        $interceptedFname = $1;
      }
      elsif ($line =~ m|^\toutput:(.*)$|) {
        $origAsmFname = $1;
      }
      elsif ($line =~ m|^\tcommand:|) {
        $state++;
      }
      elsif ($line =~ m|^\)|) {
        $state--;

        # did we see everything we were supposed to?
        if (!$origAsmFname) {
          die("cc1 command section missing 'output'\n");
        }
        if (!$interceptedFname) {
          die("cc1 command section missing 'intercepted'\n");
        }
        if (@command == 0) {
          die("cc1 command section missing 'command'\n");
        }

        # replace the original asm fname with the new one
        my $found = 0;
        for (my $i=0; $i < @command; $i++) {
          if ($command[$i] eq $origAsmFname) {
            $found++;
            $command[$i] = $rebuiltAsmFname;
          }
        }
        if ($found != 1) {
          die("cc1 command section missing original asm fname\n");
        }
        
        # uncompress the intercepted input file
        if (-f "${interceptedFname}.gz") {
          if (0!=system("gunzip -c '${interceptedFname}.gz' >'${interceptedFname}'")) {
            die("gunzip ${interceptedFname}.gz failed\n");
          }
        }
        else {
          die("intercepted file is missing: ${interceptedFname}.gz\n");
        }
        
        # rebuild the .s file
        diagnostic("invoking: @command");
        if (0!=system(@command)) {
          die("failed: @command\n");
        }
        unlink($interceptedFname);
        if (! -f $rebuiltAsmFname) {
          die("cc1 did not build $rebuiltAsmFname!\n");
        }
        
        # rebuild the .o file
        #
        # NOTE: I am assuming that I do not need the original command line
        # arguments to the assembler.  If it turns out that I do, then I
        # will have to intercept the call to 'as' and insert the command
        # line arguments into the .cc1_interceptor section before passing
        # the input to the real assembler.  I think that may have a
        # measurable effect on performance...
        if (0!=system("as", "-o", $rebuiltObjFname, $rebuiltAsmFname)) {
          die("as failed to assemble $rebuiltAsmFname\n");
        }
        unlink($rebuiltAsmFname);
        if (! -f $rebuiltObjFname) {
          die("as did not write $rebuiltObjFname!\n");
        }

        # remember this file name, as it will be an input to the
        # linker later, when we try to build the executable
        push @rebuiltObjs, ($rebuiltObjFname);
      }
    }

    elsif ($state == 3) {           # in 'command'
      if ($line =~ m|^\t\)|) {
        $state--;
      }
      elsif ($line =~ m|^\t\t(.*)$|) {
        push @command, ($1);
      }
      else {
        die("malformed line in cc1 command section: $line\n");
      }
    }
  }
}; # eval
if ($@) {
  # clean up
  foreach my $r (@rebuiltObjs) {
    unlink($r);
  }
  die($@);
}

if ($verbose) {
  print("rebuiltObjs:\n");
  foreach my $r (@rebuiltObjs) {
    print("  $r\n");
  }
}


# ------------------- 5. clean the ld command -------------------
# Next, clean the 'ld' command line.
#
# I want to remove all of the arguments that specify object files to
# link against, plus a couple of other arguments.  The tricky part is
# that I have to be able to tell when an option takes an additional
# argument, so I know to skip that too.
#
# The purpose of retaining *any* arguments is the supposition that the
# extra flags may be needed for some program to run properly after
# linking.  Arguably, we don't care about that since the main thing is
# to ensure we have all the symbols, but I will try anyway; being able
# to actually run a reconstructed program is that much more assurance
# that interception was done correctly.

# This info is from
#
#   http://www.gnu.org/software/binutils/manual/ld-2.9.1/html_chapter/ld_2.html#SEC3
#
# The description there appears to be somewhat inconsistent, sometimes
# using "--" and sometimes "-" for what appear to be multiletter 
# options.  There could well be bugs in my interpretation.

# After an initial attempt, I have discovered that parsing ld's
# arguments is as hard as parsing gcc's arguments.  GNU ld tries to be
# compatible with a dozen or so different system linkers, with
# incompatible argument languages.  It's a messy pile of ad-hoc
# guesses and heuristics, further affected by the -m (linker
# emulation) option.
#                   
# Therefore I am switching strategies: I will only retain a few
# options that (1) I can reliably parse, and (2) I estimate have a
# high likelihood of being relevant.

$keepNext = 1;         # retain /usr/bin/ld

for (my $i=0; $i < @ldCommand; $i++) {
  my $opt = $ldCommand[$i];

  # forced to keep this option?
  if ($keepNext) {
    push @newLdCommand, ($opt);
    $keepNext = 0;
    next;
  }

  # drop all non-arguments
  if ($opt !~ m|^-|) {
    next;
  }

  # drop --trace
  if ($opt eq "-t" || $opt eq "--trace") {
    next;
  }

  # drop -l and -L and -o
  if ($opt =~ m/^(-l|-L|-o|--library|--library-path|--output)/) {
    # unless we are really unlucky, the argument to these options
    # (if provided as a separate element of @ldCommand) will be
    # classified as a non-argument and dropped, without having
    # to do extra work
    next;
  }

  # non-argument forms that might be needed...
  if ($opt =~ m/^-d[cp]?$/ ||
      $opt =~ m/^-[EinNr]$/ ||
      $opt =~ m/^-?-(export-dynamic|shared|Bshareable|Ur)$/ ||
      $opt =~ m/^--(nmagic|omagic|relocateable|traditional-format)$/) {
    push @newLdCommand, ($opt);
    next;
  }

  # argument-taking single-letter forms that might be needed
  if ($opt =~ m/^-[efhmu](.*)$/) {
    push @newLdCommand, ($opt);
    if (!$1) {
      $keepNext = 1;
    }
    next;
  }

  # argument-taking double-dash multiletter forms that might be needed
  if ($opt =~ m/^--(entry|undefined|defsym|wrap)(=.*)?$/) {
    push @newLdCommand, ($opt);
    if (!$2) {
      $keepNext = 1;
    }
    next;
  }

  # argument-taking single- or double-dash multiletter forms
  if ($opt =~ m/^-?-(soname|dynamic-linker|Tbss|Tdata|Ttext)(=.*)?$/) {
    push @newLdCommand, ($opt);
    if (!$2) {
      $keepNext = 1;
    }
    next;
  }

  # drop everything else
}


# ------------------- 6. rebuild the executable -------------------
# assemble the previous section's results along with the sets
# of object files to link
push @newLdCommand, (@rebuiltObjs, @unintercepted);

# specify an output file
$reconstructedExec = $fqExecFname . "-recons";
push @newLdCommand, ("-o", $reconstructedExec);
    
# run ld
diagnostic("invoking: @newLdCommand");
system(@newLdCommand);
if ($?) {                                              
  my $code = $?;
  printf("leaving %d temporary files in /tmp/%s\n", $#rebuiltObjs+1, $ENV{"USER"});
  my $exit_value  = $code >> 8;
  my $signal_num  = $code & 255;
  if ($exit_value) {
    exit($exit_value);
  }
  die("recons: ld died with signal $signal_num\n");
}

# clean up
foreach my $r (@rebuiltObjs) {
  unlink($r);
}

# summarize results
print("Rebuilt $reconstructedExec.\n");
printf("There were %d unintercepted sources, of which %d are nonstandard.\n",
       $#unintercepted+1, $nonstandard);
exit(0);


# ------------------- subroutines -------------------
sub archiveMemberHasInterceptionInfo {
  my ($archiveFname, $objFname) = @_;
  
  # extract the archive member
  my $tmpfile = getTemporaryFname("reconstruct", ".o");
  if (0!=system("ar p '$archiveFname' '$objFname' >$tmpfile")) {
    die("ar p '$archiveFname' '$objFname' failed (code $?)\n");
  }
  
  # test it
  my $ret = objHasInterceptionInfo($tmpfile);
                   
  # clean up
  unlink($tmpfile);
  return $ret;
}


sub objHasInterceptionInfo {
  my ($fname) = @_;
  
  if (!open(DUMP, '-|', "objdump -h -w '$fname'")) {
    die("cannot run objdump: $!\n");
  }
                  
  my $line;
  my $ret = 0;
  while (defined($line = <DUMP>)) {
    my @field = split(' ', $line);

    if (!( @field >= 7 &&
           $field[0] =~ m|^\d+$| )) {
      # line is a header line, or some other non-section information
      next;
    }

    if ($field[1] eq ".note.cc1_interceptor") {
      $ret = 1;
      last;
    }
  }

  # it is possible this premature close may trigger a SIGPIPE
  # in objdump, and hence a "failure" return from 'close';
  # therefore ignore the return code  
  close(DUMP);

  return $ret;
}


sub fileExists {
  my ($fname, $allowRelative) = @_;

  if ($fname =~ m|^/|) {
    return -f $fname;
  }
  elsif (!$allowRelative) {
    # we are not allowing relative names; regard the file
    # as nonexistent because it is a relative name
    return 0;
  }
  else {
    return -f $fname;
  }
}


sub readFilePart {
  my ($fh, $offset, $size) = @_;

  my $buffer;
  $fh->seek($offset, &SEEK_SET);
  $fh->read($buffer, $size);
  $buffer =~ s/\0//g;
  return $buffer;
}

  
# get a temporary fname that is not subject to race condition
# attacks, etc.
sub getTemporaryFname {
  my ($str, $ext) = @_;

  my $user = $ENV{"USER"};
  if (!defined($user) || !$user) {
    die("no defined USER\n");
  }

  if (!-d "/tmp/$user") {
    # create it
    if (!mkdir("/tmp/$user", 0777)) {
      die("cannot mkdir /tmp/$user: $!\n");
    }
  }

  # ensure it has proper ownership and permissions
  my @fields = lstat("/tmp/$user");
  #                   ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
  #                    $atime,$mtime,$ctime,$blksize,$blocks)
  my $mode = $fields[2];
  my $uid = $fields[4];

  if (!S_ISDIR($mode)) {
    die("/tmp/$user must be a directory\n");
  }

  if ($mode & (S_IWGRP | S_IWOTH)) {
    die("/tmp/$user must not be group- or world-writable\n");
  }

  if ($uid != $>) {
    die("/tmp/$user must be owned by current effective user (id $>)\n");
  }

  # All of the checks above ensure that the directory is private
  # to the current user, and therefore immune from mischief.  So,
  # it is fine to now just return a filename, rather than (say)
  # an open file handle.

  return "/tmp/${user}/${str}-$$.${ext}";
}


sub diagnostic {
  if ($verbose) {
    print("recons: ", @_, "\n");
  }
}

# EOF
