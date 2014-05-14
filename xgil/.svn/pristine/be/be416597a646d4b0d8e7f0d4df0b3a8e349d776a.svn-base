#!/usr/bin/perl -w
# codepatch.pl
#
# This is sort of like 'patch' but a little higher-level.  I plan
# to extend the script language with constructs as I need them.
#
# 2005-08-04: I am creating a new version in smbase, based on the
# version in verifier but with different command-line syntax.

use strict 'subs';

sub usage {
  print("usage: $0 -o output input script.patch [script2.patch [...]]\n");
  exit(0);
}

if (@ARGV < 4 || $ARGV[0] ne "-o") {
  usage();
}

$output = $ARGV[1];
$input  = $ARGV[2];
$nextArgIndex = 3;        # next script to apply


# read all input
open(INPUT, "<$input") or die("cannot read $input: $!\n");
@lines = <INPUT>;
close(INPUT) or die;


# apply each script in turn
while ($nextArgIndex < @ARGV) {
  $script = $ARGV[$nextArgIndex++];
  open(SCRIPT, "<$script") or die("cannot read $script: $!\n");

  # parse the script
  $slineNum = 0;
  while ($sline = <SCRIPT>) {
    chomp($sline);
    $slineNum++;

    # skip blank lines, comments
    if ($sline =~ m|^\s*(//.*)?$|) { next; }

    # syntax:
    #   replace_line
    #   <source line>
    #   with
    #   <destination line>
    #
    # This is essentially just sed s/^<source>$/<dest>/ except we
    # require that <source> occur exactly once in the input.
    if ($sline eq "replace_line") {
      my $src = <SCRIPT>; chomp($src);
      my $with = <SCRIPT>; chomp($with);
      my $dest = <SCRIPT>; chomp($dest);
      if (!defined($dest) || $with ne "with") {
        fail("malformed replace_line");
      }

      replaceLine($src, $dest);

      $slineNum += 3;
      next;
    }

    # syntax:
    #   add_after_line
    #   <match line>
    #   the_line
    #   <line to put after it>
    if ($sline eq "add_after_line") {
      my $match = <SCRIPT>; chomp($match);
      my $the_line = <SCRIPT>; chomp($the_line);
      my $after = <SCRIPT>; chomp($after);
      if (!defined($after) || $the_line ne "the_line") {
        fail("malformed add_after_line");
      }

      addAfterLine($match, $after);

      $slineNum += 3;
      next;
    }

    # syntax:
    #   comment_function
    #   <function name>
    #
    # Find the given function, and comment it out.
    if ($sline eq "comment_function") {
      my $name = <SCRIPT>;
      chomp($name);

      surroundFunction($name,
                       "#if 0     // comment_function: $name",
                       "#endif // 0");

      $slineNum += 1;
      next;
    }

    # syntax:
    #   add_before_function
    #   <function name>
    #   the_line
    #   <line to add before>
    if ($sline eq "add_before_function") {
      my $name = <SCRIPT>; chomp($name);
      my $the_line = <SCRIPT>; chomp($the_line);
      my $toAdd = <SCRIPT>; chomp($toAdd);
      if (!defined($toAdd) || $the_line ne "the_line") {
        fail("malformed add_before_function");
      }

      surroundFunction($name, $toAdd, "");

      $slineNum += 3;
      next;
    }

    # syntax:
    #   add_after_function
    #   <function name>
    #   the_line
    #   <line to add after>
    if ($sline eq "add_after_function") {
      my $name = <SCRIPT>; chomp($name);
      my $the_line = <SCRIPT>; chomp($the_line);
      my $toAdd = <SCRIPT>; chomp($toAdd);
      if (!defined($toAdd) || $the_line ne "the_line") {
        fail("malformed add_after_function");
      }

      surroundFunction($name, "", $toAdd);

      $slineNum += 3;
      next;
    }

    # syntax:
    #   comment_line
    #   <exact line text to comment out>
    if ($sline eq "comment_line") {
      my $text = <SCRIPT>;
      chomp($text);

      replaceLine($text, "//$text");

      $slineNum += 1;
      next;
    }

    fail("unknown directive");
  }

  close(SCRIPT) or die;
}


# emit the modified input
if (-f $output && ! -w $output) {
  # This is expected when this script is being run for the second or
  # later time; change its permissions.
  #
  # I choose this approach rather than removing the file so that the
  # inode gets re-used, which is sometimes useful.
  makeWritable($output);
}

open(OUTPUT, ">$output") or die("cannot write $output: $!\n");
print OUTPUT (@lines);
close(OUTPUT) or die;

makeNonWritable($output);

exit(0);


# ---------------------- subroutines --------------------------
sub makeWritable {
  my ($fname) = @_;

  # I'm sure there's a fun and complicated way to do this using Perl's
  # system calls, and respecting umask and all that, but I'm lazy.

  if (0!=system("chmod", "u+w", $fname)) {
    exit(4);     # chmod should have printed an error message
  }
}

sub makeNonWritable {
  my ($fname) = @_;

  if (0!=system("chmod", "a-w", $fname)) {
    exit(4);     # chmod should have printed an error message
  }
}


sub fail {
  my ($msg) = @_;
  print STDERR ("$script:$slineNum: $msg\n");
  close(SCRIPT);
  exit(4);
}


sub replaceLine {
  my ($src, $dest) = @_;

  my $found = 0;
  for (my $i=0; $i < @lines; $i++) {
    my $tmp = $lines[$i];
    chomp($tmp);
    if ($tmp eq $src) {
      $lines[$i] = $dest . "\n";
      $found++;
    }
  }

  if ($found == 0) {
    fail("replaceLine: didn't find any matching lines");
  }
  if ($found > 1) {
    fail("replaceLine: found $found matches (only want to find one)");
  }
}


sub addAfterLine {
  my ($match, $after) = @_;

  my @destLines = ();

  my $found = 0;
  for (my $i=0; $i < @lines; $i++) {
    push @destLines, $lines[$i];

    my $tmp = $lines[$i];
    chomp($tmp);
    if ($tmp eq $match) {
      push @destLines, ($after . "\n");
      $found++;
    }
  }

  if ($found == 0) {
    fail("addAfterLine: didn't find any matching lines");
  }
  if ($found > 1) {
    fail("addAfterLine: found $found matches (only want to find one)");
  }

  @lines = @destLines;
}


# Find a function definition and bracket it with two given lines.
# Either line may be empty, indicating no insertion to be done.
# Heuristics for finding the start and end are a little fragile,
# but are sufficient for my present needs.
sub surroundFunction {
  my ($name, $startLine, $endLine) = @_;

  my $i=0;
  my @destLines = ();

  # find the function header
  while ($i < @lines && !atFuncHeader($i, $name)) {
    push @destLines, ($lines[$i++]);
  }
  if ($i == @lines) {
    fail("surroundFunction $name: did not find function header");
  }

  # insert begin-comment
  if ($startLine) {
    push @destLines, ($startLine . "\n");
  }

  # and function header as before
  push @destLines, ($lines[$i++]);

  # the next line should have an open-brace, with some indentation
  my ($braceInd) = ($lines[$i] =~ m/^(\s*)\{/);
  if (!defined($braceInd)) {
    # should not happen now that 'atFuncHeader' checks for this too
    fail("surroundFunction $name: did not find opening brace");
  }
  push @destLines, ($lines[$i++]);

  # look for the close brace
  while ($i < @lines &&
         $lines[$i] !~ m/^$braceInd\}/) {
    push @destLines, ($lines[$i++]);
  }
  if ($i == @lines) {
    fail("surroundFunction $name: did not find closing brace");
  }

  # emit the closing brace
  push @destLines, ($lines[$i++]);

  # close the comment
  if ($endLine) {
    push @destLines, ($endLine . "\n");
  }

  # copy rest of file
  while ($i < @lines && !atFuncHeader($i, $name)) {
    push @destLines, ($lines[$i++]);
  }
  if ($i != @lines) {
    fail("surroundFunction $name: found second function header on line $i");
  }

  # put it all back into 'lines'
  @lines = @destLines;
}


sub atFuncHeader {
  my ($i, $name) = @_;
  my $line = $lines[$i];

  # if name is followed by '(', say yes.
  # don't allow line to begin with '#'.
  if ($line =~ m/^[^\#]*$name\s*\(/) {
    # check next line for open-brace
    if ($lines[$i+1] =~ m/^\s*\{/) {
      return 1;
    }
  }

  return 0;
}


# EOF
