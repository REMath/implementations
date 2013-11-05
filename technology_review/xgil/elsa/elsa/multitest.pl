#!/usr/bin/perl -w
# run a program on an input file, then (if the input has some
# stylized comments) re-run, expecting an error

use strict 'subs';
use Config;

$comment = "//";    # comment syntax
$selectedError = "";
$keepTemps = 0;
$contin = 0;
@failures = ();     # if $contin, track which configurations failed

$me = "multitest";

while (@ARGV && $ARGV[0] =~ m/^-/) {
  my $opt = $ARGV[0];
  shift @ARGV;

  if ($opt eq "-errnum") {
    $selectedError = $ARGV[0];
    shift @ARGV;
    next;
  }

  if ($opt eq "-keep") {
    $keepTemps = 1;
    next;
  }

  if ($opt eq "-contin") {
    $contin = 1;
    next;
  }

  die("$me: unknown argument: $opt\n");
}

if (@ARGV < 2) {
  print(<<"EOF");
usage: $0 [options] program [args...] input.cc

This will first invoke the command line as given, expecting that to
succeed.  Then, it will scan input.cc (which must be the last argument
on the command line) for any lines of the forms:

  ${comment}ERROR(n): <some code>
  <some code>     ${comment}ERRORIFMISSING(n):

If it finds them, then for each such 'n' the lines ERROR(n) will be
uncommented (and "ERROR(n)" removed), and lines ERRORIFMISSING(n)
commented-out, and the original command executed again.  These
additional runs should fail.

options:
  -errnum n     Only test ERROR(n) (does not test original).
  -keep         Keep temporaries even when they succeed.
EOF

  exit(0);
}


# excerpt from perlipc man page
defined $Config{sig_name} || die "No sigs?";
$i = 0;
foreach $name (split(' ', $Config{sig_name})) {
  $signo{$name} = $i;
  $signame[$i] = $name;
  $i++;
}

$sigint = $signo{INT};
$sigquit = $signo{QUIT};
#print("sigint: $sigint\n");


$fname = $ARGV[@ARGV - 1];
#print("fname: $fname\n");

($fnameBase, $fnameExt) = ($fname =~ m|^(.*)(\.[^./]*)$|);
                                   #    bse ext
if (!defined($fnameExt)) {
  $fnameBase = $fname;
  $fnameExt = "";     # no '.' present anywhere (after last '/')
}

# try once with no modifications
if (!$selectedError) {
  $code = mysystem(@ARGV);
  if ($code != 0) {
    failed("original", $code);
  }
}

# bail, or if $contin, just keep track
sub failed {
  my ($config, $code) = @_;

  if ($contin) {
    push @failures, ($config);
  }
  else {
    exit($code);
  }
}


# read the input file
open(IN, "<$fname") or die("can't open $fname: $!\n");
@lines = <IN>;
close(IN) or die;

# see what ERROR/ERRORIFMISSING lines are present
%codes = ();
foreach $line (@lines) {
  my ($miss, $code) = ($line =~ m|${comment}ERROR(IFMISSING)?\((\d+)\):|);
  if (defined($code)) {
    $codes{$code} = 1;
    $miss .= " ";     # pretend used
  }
}

# get sorted keys
@allkeys = (sort {$a <=> $b} (keys %codes));
$numkeys = @allkeys;
if ($numkeys == 0) {
  # no error tags
  exit(0);
}

# consider each in turn
$testedVariations = 0;
foreach $selcode (@allkeys) {
  if ($selectedError &&
      $selectedError ne $selcode) {
    next;
  }
  $testedVariations++;

  print("-- selecting ERROR($selcode) --\n");

  my $tempfname = "${fnameBase}.error${selcode}${fnameExt}";

  # run through the lines in the file, generating a new file
  # that has the selected lines uncommented
  open(OUT, ">$tempfname") or die("can't create $tempfname: $!\n");
  foreach $line (@lines) {
    my ($miss, $code, $rest) =
      ($line =~ m|${comment}ERROR(IFMISSING)?\((\d+)\):(.*)$|);
      #                  miss          code    rest
    if (defined($code) && $selcode == $code) {
      if ($miss) {
        # ERRORIFMISSING: we want to comment the whole line
        print OUT ("${comment} $line");
      }
      else{
        # ERROR: we want to uncomment what follows the "ERROR" marker
        print OUT ($rest, "\n");
      }
    }
    elsif ($line =~ m|collectLookupResults|) {
      # comment-out this line in the error cases because if I do not
      # then it will often lead to its own error, which would mask the
      # one I am trying to verify
      print OUT ("${comment} $line");
    }
    else {
      print OUT ($line);         # emit as-is
    }
  }
  close(OUT) or die;

  # run the command on the new input file
  @args = @ARGV;
  $args[@ARGV - 1] = $tempfname;

  #print("command: ", join(' ', @args), "\n");
  $code = mysystem(@args);
  if ($code == 0) {
    print("ERROR($selcode): expected this to fail:\n",
          "  ", join(' ', @args), "\n");
    failed($selcode, 4);
  }
  else {
    print("$selcode: failed as expected\n");
    if (!$keepTemps) {
      unlink($tempfname);
    }
  }
}

print("\n$me: ");

if ($contin && @failures) {
  print("failures: @failures\n");
  exit(4);
}
elsif (!$selectedError) {
  print("success: all $testedVariations variations failed as expected\n");
}
elsif ($testedVariations) {
  print("success: error $selectedError failed as expected\n");
}
else {
  print("nop: there is no error $selectedError in $fname\n");
}

exit(0);


# like 'system', except return a proper exit code, and
# propagate fatal signals (esp. ctrl-C)
sub mysystem {
  my @args = @_;

  my $code = system(@args);
  if ($code == 0) { return $code; }

  my $sig = $code & 127;
  if ($sig != 0) {
    if ($sig == $sigquit || $sig == $sigint) {
      # subprocess died to user-originated signal; kill myself
      # the same way
      #print("killing myself with $sig\n");
      kill $sig, $$;
    }

    # some other signal
    die("child died with signal $signame[$sig]\n");
  }

  return $code >> 8;
}


# EOF
