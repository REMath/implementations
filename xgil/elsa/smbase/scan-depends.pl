#!/usr/bin/perl -w
# scan some C/C++ source files for their module dependencies,
# output a description in the Dot graph format
# author: smcpeak@cs.berkeley.edu

# info on Dot: http://www.research.att.com/sw/tools/graphviz/

# this scanner assumes that dependencies are expressed in one
# of three ways:
#   1. direct #inclusion, using quotes to delimit the filename
#      (assuption is that angle brackets are used to refer to
#      system headers, and we don't want to see those 
#      dependencies)
#   2. implicit link dependency of foo.h on foo.{c,cc,cpp},
#      whichever exists, if any
#   3. explicit link dependency expressed as a comment of the form
#      // linkdepend: <filename>

# Any line containing "(r)" is ignored by this script.  The intent
# is to mark #include lines with this if the file included is
# actually pulled in by another #include (so it's redundant, hence
# the "r") but I don't want to remove the #include altogether
# (because it still provides useful documentation).  By adding the
# occasional "(r)" here and there one can prune the dependency tree
# output to get a pleasing output (I wish Dot itself exposed more
# knobs to tweak...)

# The scanner does *not* run the preprocessor or otherwise use any
# smarts to decode #ifdefs, #defines, tricky #inclusion sequences,
# etc.  It also does not analyze anything produced by the compiler,
# so it can easily miss link-time dependencies if your coding
# conventions differ from mine.  Caveat emptor.

# The scanner also assumes that file names are unique across all
# directories under consideration.  My own projects conform to this
# constraint since it helps avoid confusion, and using this assumption
# means avoiding the clutter of qualifying names with directories.

# NOTE: throughout, when file names are passed or stored, they
# are stored *without* path qualification; all files are in
# either the current directory or one of the directories 
# specified with -I (and hence in @incdirs)


# -------------------- global variables ---------------------
# list of directories to search for #include files in; the user
# adds things to this list with -I
@incdirs = ();

# hashtable of files to exclude; actually, each entry is a number,
# and when that number is positive it says how many more incoming
# links we'll allow; when it is zero then no more links are allowed;
# user adds to this with -X
%excluded = ();

# table of files whose outgoing edges should not be explored;
# the data is always a 1; user adds to this with -S
%subsystem = ();

# when I print the info for a node, I put a 1 in this hashtable
%nodes = ();

# when I explore the edges from a node, I put a 1 in this table
%explored = ();
$recursive = 0;

# list of files to explore; initially it's whatever is passed on the
# command line, but as new files are discovered (when $recursive is
# true) they get added here too
@toExplore = ();

# true to print debug messages
$debug = 0;

# true to suppress warning messages
$quiet = 0;
                     
# list of extensions to try when looking for implicit link dependencies
@extensions = (".cc", ".cpp", ".c");


# ---------------------- subroutines ----------------------
sub usage {
  print(<<"EOF");
usage: $0 [options] sourcefile [sourcefile ...]

This program reads each of the source files specified on the command
line, and emits a graph of their interdependencies in the Dot graph
file format.  The source files should *not* be qualified with a path,
but instead be inside some directory specified with -I.

Options:
  -I<dir>     Add <dir> to the list of directories to search when
              looking for \#included files (files which are included
              but not found are not printed as dependencies).

  -X<name>    Exclude module <name> from the graph.  If a number is
  -X<name>=n  specified, at most that many incoming links will be shown.

  -S<name>    Do not process any outgoing edges from module <name>.  This
              is useful when <name> is the entry point to a subsystem
              whose dependencies are charted separately.

  -r          Recursively follow dependencies for files encountered.
  -q          Suppress warnings.
  -d          Enable debug messages.
  -h,-help    Print this usage string.

EOF
  exit(0);
}


# read command-line arguments, looking for options as documented above
$origArgs = join(' ', @ARGV);
sub processArguments {
  while (@ARGV >= 1 &&
         ($ARGV[0] =~ m/^-/)) {
    my $option = $ARGV[0];
    shift @ARGV;

    my ($arg) = ($option =~ m/^-I(.*)$/);
    if (defined($arg)) {
      @incdirs = (@incdirs, $arg);
      next;
    }

    my $count;
    ($arg, $count) = ($option =~ m/^-X(.*)=(\d+)$/);
    if (defined($arg)) {
      $excluded{$arg} = $count;
      next;
    }

    ($arg) = ($option =~ m/^-X(.*)$/);
    if (defined($arg)) {
      $excluded{$arg} = 0;    # no count implies 0 incoming links allowed
      next;
    }

    ($arg) = ($option =~ m/^-S(.*)$/);
    if (defined($arg)) {
      $subsystem{$arg} = 1;
      next;
    }

    if ($option eq "-r") {
      $recursive = 1;
      next;
    }

    if ($option eq "-q") {
      $quiet = 1;
      next;
    }

    if ($option eq "-d") {
      $debug = 1;
      next;
    }

    if ($option eq "-h" ||
        $option eq "-help" ||
        $option eq "--help") {
      usage();
    }

    error("unknown option: $option\n" .
          "try \"$0 -help\" for usage info");
  }

  if (@ARGV == 0) {
    usage();
  }
}


# error messages
sub error {
  print STDERR ("error: ", @_, "\n");
  exit(2);
}

# warnings the user might be interested in
sub warning {
  if (!$quiet) {
    print STDERR ("warning: ", @_, "\n");
  }
}

# debug messages
sub diagnostic {
  if ($debug) {
    print STDERR ("diagnostic: ", @_, "\n");
  }
}


# return true if the argument file exists in the current directory
# or any of the directories in @incdirs; return value is the name
# under which the file was found, if it was
sub fileExists {
  my ($fname) = @_;

  if (-e $fname) {
    return $fname;
  }

  foreach $dir (@incdirs) {
    if (-e "$dir/$fname") {
      return "$dir/$fname";
    }
  }

  diagnostic("didn't find $fname");
  return "";   # false
}


# true if the filename meets my definition of a 'header', which has
# two implications:
#   - headers are printed without a circle around their name
#   - headers have implicit link-time dependencies on their
#     correspondingly-named .cc files
sub isHeader {
  my ($filename) = @_;
  return ($filename =~ m/\.h$/);
}


# print the node info for the argument filename, if it
# hasn't already been printed
sub addNode {
  my ($filename) = @_;

  if (!defined($nodes{$filename})) {
    # print info for this node; note that the default label is the
    # same as the name of the node, so I normally don't also have
    # an explicit 'label' attribute
    $nodes{$filename} = 1;
    print("  \"$filename\" [\n");

    if (defined($subsystem{$filename})) {
      # indicate that this module's dependencies weren't explored, hence
      # the module actually stands for a subgraph of hidden dependencies
      print("    label = \"$filename\\n(subsystem)\"\n",
            "    shape = box\n",
            "    style = dashed\n");
    }

    elsif (defined($excluded{$filename})) {
      # indicate some incoming edges were not explored
      print("    label = \"$filename\\n(ubiquitous)\"\n",
            "    style = dashed\n");
    }

    elsif (isHeader($filename)) {
      # I prefer headers to not have any delimiting shape; since I
      # don't see a way to turn off the shape altogether, I make
      # it white so it's effectively invisible
      print("    color = white\n");
    }

    print("  ]\n");
  }
}


# given a file name, strip its path if there is one (this is what
# /bin/basename does, also)
sub basename {
  my ($fname) = @_;

  my ($ret) = ($fname =~ m,/([^/]*)$,);
  if (defined($ret)) {
    # there was a slash, and we stripped it and everything before it
    return $ret;
  }
  else {
    # no slash
    return $fname;
  }
}


# given a file name, possibly with path, return the string of
# characters after the last slash (if any) but before the first dot
# which follows the last slash (if any)
sub prefix {
  my ($fname) = @_;
  $fname = basename($fname);

  # no slash now; get everything up to first dot
  ($ret) = ($fname =~ m,^([^.]*),);
  #diagnostic("prefix($fname) = $ret");
  return $ret;
}


# add an edge between the two nodes; if the third argument
# is true, then this is a link-time dependency (which is
# printed with a dashed line)
sub addEdge {
  my ($src, $dest, $isLinkTime) = @_;

  # is the link excluded?
  my $allowed = $excluded{$dest};
  if (defined($allowed)) {
    die if $allowed < 0;
    if ($allowed == 0) {
      diagnostic("skipping $dest because it is excluded");
      return;
    }                      
    $allowed--;
    diagnostic("$allowed more links will be allowed for $dest");
    $excluded{$dest} = $allowed;
  }

  if ($recursive) {
    # arrange to explore this later
    @toExplore = (@toExplore, $dest);
  }

  addNode($src);
  addNode($dest);

  print("  \"$src\" -> \"$dest\" [\n");

  if ($isLinkTime) {
    print("    style = dashed\n");
  }

  # if src and dest have the same base name, use a large
  # weight so they will be close together visually
  if (prefix($src) eq prefix($dest)) {
    print("    weight = 10\n");
  }

  print("  ]\n");
}


# explore the edges emanating from this file; expect a filename
# without path
sub exploreFile {
  my ($filename) = @_;
  
  # since we expect a filename without path, qualify it now
  # so we can open the file
  my $withPath = fileExists($filename);
  if (!$withPath) {
    warning("does not exist: $filename");
    return;
  }

  if (defined($explored{$filename})) {
    return;    # already explored this node
  }
  $explored{$filename} = 1;

  # if the file has no outgoing or incoming edges (the user must have
  # explicitly specified its name on the command line), this will
  # ensure the node at least shows up (floating off disconnected, of
  # course)
  addNode($filename);

  if (defined($subsystem{$filename})) {
    return;    # don't explore outgoing edges
  }

  # if it's a header, and the corresponding .cc file exists,
  # then add a link-time dependency edge
  if (isHeader($filename)) {
    foreach my $ext (@extensions) {
      my $corresp = $filename;
      $corresp =~ s/\.h$/$ext/;
      $corresp = basename($corresp);
      if (fileExists($corresp)) {
        addEdge($filename, $corresp, 1);
        last;     # stop looking after first match
      }
    }
  }

  if (!open(IN, "<$withPath")) {
    warning("cannot read $withPath: $!");
    next;    # skip it
  }

  # scan the file for its edges
  my $line;
  while (defined($line = <IN>)) {
    # is this line marked with "(r)", meaning "redundant", and
    # should therefore be ignored by this script?
    if ($line =~ m/\(r\)/) {
      next;
    }

    # is this an #include line?
    my ($target) = ($line =~ m/^\s*\#include\s+\"([^\"]*)\"/);
    if (defined($target)) {
      $target = basename($target);
      if (fileExists($target)) {
        # add a compile-time edge
        addEdge($filename, $target, 0);
      }
    }

    # is this a comment specifying a link-time dependency?
    ($target) = ($line =~ m/linkdepend: (.*)$/);
    if (defined($target)) {
      $target = basename($target);

      # add a link-time edge; do so even if the file can't
      # be found, because it's clearly important if the
      # programmer went to the trouble of mentioning it
      addEdge($filename, $target, 1);

      if (!fileExists($target)) {
        warning("could not find linkdepend: $target\n");
      }
    }
  }

  close(IN) or die;
}


# ---------------------- main ------------------------
processArguments();

# graph preamble
print(<<"EOF");
// dependency graph automatically produced by
//   $0 $origArgs

digraph "Dependencies" {
EOF

# process all the files, in the process adding nodes and edges to the
# graph
@toExplore = @ARGV;
while (@toExplore != 0) {
  my $filename = $toExplore[0];
  shift @toExplore;

  if ($filename =~ m,/,) {
    warning("should not use paths in arguments: $filename\n");
    $filename = basename($filename);
  }

  exploreFile($filename);
}

# finish the graph
print("}\n");

exit(0);

