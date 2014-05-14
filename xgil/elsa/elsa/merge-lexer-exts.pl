#!/usr/bin/perl -w
# merge a base flexer lexer description with zero or more extensions

# TODO: I would like a feature where an extension can identify a
# rule from the base that it would like to delete.  For example,
# an extension might contain something like:
#
#   delete_rule "L"?{QUOTE}({STRCHAR}|{ESCAPE})*{QUOTE}
#
# and the effect would be to remove the entire rule+action:
#
#   "L"?{QUOTE}({STRCHAR}|{ESCAPE})*{QUOTE} {
#     return svalTok(TOK_STRING_LITERAL);
#   }
#
# by finding the pattern, then matching braces to find the action.
#
# It should be an error if the rule cannot be found, because in that
# case it means the base specification has changed in a significant
# way since the extension was written.


use strict 'subs';

if (@ARGV == 0) {
  print(<<"EOF");
usage: $0 base.lex [extension.lex [...]] >merged.lex
EOF
  exit(0);
}

$base = $ARGV[0];
shift @ARGV;
                     
open(IN, "<$base") or die("cannot open $base: $!\n");
while (defined($line = <IN>)) {
  # re-echo all, including marker line, to allow composition via
  # multiple runs
  print($line);

  if ($line =~ m/EXTENSION RULES GO HERE/) {
    # insert all extension modules; insert in reverse order to
    # preserve the idea that later files are extending earlier
    # files, and the last-added extension should come first so
    # it has total control
    for ($i = @ARGV-1; $i >= 0; $i--) {
      my $ext = $ARGV[$i];
      open(EXT, "<$ext") or die("cannot open $ext: $!\n");
      while (defined($extline = <EXT>)) {
        print($extline);
      }
      close(EXT) or die;
    }
  }
}

close(IN) or die;
exit(0);
