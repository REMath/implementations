#!/usr/bin/perl -w
# given a partial grammar spec on input, write a grammar spec
# on output which is well-formed, and whose actions just print
# the productions that drive them

use strict 'subs';

if (@ARGV < 1) {
  print("usage: $0 [-ptree] NAME < NAME.gr.in > NAME.gr\n",
        "  -ptree: emit code to build a parse tree\n");
  exit(0);
}
                          
my $ptree = 0;
if ($ARGV[0] eq "-ptree") {
  $ptree = 1;
  shift @ARGV;
}

$name = $ARGV[0];


$nodeType = "[int]";
if ($ptree) {
  $nodeType = "[PTreeNode*]";
}


print("// automatically produced by $0\n",
      "// do not edit directly\n",
      "\n");


sub preamble {
  # insert standard preamble
  my $addlIncl = "";
  my $addlExt = "";
  if ($ptree) {
    $addlIncl = "#include \"ptreenode.h\"    // PTreeNode";
    $addlExt = ".tree";
  }

  print(<<"EOF");

    verbatim [
      $addlIncl

      extern int count;
    ]

    context_class $name : public UserActions {
    };

    impl_verbatim [
      UserActions *makeUserActions()
      {
        return new $name;
      }

      int count = 0;
    ]

EOF
}


# add actions
while (defined($line = <STDIN>)) {
  # insert preamble right before terminals
  if ($line =~ /^\s*terminals/) {
    preamble();
    print($line);

    # add EOF terminal
    print("  0 : EOF ;\n");
    next;
  }

  # remember last-seen nonterm
  ($prefix, $tail, $nonterm) = ($line =~ m/^(.*)nonterm\s+((\S+)\s+.*)$/);
  if (defined($nonterm)) {
    if (!defined($curNT)) {
      # this is the first nonterminal; insert dummy start rule
      #print("// dummy first rule\n",
      #      "nonterm$nodeType DummyStart -> tree:$nonterm EOF [ return tree; ]\n",
      #      "\n");
    }

    $curNT = $nonterm;
    print("${prefix}nonterm$nodeType $tail\n");

    # add a rule for merging
    if ($ptree) {
      print(#"  fun merge(t1, t2)   [ return new PTreeNode(PTREENODE_MERGE, t1, t2); ]\n",
            "  fun merge(t1, t2)   [ t1->addAlternative(t2); return t1; ]\n",
            "  fun del(t)          []\n",
            "  fun dup(t)          [ return t; ]\n",
            "\n");
    }
    else {
      #print("  fun merge(t1, t2)          [ cout << \"merged $nonterm\\n\"; return t1; ]\n\n");
    }

    next;
  }

  # add actions to rules without them
  ($space, $rule) = ($line =~ /^(\s*)(->.*);\s*$/);
  if (defined($rule)) {
    $len = length($space) + length($rule);
    print($space, $rule, " " x (25-$len));
    
    # text of the rule with quotes escaped
    ($ruleText = $rule) =~ s/\"/\\\"/g;

    if ($ptree) {
      print("[ return new PTreeNode(\"$curNT $ruleText\"");

      # work through the rule RHS, finding subtrees to attach
      $tail = substr($rule, 2);      # remove the leading "->"
      for(;;) {
        my ($unused, $tag, $symbol, $rest) =
          ($tail =~ m/\s*(([a-z][a-zA-Z_0-9]*):)?([a-zA-Z]+)\s*(.*)/);
        if (!defined($symbol)) {
          last;
        }
        if (defined($tag)) {
          # subtree to put into the node
          print(", $tag");
        }
        $tail = $rest;

        pretendUsed($unused);
      }
      print("); ]\n");
    }
    else {
      print("[ cout << \"reduced by $curNT $ruleText\\n\"; return ++count; ]\n");
    }
    next;
  }

  # expand terminals (single letter with *no* semicolon, and possibly
  # a comment); this avoids having to remember the ascii code for some
  # letter..
  ($letter, $comment) = ($line =~ m|^\s*([a-z])\s*(//.*)?$|);
  if (defined($letter)) {
    if (!defined($comment)) {
      $comment = "";
    }
    printf("  %d : $letter ;   $comment\n", ord(uc($letter)));
    next;
  }

  print($line);
}

exit(0);


sub pretendUsed {
}
