package YAPE::Regex::Explain;

use YAPE::Regex 'YAPE::Regex::Explain';
use strict;
use vars '$VERSION';


$VERSION = '3.011';


my $exp_format = << 'END';
^<<<<<<<<<<<<<<<<<<<<<   ^<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
END

my $REx_format = << 'END';
^<<<<<<<<<<<<<<<<<<<<< # ^<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
END

my $noc_format = << 'END';
^<<<<<<<<<<<<<<<<<<<<<
END

my ($using_rex,$format,$br);


my $valid_POSIX = qr{
  alpha | alnum | ascii | cntrl | digit | graph |
  lower | print | punct | space | upper | word | xdigit
}x;


my $cc_REx = qr{(
  \\[0-3][0-7]{2} |
  \\x[a-fA-F0-9]{2} |
  \\x\{[a-fA-F0-9]+\} |
  \\c. |
  \\[nrftbae] |
  \\N\{([^\}]+)\} |
  \\[wWdDsS] |
  \\([Pp])([A-Za-z]|\{[^\}]+\}) |
  \[:(\^?)($valid_POSIX):\] |
  \\?.
)}xs;


my %modes = ( on => '', off => '' );

my %exp = (

  # anchors
  '\A' => 'the beginning of the string',
  '^' => 'the beginning of the string',
  '^m' => 'the beginning of a "line"',
  '\z' => 'the end of the string',
  '\Z' => 'before an optional \n, and the end of the string',
  '$' => 'before an optional \n, and the end of the string',
  '$m' => 'before an optional \n, and the end of a "line"',
  '\G' => 'where the last m//g left off',
  '\b' => 'the boundary between a word char (\w) and something ' .
          'that is not a word char',
  '\B' => 'the boundary between two word chars (\w) or two ' .
          'non-word chars (\W)',
  
  # quantifiers
  '*' => '0 or more times',
  '+' => '1 or more times',
  '?' => 'optional',
  
  # macros
  '\w' => 'word characters (a-z, A-Z, 0-9, _)',
  '\W' => 'non-word characters (all but a-z, A-Z, 0-9, _)',
  '\d' => 'digits (0-9)',
  '\D' => 'non-digits (all but 0-9)',
  '\s' => 'whitespace (\n, \r, \t, \f, and " ")',
  '\S' => 'non-whitespace (all but \n, \r, \t, \f, and " ")',

  # dot
  '.' => 'any character except \n',
  '.s' => 'any character',

  # alt
  '|' => "OR",

  # flags
  'i' => 'case-insensitive',
  '-i' => 'case-sensitive',
  'm' => 'with ^ and $ matching start and end of line',
  '-m' => 'with ^ and $ matching normally',
  's' => 'with . matching \n',
  '-s' => 'with . not matching \n',
  'x' => 'disregarding whitespace and comments',
  '-x' => 'matching whitespace and # normally',

);


my %macros = (
  # utf8/POSIX macros
  alpha => 'letters',
  alnum => 'letters and digits',
  ascii => 'all ASCII characters (\000 - \177)',
  cntrl => 'control characters (those with ASCII values less than 32)',
  digit => 'digits (like \d)',
  graph => 'alphanumeric and punctuation characters',
  lower => 'lowercase letters',
  print => 'alphanumeric, punctuation, and whitespace characters',
  punct => 'punctuation characters',
  space => 'whitespace characters (like \s)',
  upper => 'uppercase letters',
  word => 'alphanumeric and underscore characters (like \w)',
  xdigit => 'hexadecimal digits (a-f, A-F, 0-9)',
);


my %trans = (
  '\a' => q('\a' (alarm)),
  '\b' => q('\b' (backspace)),
  '\e' => q('\e' (escape)),
  '\f' => q('\f' (form feed)),
  '\n' => q('\n' (newline)),
  '\r' => q('\r' (carriage return)),
  '\t' => q('\t' (tab)),
);


sub explain {
  my $self = shift;
  $using_rex = shift || '';
  local $^A = "";
  $^A = << "END" if not $using_rex;
The regular expression:

@{[ $self->display ]}

matches as follows:
  
NODE                     EXPLANATION
----------------------------------------------------------------------
END
  
  my @nodes = @{ $self->{TREE} };
  $format =
    $using_rex eq 'silent' ? $noc_format :
    $using_rex eq 'regex'  ? $REx_format :
                             $exp_format;

  while (my $node = shift @nodes) {
    $node->explanation;
  }
  
  ($using_rex,$br) = (0,0);
  %modes = ( on => '', off => '' );

  return $^A;
}


sub YAPE::Regex::Explain::Element::extra_info {
  my $self = shift;    
  my ($q,$ng) = ($self->quant, $self->ngreed);
  my $ex = '';

  chop $q if $ng;
  if ($q =~ /\{(\d*)(,?(\d*))\}/) {
    if ($2 and length $3) { $q = "between $1 and $3 times" }
    elsif ($2) { $q = "at least $1 times" }
    elsif (length $1) { $q = "$1 times" }
  }

  if ($q) {
    $ex .= ' (' . ($exp{$q} || $q);
    $ex .= ' (matching the ' . ($ng ? 'lea' : 'mo') . 'st amount possible)'
      if $q !~ /^\d+ times$/;
    $ex .= ')' if $q;
  }

  return $ex;
}


# yes, I'm sure this could be made a bit more efficient...
# but I'll deal with the small fish when the big fish are fried

sub YAPE::Regex::Explain::Element::handle_flags {
  my $self = shift;
  my ($prev_on, $prev_off) = @modes{qw( on off )};
  
  for (split //, $self->{ON}) {
    $modes{on} .= $_ if index($modes{on},$_) == -1;
  }
  my $on = $modes{on} = join "", sort split //, $modes{on};

  $modes{off} =~ s/[$on]+//g if length $on;

  for (split //, $self->{OFF}) {
    $modes{off} .= $_ if index($modes{off},$_) == -1;
  }
  my $off = $modes{off} = join "", sort split //, $modes{off};

  $modes{on} =~ s/[$off]+//g if length $off;

  my $exp = '';

  if ($modes{on} ne $prev_on) {
    for (split //, $modes{on}) { $exp .= ' (' . $exp{$_} . ')' }
  }
  
  if ($modes{off} ne $prev_off) {
    for (split //, $modes{off}) { $exp .= ' (' . $exp{-$_} . ')' }
  }

  return $exp;
}


sub YAPE::Regex::Explain::anchor::explanation {
  my $self = shift;
  my $type = $self->{TEXT};
  $type .= 'm' if
    ($type eq '^' or $type eq '$') and
    $modes{on} =~ /m/;

  my $explanation = $exp{$type} . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::macro::explanation {
  my $self = shift;
  my $type = $self->text;

  my $explanation = $exp{$type} . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::oct::explanation {
  my $self = shift;
  my $n = oct($self->{TEXT});

  my $explanation = "character $n" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::hex::explanation {
  my $self = shift;
  my $n = hex($self->{TEXT});

  my $explanation = "character $n" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::utf8hex::explanation {
  my $self = shift;
  my $n = hex($self->{TEXT});

  my $explanation = "UTF character $n" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::ctrl::explanation {
  my $self = shift;
  my $c = $self->{TEXT};

  my $explanation = "^$c" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::named::explanation {
  my $self = shift;
  my $c = $self->{TEXT};

  my $explanation = "the character named '$c'" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::Cchar::explanation {
  my $self = shift;
  my $c = $self->{TEXT};

  my $explanation = "one byte (a C character)" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::slash::explanation {
  my $self = shift;

  my $explanation =
    ($trans{$self->text} || "'$self->{TEXT}'") .
    $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::any::explanation {
  my $self = shift;
  my $type = '.';
  $type .= 's' if $modes{on} =~ /s/;

  my $explanation = $exp{$type} . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::text::explanation {
  my $self = shift;
  my $text = $self->text;
  
  $text =~ s/\n/\\n/g;
  $text =~ s/\r/\\r/g;
  $text =~ s/\t/\\t/g;
  $text =~ s/\f/\\f/g;
  $text =~ s/'/\\'/g;
  
  my $explanation = "'$text'" . $self->extra_info;
  my $string = $self->string;

  if ($using_rex) {
    $string =~ s/\n/\\n/g;
    $string =~ s/\r/\\r/g;
    $string =~ s/\t/\\t/g;
    $string =~ s/\f/\\f/g;
    $string =~ s/([ #])/\\$1/g;
  }  

  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::alt::explanation {
  my $self = shift;

  my $explanation = $exp{'|'};
  my $string = $self->string;
  
  my $oldfmt = $format;
  $format =~ s/ (\^<+)/$1 /g;
  $format =~ s/ #/# / if $using_rex;
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
  $format = $oldfmt;

}


sub YAPE::Regex::Explain::backref::explanation {
  my $self = shift;

  my $explanation =
    "what was matched by capture \\$self->{TEXT}" . $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::class::explanation {
  my $self = shift;
  my $class = $self->{TEXT};
  $class = $self->text if $self->{NEG} =~ /[pP]/;

  my $explanation = "any character ";
  $explanation .= ($self->{NEG} eq '^') ? "except: " : "of: ";

  while ($class =~ s/^$cc_REx//) {
    my ($c1, $name, $pP, $utf8, $neg, $posix) = ($1,$2,$3,$4,$5,$6);
    
    if ($name) {
      $explanation .= qq{the character named "$name"};
    }
    
    elsif ($utf8) {
      $utf8 =~ tr/{}//d;
      (my $nice = $utf8) =~ s/^Is//;

      my $add =
        ($pP eq 'P' and "anything but ") .
        ($macros{lc $nice} || "UTF macro '$utf8'");
      $add =~ s/\\([wds])/\\\U$1/ if $pP eq 'P';
      $explanation .= $add;
    }
    
    elsif ($posix) {
      my $add = ($neg and "anything but ") . $macros{lc $posix};
      $add =~ s/\\([wds])/\\\U$1/ if $neg;
      $explanation .= $add;
    }
    
    else {
      $explanation .= (
        $trans{$c1} ||
        ($c1 =~ /\\[wWdDsS]/ and $exp{$c1}) ||
        "'$c1'"
      );
    }

    if (!$utf8 and !$posix and $c1 !~ /\\[wWdDsS]/ and $class =~ s/^-$cc_REx//) {
      my ($c2, $name, $pP, $utf8, $neg, $posix) = ($1,$2,$3,$4,$5,$6);

      $class = "-$c2", next if $utf8 or $posix or $c2 =~ /\\[wWdDsS]/;

      if ($name) {
        $explanation .= qq{ to the character named "$name"};
      }
      else {
        $explanation .= ' to ' . ($trans{$c2} || "'$c2'");
      }
    }
    $explanation .= ', ';

  }

  substr($explanation,-2) = $self->extra_info;
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::comment::explanation { }


sub YAPE::Regex::Explain::whitespace::explanation { }


sub YAPE::Regex::Explain::flags::explanation {
  my $self = shift;
  if ($using_rex) {
    $self->{ON} .= 'x' if $self->{ON} !~ /x/;
    $self->{OFF} =~ s/x//;
  }
  my $string = $self->string;
  my $explanation =
    'set flags for this block' .
    $self->handle_flags;

  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::code::explanation {
  my $self = shift;
  my $string = $self->string;
  my $explanation = 'run this block of Perl code';

  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::later::explanation {
  my $self = shift;
  my $string = $self->string;
  my $explanation = 'run this block of Perl code (that isn\'t interpolated until RIGHT NOW)';

  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::group::explanation {
  my $self = shift;
  if ($using_rex) {
    $self->{ON} .= 'x' if $self->{ON} !~ /x/;
    $self->{OFF} =~ s/x//;
  }
  my $explanation =
    'group, but do not capture' .
    $self->handle_flags .
    $self->extra_info .
    ":";
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";

  my %old = %modes;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;
  $_->explanation for @{ $self->{CONTENT} };
  $format = $oldfmt;
  
  $string = ')' . $self->quant;
  $explanation = 'end of grouping';

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::capture::explanation {
  my $self = shift;
  my $explanation =
    'group and capture to \\' .
    ++$br .
    $self->extra_info .
    ":";
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";

  my %old = %modes;
  my $old_br = $br;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;
  $_->explanation for @{ $self->{CONTENT} };
  $format = $oldfmt;  
  $string = ')' . $self->quant;
  $explanation = "end of \\$old_br";

  $explanation .= << "END" if $self->quant;
 (NOTE: because you're using a quantifier on this capture, only the LAST
repetition of the captured pattern will be stored in \\$old_br)
END

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::cut::explanation {
  my $self = shift;
  my $explanation =
    'match (and do not backtrack afterwards)' .
     $self->extra_info .
     ":";
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";

  my %old = %modes;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;
  $_->explanation for @{ $self->{CONTENT} };
  $format = $oldfmt;  
  $string = ')' . $self->quant;
  
  $explanation = 'end of look-ahead';

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::lookahead::explanation {
  my $self = shift;

  if (not @{ $self->{CONTENT} }) {
    my $explanation =
      ($self->{POS} ? 'succeed' : 'fail') .
      $self->extra_info;
    my $string = $self->fullstring;
    
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
    return;
  }  

  my $explanation =
    'look ahead to see if there is' .
    ($self->{POS} ? '' : ' not') .
    $self->extra_info .
    ":";
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";

  my %old = %modes;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;
  $_->explanation for @{ $self->{CONTENT} };
  $format = $oldfmt;  
  $string = ')' . $self->quant;
  $explanation = 'end of look-ahead';

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::lookbehind::explanation {
  my $self = shift;
  my $explanation =
    'look behind to see if there is' .
    ($self->{POS} ? '' : ' not') .
    $self->extra_info .
    ":";
  my $string = $self->string;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";

  my %old = %modes;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;
  $_->explanation for @{ $self->{CONTENT} };
  $format = $oldfmt;  
  $string = ')' . $self->quant;
  $explanation = 'end of look-behind';

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


sub YAPE::Regex::Explain::conditional::explanation {
  my $self = shift;
  my ($string,$explanation);
  
  if (ref $self->{CONTENT}) {
    $string = '(?';
    $explanation =
      'if the following assertion is true' .
      $self->extra_info .
      ":";
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";

    my $oldfmt = $format;
    $format =~ s/\^<<(<+)/  ^$1/g;
    $format =~ s/#  /  #/ if $using_rex;
    $self->{CONTENT}[0]->explanation;

    $format =~ s/ (\^<+)/$1 /g;
    $format =~ s/ #/# / if $using_rex;
  
    $explanation = 'then:';
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";
  
    $format = $oldfmt;
  }
  else {
    $string = $self->string;
    $explanation =
      "if back-reference \\$self->{CONTENT} matched, then" .
      $self->extra_info .
      ":";
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";
  }
  
  my %old = %modes;

  my $oldfmt = $format;
  $format =~ s/\^<<(<+)/  ^$1/g;
  $format =~ s/#  /  #/ if $using_rex;

  $_->explanation for @{ $self->{TRUE} };

  unless (@{ $self->{TRUE} }) {
    my $string = "";
    my $explanation = 'succeed';
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";
  }

  {
    my $oldfmt = $format;

    $format =~ s/ (\^<+)/$1 /g;
    $format =~ s/ #/# / if $using_rex;
  
    my $string = "|";
    my $explanation = 'else:';
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";

    $format = $oldfmt;
  }
  
  $_->explanation for @{ $self->{FALSE} };

  if (not @{ $self->{FALSE} }) {
    my $string = "";
    my $explanation = 'succeed';
    if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }
    $^A .= ($using_rex ? '' : '-' x 70) . "\n";
  }  

  $format = $oldfmt;  
  $string = ')' . $self->quant;
  $explanation =
    "end of conditional" .
    (ref $self->{CONTENT} ? '' : " on \\$self->{CONTENT}");

  %modes = %old;
  
  if ($using_rex ne 'silent') { formline($format, $string, $explanation) while length($string . $explanation) } else { formline($format, $string) while length($string) }  $^A .= ($using_rex ? '' : '-' x 70) . "\n";
}


1;

__END__

=head1 NAME

YAPE::Regex::Explain - explanation of a regular expression

=head1 SYNOPSIS

  use YAPE::Regex::Explain;
  my $exp = YAPE::Regex::Explain->new($REx)->explain;

=head1 C<YAPE> MODULES

The C<YAPE> hierarchy of modules is an attempt at a unified means of parsing
and extracting content.  It attempts to maintain a generic interface, to
promote simplicity and reusability.  The API is powerful, yet simple.  The
modules do tokenization (which can be intercepted) and build trees, so that
extraction of specific nodes is doable.

=head1 DESCRIPTION

This module merely sub-classes C<YAPE::Regex>, and produces a rather verbose
explanation of a regex, suitable for demonstration and tutorial purposes.
Perl 5.6 regex structures like C<\p{...}> and C<\P{...}> and C<[:...:]> are
now supported.

=head2 Methods for C<YAPE::Regex::Explain>

=over 4

=item * C<my $p = YAPE::Regex::Explain-E<gt>new($regex);>

Calls C<YAPE::Regex>'s C<new> method (see its docs).

=item * C<my $p = YAPE::Regex::Explain-E<gt>explain($mode);>

Returns a string explaining the regex.  If C<$mode> is C<regex>, it will output
a valid regex (instead of the normal string).  If C<$mode> is C<silent>, no
comments will be added, but the regex will be expanded into a readable format.

=back

=head1 SUPPORT

Visit C<YAPE>'s web site at F<http://www.pobox.com/~japhy/YAPE/>.

=head1 SEE ALSO

The C<YAPE::Regex> documentation.

=head1 AUTHOR

  Jeff "japhy" Pinyan
  CPAN ID: PINYAN
  japhy@pobox.com
  http://www.pobox.com/~japhy/

=cut


