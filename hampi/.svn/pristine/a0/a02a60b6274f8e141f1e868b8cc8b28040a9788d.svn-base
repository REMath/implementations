package YAPE::Regex::Element;

$VERSION = '3.00';


sub text { exists $_[0]{TEXT} ? $_[0]{TEXT} : "" }
sub string { $_[0]->text . "$_[0]{QUANT}$_[0]{NGREED}" }
sub fullstring { $_[0]->string }
sub quant { "$_[0]{QUANT}$_[0]{NGREED}" }
sub ngreed { $_[0]{NGREED} }


package YAPE::Regex::anchor;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub type { 'anchor' }



package YAPE::Regex::macro;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\$_[0]{TEXT}" }
sub type { 'macro' }



package YAPE::Regex::oct;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\$_[0]{TEXT}" }
sub type { 'oct' }



package YAPE::Regex::hex;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\x$_[0]{TEXT}" }
sub type { 'hex' }



package YAPE::Regex::backref;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\$_[0]{TEXT}" }
sub type { 'backref' }



package YAPE::Regex::ctrl;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\c$_[0]{TEXT}" }
sub type { 'ctrl' }



package YAPE::Regex::named;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\N{$_[0]{TEXT}}" }
sub type { 'named' }



package YAPE::Regex::Cchar;

sub new {
  my ($class,$q,$ng) = @_;
  bless { QUANT => $q, NGREED => $ng }, $class;
}

sub text { '\C' }
sub type { 'Cchar' }



package YAPE::Regex::slash;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub text { "\\$_[0]{TEXT}" }
sub type { 'slash' }



package YAPE::Regex::any;

sub new {
  my ($class,$q,$ng) = @_;
  bless { TEXT => '.', QUANT => $q, NGREED => $ng }, $class;
}

sub type { 'any' }



package YAPE::Regex::class;

sub new {
  my ($class,$match,$neg,$q,$ng) = @_;
  bless { TEXT => $match, NEG => $neg, QUANT => $q, NGREED => $ng }, $class;
}

sub text {
    $_[0]{NEG} =~ /[pP]/ ?
      "\\$_[0]{NEG}\{$_[0]{TEXT}\}" :
      "[$_[0]{NEG}$_[0]{TEXT}]"
}
sub type { 'class' }



package YAPE::Regex::text;

sub new {
  my ($class,$match,$q,$ng) = @_;
  bless { TEXT => $match, QUANT => $q, NGREED => $ng }, $class;
}

sub type { 'text' }



package YAPE::Regex::alt;

sub new { bless { NGREED => "", QUANT => "" }, $_[0] }
sub text { '' }
sub string { '|' }
sub type { 'alt' }



package YAPE::Regex::comment;

sub new {
  my ($class,$text,$X) = @_;
  bless { TEXT => $text, XCOMM => $X }, $class;
}

sub string { $_[0]{XCOMM} ? " # $_[0]{TEXT}" : "(?#$_[0]{TEXT})" }
sub xcomm { $_[0]{XCOMM} }
sub type { 'comment' }



package YAPE::Regex::whitespace;

sub new {
  my ($class,$text) = @_;
  bless { TEXT => $text }, $class;
}

sub type { 'whitespace' }
sub string { $_[0]{TEXT} }



package YAPE::Regex::flags;

sub new {
  my ($class,$add,$sub) = @_;
  my %mode = map { $_ => 1 } split //, $add ||= "";
  delete @mode{split //, $sub ||= ""};
  $add = join "", sort split //, $add;
  $sub = join "", sort split //, $sub;
  bless { MODE => \%mode, ON => $add, OFF => $sub }, $class;
}

sub string { "(?$_[0]{ON}" . ($_[0]{OFF} && "-$_[0]{OFF}") . ')' }
sub type { 'flags' }



package YAPE::Regex::cut;

sub new {
  bless {
    CONTENT => $_[1] || [],
    QUANT => $_[2] || "",
    NGREED => $_[3] || "",
  }, $_[0]
}

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{CONTENT} }),
    ")$_[0]{QUANT}$_[0]{NGREED}"
}

sub string { '(?>' }
sub type { 'cut' }



package YAPE::Regex::lookahead;

sub new { bless { POS => $_[1], CONTENT => $_[2] || [] }, $_[0] }

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{CONTENT} }),
    ')'
}

sub string { '(?' . ('!','=')[$_[0]{POS}] }
sub type { 'lookahead' }
sub pos { $_[0]{POS} }



package YAPE::Regex::lookbehind;

sub new { bless { POS => $_[1], CONTENT => $_[2] || [] }, $_[0] }

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{CONTENT} }),
    ')'
}

sub string { '(?<' . ('!','=')[$_[0]{POS}] }
sub type { 'lookbehind' }
sub pos { $_[0]{POS} }



package YAPE::Regex::conditional;

sub new {
  bless {
    OPTS => 1,
    CONTENT => $_[1] || [],
    TRUE => $_[2] || [],
    FALSE => $_[3] || [],
    QUANT => $_[4] || "",
    NGREED => $_[5] || "",
  }, $_[0];
}

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{TRUE} }),
    $_[0]{OPTS} == 2 ? (
      '|', map($_->fullstring, @{ $_[0]{FALSE} }),
    ) : (),
    ")$_[0]{QUANT}$_[0]{NGREED}";
}

sub string {
  '(?' . (ref $_[0]{CONTENT} ?
    $_[0]{CONTENT}[0]->fullstring :
    "($_[0]{CONTENT})"
  )
}
sub backref { $_[0]{CONTENT} }
sub type { 'cond' }



package YAPE::Regex::group;

sub new {
  my $on = join "", sort split //, $_[1] || "";
  my $off = join "", sort split //, $_[2] || "";
  bless {
    ON => $on,
    OFF => $off,
    CONTENT => $_[3] || [],
    QUANT => $_[4] || "",
    NGREED => $_[5] || "",
  }, $_[0]
}

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{CONTENT} }),
    ")$_[0]{QUANT}$_[0]{NGREED}"
}
sub string { $_[0]{OFF} ? "(?$_[0]{ON}-$_[0]{OFF}:" : "(?$_[0]{ON}:" }
sub type { 'group' }



package YAPE::Regex::capture;

sub new {
  bless {
    CONTENT => $_[1] || [],
    QUANT => $_[2] || "",
    NGREED => $_[3] || "",
  }, $_[0]
}

sub fullstring {
  join "",
    $_[0]->string,
    map($_->fullstring, @{ $_[0]{CONTENT} }),
    ")$_[0]{QUANT}$_[0]{NGREED}"
}

sub string { '(' }
sub type { 'capture' }



package YAPE::Regex::code;

sub new { bless { CONTENT => $_[1], QUANT => "", NGREED => "", }, $_[0] }
sub text { "(?$_[0]{CONTENT})" }
sub type { 'code' }



package YAPE::Regex::later;

sub new { bless { CONTENT => $_[1], QUANT => "", NGREED => "", }, $_[0] }
sub text { "(??$_[0]{CONTENT})" }
sub type { 'later' }



package YAPE::Regex::close;

sub new { bless { QUANT => $_[1] || "", NGREED => $_[2] || "" }, $_[0] }
sub string { ")$_[0]{QUANT}$_[0]{NGREED}" }
sub type { 'close' }


1;

__END__

=head1 NAME

YAPE::Regex::Element - sub-classes for YAPE::Regex elements

=head1 SYNOPSIS

  use YAPE::Regex 'MyExt::Mod';
  # this sets up inheritence in MyExt::Mod
  # see YAPE::Regex documentation

=head1 C<YAPE> MODULES

The C<YAPE> hierarchy of modules is an attempt at a unified means of parsing
and extracting content.  It attempts to maintain a generic interface, to
promote simplicity and reusability.  The API is powerful, yet simple.  The
modules do tokenization (which can be intercepted) and build trees, so that
extraction of specific nodes is doable.

=head1 DESCRIPTION

This module provides the classes for the C<YAPE::Regex> objects.  The base
class for these objects is C<YAPE::Regex::Element>.  The objects classes are
numerous.

=head2 Methods for C<YAPE::Regex::Element>

This class contains fallback methods for the other classes.

=over 4

=item * C<my $str = $obj-E<gt>text;>

Returns a string representation of the content of the regex node I<itself>, not
any nodes contained in it.  This is C<undef> for non-text nodes.

=item * C<my $str = $obj-E<gt>string;>

Returns a string representation of the regex node I<itself>, not any nodes
contained in it.

=item * C<my $str = $obj-E<gt>fullstring;>

Returns a string representation of the regex node, including any nodes contained
in it.

=item * C<my $quant = $obj-E<gt>quant;>

Returns a string with the quantity, and a C<?> if the node is non-greedy.  The
quantity is one of C<*>, C<+>, C<?>, C<{I<M>,I<N>}>, or an empty string.

=item * C<my $ng = $obj-E<gt>ngreed;>

Returns a C<?> if the node is non-greedy, and an empty string otherwise.

=back

=head2 Methods for C<YAPE::Regex::anchor>

This class represents anchors.  Objects have the following methods:

=over 4

=item * C<my $anchor = YAPE::Regex::anchor-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::anchor> object.  Takes three arguments:  the anchor
(C<^>, C<\A>, C<$>, C<\Z>, C<\z>, C<\B>, C<\b>, or C<\G>), the quantity, and
the non-greedy flag.  The quantity I<should> be an empty string.

  my $anc = YAPE::Regex::anchor->new('\A', '', '?');
  # /\A?/

=item * C<my $type = $anchor-E<gt>type;>

Returns the string C<anchor>.

=back

=head2 Methods for C<YAPE::Regex::macro>

This class represents character-class macros.  Objects have the following
methods:

=over 4

=item * C<my $macro = YAPE::Regex::macro-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::macro> object.  Takes three arguments:  the macro
(C<w>, C<W>, C<d>, C<D>, C<s>, or C<S>), the quantity, and the non-greedy
flag.

  my $macro = YAPE::Regex::macro->new('s', '{3,5}');
  # /\s{3,5}/

=item * C<my $text = $macro-E<gt>text;>

Returns the macro.

  print $macro->text;  # '\s'

=item * C<my $type = $macro-E<gt>type;>

Returns the string C<macro>.

=back

=head2 Methods for C<YAPE::Regex::oct>

This class represents octal escapes.  Objects have the following methods:

=over 4

=item * C<my $oct = YAPE::Regex::oct-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::oct> object.  Takes three arguments:  the octal number
(as a string), the quantity, and the non-greedy flag.

  my $oct = YAPE::Regex::oct->new('040');
  # /\040/

=item * C<my $text = $oct-E<gt>text;>

Returns the octal escape.

  print $oct->text;  # '\040'

=item * C<my $type = $oct-E<gt>type;>

Returns the string C<oct>.

=back

=head2 Methods for C<YAPE::Regex::hex>

This class represents hexadecimal escapes.  Objects have the following methods:

=over 4

=item * C<my $hex = YAPE::Regex::hex-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::hex> object.  Takes three arguments:  the hexadecimal
number (as a string), the quantity, and the non-greedy flag.

  my $hex = YAPE::Regex::hex->new('20','{2,}');
  # /\x20{2,}/

=item * C<my $text = $hex-E<gt>text;>

Returns the hexadecimal escape.

  print $hex->text;  # '\x20'

=item * C<my $type = $hex-E<gt>type;>

Returns the string C<hex>.

=back

=head2 Methods for C<YAPE::Regex::utf8hex>

This class represents UTF hexadecimal escapes.  Objects have the following
methods:

=over 4

=item * C<my $hex = YAPE::Regex::utf8hex-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::utf8hex> object.  Takes three arguments:  the
hexadecimal number (as a string), the quantity, and the non-greedy flag.

  my $utf8hex = YAPE::Regex::utf8hex->new('beef','{0,4}');
  # /\x{beef}{2,}/

=item * C<my $text = $utf8hex-E<gt>text;>

Returns the hexadecimal escape.

  print $utf8hex->text;  # '\x{beef}'

=item * C<my $type = $utf8hex-E<gt>type;>

Returns the string C<utf8hex>.

=back

=head2 Methods for C<YAPE::Regex::backref>

This class represents back-references.  Objects have the following methods:

=over 4

=item * C<my $bref = YAPE::Regex::bref-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::bref> object.  Takes three arguments:  the number of
the back-reference, the quantity, and the non-greedy flag.

  my $bref = YAPE::Regex::bref->new(2,'','?');
  # /\2?/

=item * C<my $text = $bref-E<gt>text;>

Returns the backescape.

  print $bref->text;  # '\2'

=item * C<my $type = $bref-E<gt>type;>

Returns the string C<backref>.

=back

=head2 Methods for C<YAPE::Regex::ctrl>

This class represents control character escapes.  Objects have the following
methods:

=over 4

=item * C<my $ctrl = YAPE::Regex::ctrl-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::ctrl> object.  Takes three arguments:  the control
character, the quantity, and the non-greedy flag.

  my $ctrl = YAPE::Regex::ctrl->new('M');
  # /\cM/

=item * C<my $text = $ctrl-E<gt>text;>

Returns the control character escape.

  print $ctrl->text;  # '\cM'

=item * C<my $type = $ctrl-E<gt>type;>

Returns the string C<ctrl>.

=back

=head2 Methods for C<YAPE::Regex::named>

This class represents named characters.  Objects have the following methods:

=over 4

=item * C<my $ctrl = YAPE::Regex::named-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::named> object.  Takes three arguments:  the name of the
character, the quantity, and the non-greedy flag.

  my $named = YAPE::Regex::named->new('GREEK SMALL LETTER BETA');
  # /\N{GREEK SMALL LETTER BETA}/

=item * C<my $text = $named-E<gt>text;>

Returns the character escape text.

  print $named->text;  # '\N{GREEK SMALL LETTER BETA}'

=item * C<my $type = $named-E<gt>type;>

Returns the string C<named>.

=back

=head2 Methods for C<YAPE::Regex::Cchar>

This class represents C characters.  Objects have the following methods:

=over 4

=item * C<my $ctrl = YAPE::Regex::Cchar-E<gt>new($q,$ng);>

Creates a C<YAPE::Regex::Cchar> object.  Takes two arguments:  the quantity and
the non-greedy flag.

  my $named = YAPE::Regex::Char->new(2);
  # /\C{2}/

=item * C<my $text = $Cchar-E<gt>text;>

Returns the escape sequence.

  print $Cchar->text;  # '\C'

=item * C<my $type = $Cchar-E<gt>type;>

Returns the string C<Cchar>.

=back

=head2 Methods for C<YAPE::Regex::slash>

This class represents any other escaped characters.  Objects have the following
methods:

=over 4

=item * C<my $slash = YAPE::Regex::slash-E<gt>new($type,$q,$ng);>

Creates a C<YAPE::Regex::slash> object.  Takes three arguments:  the backslashed
character, the quantity, and the non-greedy flag.

  my $slash = YAPE::Regex::slash->new('t','','?');
  # /\t?/

=item * C<my $text = $slash-E<gt>text;>

Returns the escaped character.

  print $slash->text;  # '\t'

=item * C<my $type = $slash-E<gt>type;>

Returns the string C<slash>.

=back

=head2 Methods for C<YAPE::Regex::any>

This class represents the dot metacharacter.  Objects have the following methods:

=over 4

=item * C<my $any = YAPE::Regex::any-E<gt>new($q,$ng);>

Creates a C<YAPE::Regex::any> object.  Takes two arguments:  the quantity, and
the non-greedy flag.

  my $any = YAPE::Regex::any->new('{1,3}');
  # /.{1,3}/

=item * C<my $type = $any-E<gt>type;>

Returns the string C<any>.

=back

=head2 Methods for C<YAPE::Regex::class>

This class represents character classes.  Objects have the following methods:

=over 4

=item * C<my $class = YAPE::Regex::class-E<gt>new($chars,$neg,$q,$ng);>

Creates a C<YAPE::Regex::class> object.  Takes four arguments:  the characters
in the class, a C<^> if the class is negated (an empty string otherwise), the
quantity, and the non-greedy flag.

  my $class = YAPE::Regex::class->new('aeiouy','^');
  # /[^aeiouy]/

=item * C<my $text = $class-E<gt>text;>

Returns the character class.

  print $class->text;  # [^aeiouy]

=item * C<my $type = $class-E<gt>type;>

Returns the string C<class>.

=back

=head2 Methods for C<YAPE::Regex::hex>

This class represents hexadecimal escapes.  Objects have the following methods:

=over 4

=item * C<my $text = YAPE::Regex::text-E<gt>new($text,$q,$ng);>

Creates a C<YAPE::Regex::text> object.  Takes three arguments:  the text, the
quantity, and the non-greedy flag.  The quantity and non-greedy modifier should
only be present for I<single-character> text, because of the way the parser
renders the quantity and non-greedy modifier.

  my $text = YAPE::Regex::text->new('alphabet','');
  # /alphabet/
  
  my $text = YAPE::Regex::text->new('x','?','?');
  # /x??/

=item * C<my $type = $text-E<gt>type;>

Returns the string C<text>.

=back

=head2 Methods for C<YAPE::Regex::alt>

This class represents alternation.  Objects have the following methods:

=over 4

=item * C<my $alt = YAPE::Regex::alt-E<gt>new;>

Creates a C<YAPE::Regex::alt> object.

  my $alt = YAPE::Regex::alt->new;
  # /|/

=item * C<my $type = $oct-E<gt>type;>

Returns the string C<alt>.

=back

=head2 Methods for C<YAPE::Regex::comment>

This class represents in-line comments.  Objects have the following methods:

=over 4

=item * C<my $comment = YAPE::Regex::comment-E<gt>new($comment,$x);>

Creates a C<YAPE::Regex::comment> object.  Takes two arguments:  the text of the
comment, and whether or not the C</x> regex modifier is in effect for this
comment.  Note that Perl's regex engine will stop a C<(?#...)> comment at the
first C<)>, regardless of what you do.

  my $comment = YAPE::Regex::comment->new(
    "match an optional string of digits"
  );
  # /(?#match an optional string of digits)/

  my $comment = YAPE::Regex::comment->new(
    "match an optional string of digits",
    1
  );
  # /# match an optional string of digits/

=item * C<my $type = $comment-E<gt>type;>

Returns the string C<comment>.

=item * C<my $x_on = $comment-E<gt>xcomm;>

Returns true or false, depending on whether the comment is under the C</x> regex
modifier.

=back

=head2 Methods for C<YAPE::Regex::whitespace>

This class represents whitespace under the C</x> regex modifier.  Objects have
the following methods:

=over 4

=item * C<my $ws = YAPE::Regex::whitespace-E<gt>new($text);>

Creates a C<YAPE::Regex::whitespace> object.  Takes one argument:  the text of
the whitespace.

  my $ws = YAPE::Regex::whitespace->new('  ');
  # /  /x

=item * C<my $text = $ws-E<gt>text;>

Returns the whitespace.

  print $ws->text;  # '  '

=item * C<my $type = $ws-E<gt>type;>

Returns the string C<whitespace>.

=back

=head2 Methods for C<YAPE::Regex::flags>

This class represents C<(?ismx)> flags.  Objects have the following methods:

=over 4

=item * C<my $flags = YAPE::Regex::flags-E<gt>new($add,$sub);>

Creates a C<YAPE::Regex::flags> object.  Takes two arguments:  a string of the
modes to have on, and a string of the modes to explicitly turn off.  The flags
are displayed in alphabetical order.

  my $flags = YAPE::Regex::flags->new('is','m');
  # /(?is-m)/

=item * C<my $type = $flags-E<gt>type;>

Returns the string C<flags>.

=back

=head2 Methods for C<YAPE::Regex::cut>

This class represents the cut assertion.  Objects have the following methods:

=over 4

=item * C<my $look = YAPE::Regex::cut-E<gt>new(\@nodes);>

Creates a C<YAPE::Regex::cut> object.  Takes one arguments:  a reference to an
array of objects to be contained in the cut.

  my $REx = YAPE::Regex::class->new('aeiouy','','+');
  my $look = YAPE::Regex::cut->new(0,[$REx]);
  # /(?>[aeiouy]+)/

=item * C<my $type = $cut-E<gt>type;>

Returns the string C<cut>.

=back

=head2 Methods for C<YAPE::Regex::lookahead>

This class represents lookaheads.  Objects have the following methods:

=over 4

=item * C<my $look = YAPE::Regex::lookahead-E<gt>new($pos,\@nodes);>

Creates a C<YAPE::Regex::lookahead> object.  Takes two arguments:  a boolean
value indicating whether or not the lookahead is positive, and a reference to an
array of objects to be contained in the lookahead.

  my $REx = YAPE::Regex::class->new('aeiouy');
  my $look = YAPE::Regex::lookahead->new(0,[$REx]);
  # /(?![aeiouy])/

=item * C<my $pos = $look-E<gt>pos;>

Returns true if the lookahead is positive.

  print $look->pos ? 'pos' : 'neg';  # 'neg'

=item * C<my $type = $look-E<gt>type;>

Returns the string C<lookahead(pos)> or C<lookahead(neg)>.

=back

=head2 Methods for C<YAPE::Regex::lookbehind>

This class represents lookbehinds.  Objects have the following methods:

=over 4

=item * C<my $look = YAPE::Regex::lookbehind-E<gt>new($pos,\@nodes);>

Creates a C<YAPE::Regex::lookbehind> object.  Takes two arguments:  a boolean
value indicating whether or not the lookbehind is positive, and a reference to
an array of objects to be contained in the lookbehind.

  my $REx = YAPE::Regex::class->new('aeiouy','^');
  my $look = YAPE::Regex::lookbehind->new(1,[$REx]);
  # /(?<=[^aeiouy])/

=item * C<my $pos = $look-E<gt>pos;>

Returns true if the lookbehind is positive.

  print $look->pos ? 'pos' : 'neg';  # 'pos'

=item * C<my $type = $look-E<gt>type;>

Returns the string C<lookbehind(pos)> or C<lookbehind(neg)>.

=back

=head2 Methods for C<YAPE::Regex::conditional>

This class represents conditionals.  Objects have the following methods:

=over 4

=item * C<my $cond = YAPE::Regex::conditional-E<gt>new($br,$t,$f,$q,$ng);>

Creates a C<YAPE::Regex::hex> object.  Takes five arguments:  the number of the
back-reference (that's all that's supported in the current version), an array
reference to the "true" pattern, an array reference to the "false" pattern, and
the quantity and non-greedy flag.

  my $cond = YAPE::Regex::conditional->new(
    2,
    [],
    [ YAPE::Regex::text->new('foo') ],
    '?',
  );
  # /(?(2)|foo)?/

=item * C<my $br = $cond-E<gt>backref;>

Returns the number of the back-reference the conditional depends on.

  print $br->backref;  # 2

=item * C<my $type = $cond-E<gt>type;>

Returns the string C<conditional(I<N>)>, where I<N> is the number of the
back-reference.

=back

=head2 Methods for C<YAPE::Regex::group>

This class represents non-capturing groups.  Objects have the following methods:

=over 4

=item * C<my $group = YAPE::Regex::group-E<gt>new($on,$off,\@nodes,$q,$ng);>

Creates a C<YAPE::Regex::group> object.  Takes five arguments:  the modes turned
on, the modes explicitly turned off, a reference to an array of objects in the
group, the quantity, and the non-greedy flag.  The modes are displayed in
alphabetical order.

  my $group = YAPE::Regex::group->new(
    'i',
    's',
    [
      YAPE::Regex::macro->new('d', '{2}'),
      YAPE::Regex::macro->new('s'),
      YAPE::Regex::macro->new('d', '{2}'),
    ],
    '?',
  );
  # /(?i-s:\d{2}\s\d{2})?/

=item * C<my $type = $group-E<gt>type;>

Returns the string C<group>.

=back

=head2 Methods for C<YAPE::Regex::capture>

This class represents capturing groups.  Objects have the following methods:

=over 4

=item * C<my $capture = YAPE::Regex::capture-E<gt>new(\@nodes,$q,$ng);>

Creates a C<YAPE::Regex::capture> object.  Takes three arguments:  a reference
to an array of objects in the group, the quantity, and the non-greedy flag.

  my $capture = YAPE::Regex::capture->new(
    [
      YAPE::Regex::macro->new('d', '{2}'),
      YAPE::Regex::macro->new('s'),
      YAPE::Regex::macro->new('d', '{2}'),
    ],
  );
  # /(\d{2}\s\d{2})/

=item * C<my $type = $capture-E<gt>type;>

Returns the string C<capture>.

=back

=head2 Methods for C<YAPE::Regex::code>

This class represents code blocks.  Objects have the following methods:

=over 4

=item * C<my $code = YAPE::Regex::code-E<gt>new($block);>

Creates a C<YAPE::Regex::code> object.  Takes one arguments:  a string holding
a block of code.

  my $code = YAPE::Regex::code->new(q({ push @poss, $1 }));
  # /(?{ push @poss, $1 })/

=item * C<my $type = $code-E<gt>type;>

Returns the string C<code>.

=back

=head2 Methods for C<YAPE::Regex::later>

This class represents closed parentheses.  Objects have the following methods:

=over 4

=item * C<my $later = YAPE::Regex::later-E<gt>new($block);>

Creates a C<YAPE::Regex::later> object.  Takes one arguments:  a string holding
a block of code.

  my $later = YAPE::Regex::later->new(q({ push @poss, $1 }));
  # /(?{{ push @poss, $1 }})/

=item * C<my $type = $later-E<gt>type;>

Returns the string C<later>.

=back

=head2 Methods for C<YAPE::Regex::close>

This class represents closed parentheses.  Objects have the following methods:

=over 4

=item * C<my $close = YAPE::Regex::close-E<gt>new($q,$ng);>

Creates a C<YAPE::Regex::close> object.  Takes two arguments:  the quantity, and
the non-greedy flag.  This object is never needed in the tree; however, they are
returned in the parsing stage, so that you know when they've been reached.

  my $close = YAPE::Regex::close->new('?','?');
  # /)??/

=item * C<my $type = $close-E<gt>type;>

Returns the string C<close>.

=back

=head1 TO DO

This is a listing of things to add to future versions of this module.

=over 4

=item * None!

=back

=head1 BUGS

Following is a list of known or reported bugs.

=over 4

=item * This documentation might be incomplete.

=back

=head1 SUPPORT

Visit C<YAPE>'s web site at F<http://www.pobox.com/~japhy/YAPE/>.

=head1 SEE ALSO

The C<YAPE::Regex> documentation, for information on the main class.

=head1 AUTHOR

  Jeff "japhy" Pinyan
  CPAN ID: PINYAN
  japhy@pobox.com
  http://www.pobox.com/~japhy/

=cut
