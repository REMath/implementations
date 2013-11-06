#/usr/bin/perl -w

package pcre_tohampi::Element;
package pcre_tohampi;

# Author : Devdatta Akhawe
# Code under MIT License
use strict;
use warnings;
use YAPE::Regex 'pcre_tohampi';

my $groupcntr=0;
my %minhash=();
my %maxhash=();

sub qnormalize{
  my ($min,$max,$quant)=@_;
  return ($min,$max) if ($quant eq "");
  return (0,-1) if ($quant eq "*");
  return (0,$max) if ($quant eq "?");
  return ($min,-1) if ($quant eq "+");
  return ($min*$1,$max*$2) if ($quant =~ m/\{(\d+),(\d+)\}/);
  return ($min*$1,-1) if ($quant =~ m/\{(\d+),\}/);
}


sub pcre_tohampi::anchor::minmax { die "Can't handle anchor\n";}
sub pcre_tohampi::macro::minmax { return qnormalize(1,1,$_[0]->quant);}
sub pcre_tohampi::oct::minmax { return qnormalize(1,1,$_[0]->quant);}
sub pcre_tohampi::hex::minmax { return qnormalize(1,1,$_[0]->quant);} 
sub pcre_tohampi::utf8hex::minmax { die "utf8hex unsupported" ; }
sub pcre_tohampi::ctrl::minmax { die "ctrl characters unsupported" ; }
sub pcre_tohampi::named::minmax { die "named expressions unsupported";}
sub pcre_tohampi::Cchar::minmax { die "cchars unsupported";}
sub pcre_tohampi::slash::minmax { return qnormalize(1,1,$_[0]->quant); }	
sub pcre_tohampi::any::minmax { return qnormalize(1,1,$_[0]->quant);}
sub pcre_tohampi::text::minmax { 
  return qnormalize((length ($_[0]->text)),(length ($_[0]->text)),$_[0]->quant); }
sub pcre_tohampi::alt::minmax { die " Can't handle alt\n"; }
sub pcre_tohampi::backref::minmax { die "Can't handle backref\n";}
sub pcre_tohampi::class::minmax { return qnormalize(1,1,$_[0]->quant);}
sub pcre_tohampi::comment::minmax { die "can't handle comment\n"; }
sub pcre_tohampi::whitespace::minmax { die "can't handle whitespace in regex \n";}
sub pcre_tohampi::flags::minmax { die "can't handle flags \n";}
sub pcre_tohampi::code::minmax { die "can't handle code\n"; }
sub pcre_tohampi::later::minmax { die "can't handle later \n"; }
sub pcre_tohampi::capture::minmax { 
     my $self=shift;
	my $themin=1000;
	my $themax=0;
	my ($tmin,$tmax)=(0,0);
     my $flag="true";
	for my $child (@{$self->{CONTENT}}){
		if($child->type eq "alt"){
			die "found an alt but there was no previous choice " if $flag;
			$themin=$tmin if $tmin<$themin;
			$themax=$tmax if ($tmax==-1);
			$themax=$tmax if ($themax != -1 and $tmax > $themax);
			($tmin,$tmax)=(0,0);
			next;
		}
		
		next if($child->type eq "anchor");
		$flag="";
		
 		my ($mn,$mx)=$child->minmax;
#		print "\n child return $mn,$mx";
		$tmin+=$mn;
		next if $tmax==-1;
		$tmax=$mx if $mx==-1;
		$tmax+=$mx if $mx!=-1;
    }
    $themin=$tmin if $tmin<$themin;
    $themax=$tmax if ($tmax==-1);
    $themax=$tmax if ($themax != -1 and $tmax > $themax);
    my ($a,$b)= qnormalize($themin,$themax,$self->quant);
    $minhash{$groupcntr}=$a;
    $maxhash{$groupcntr}=$b;
    $groupcntr++;
    #print "\ncapture returns $a,$b for".$self->fullstring."\n";
    return ($a,$b);
}


  
  

sub pcre_tohampi::group::minmax { 
     my $self=shift;
	my $themin=1000;
	my $themax=0;
	my ($tmin,$tmax)=(0,0);
     my $flag="true";
	for my $child (@{$self->{CONTENT}}){
		if($child->type eq "alt"){
			die "found an alt but there was no previous choice " if $flag;
			$themin=$tmin if $tmin<$themin;
			$themax=$tmax if ($tmax==-1);
			$themax=$tmax if ($themax != -1 and $tmax > $themax);
			($tmin,$tmax)=(0,0);
			next;
		}
		
		$flag="";
		next if($child->type eq "anchor");
 		my ($mn,$mx)=$child->minmax;
		#print "\n child return $mn,$mx";
		$tmin+=$mn;
		next if $tmax==-1;
		next unless $mx;
		$tmax=$mx if $mx==-1;
		$tmax+=$mx if $mx!=-1;
    }
    $themin=$tmin if $tmin<$themin;
    $themax=$tmax if ($tmax==-1);
    $themax=$tmax if ($themax != -1 and $tmax > $themax);
    #print "\ngroup returns $themin,$themax with quant".$self->quant."\n";
    return qnormalize($themin,$themax,$self->quant);
}
sub pcre_tohampi::cut::minmax { die " Can't handle cut \n"; }
sub pcre_tohampi::lookahead::minmax { die "Can't handle lookahead\n"; }
sub pcre_tohampi::lookbehind::minmax { die "Can't handle lookbehind\n"; }
sub pcre_tohampi::conditional::minmax { die "Can't handle conditionals\n"; }
sub getminmax{
	my $self=shift;
	my $targetgroup=shift || 0;
	$groupcntr=1;
	%minhash=();
	%maxhash=();
	for my $node (@{ $self->{TREE} }){
	  my ($a,$b)= $node->minmax();
	  $minhash{0}=$a;
	  $maxhash{0}=$b;
    
    }
    
    return ($minhash{$targetgroup},$maxhash{$targetgroup});
}


my $case="";
my $counter=0;
my $capturenum=0;
my @array=();
my %casehash=();
my $valid_POSIX = qr{
  alpha | alnum | ascii | cntrl | digit | graph |
  lower | print | punct | space | upper | word | xdigit
}x;

my %exp = (
  # macros
  # Don't tell me \096 - \096 is stupid .. I know .. but I am lazy
  '\w' => '[\065 - \090] | [\097 - \122] | [\048 - \057] | [\095 - \095]' ,#word characters (a-z, A-Z, 0-9, _)',
  '\W' => '[\000 - \047] | [\058 - \064] | [\091 - \094] | [\096 - \096] | [\123 - \255]' ,#'non-word characters (all but a-z, A-Z, 0-9, _)',
  '\d' => '[\048 - \057]', #'digits (0-9)',
  '\D' => '[\000 - \047] | [\058 - \255]' , #'non-digits (all but 0-9)',
  '\s' => '[\009 - \009] | [\032 - \032]',# (\n, \r, \t, \f, and " ")',
  '\S' => '[\000 - \008] | [\010 - \031] | [\033 - \255]', #non-whitespace (all but \n, \r, \t, \f, and " ")',
  '.' => '[\032 - \126]',
);

my %slashhash = (
  '\n'=> "\n",
  '\t' => "\t",
  '\r' => "\r",
  "\\\\" => "\\",
  '\[' => "\[",
  '\(' => "\(",
  '\.' => "\.",
  '\{' => "\{",
  '\*' => "\*",
  '\+' => "\+",
  '\?' => "\?",
  '\}' => "\}",
  '\^' => "\^",
  '\)' => "\)",
  '\]' => "\]",
  '\_' => "\_",
  '\#' => "\#",
  '\"' => "\"",
  '\\\'' => "\'",
  '\%' => "\%",
  '\-' => "\-",
  '\>' => "\>",
  '\<' => "\<",
  '\0' => "\0",
#  '\v' => "\v",
  '\f' => "\f",
  '\$' => "\$",
  '\:' => "\:",
  '\@' => "\@",
  '\|' => "\|",
);

my $theregexstr="";
my $prefix="";

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


sub numToHampi {
	my $num=shift;
	my $str=$num;
	$str="0$str" if $num < 100;
	$str="0$str" if $num < 10;
	return "\\$str";
} 		

sub charToHampi{
	my $char=shift;
	return numToHampi(ord($char));
}


sub getNT{
	$counter++;
	return "$prefix\_q$counter";
}

sub addRule{
	my ($nt,$quant,@rhsarr) = @_;
    	my $out=join(" | ",@rhsarr);
	my $rule="cfg $nt := ".join(" | ",@rhsarr)." ;";
    	push @array,$rule;
	return $nt if ($quant eq "");
	#print STDERR "$rule\n";
	my $newnt=$nt;
	if ( $quant eq "+" or $quant eq "*" or $quant eq "?" ){
		$newnt=getNT();
		my $extrarule="cfg $newnt := ($nt)$quant;";
		push @array,$extrarule;
     }
	
	if ( $quant =~ /\{(\d+),\}/){
		my $n1 = $1;
		my $tempnt = getNT();
		$newnt = getNT();
		my $extrarule="cfg $newnt := "."$nt "x $n1."$tempnt;";
		push @array,$extrarule;
		$extrarule="cfg $tempnt := ($nt)* ; ";
		push @array,$extrarule;
     }
	
	if ( $quant =~ /\{(\d+),(\d+)\}/){
		my ($n1,$n2)=($1,$2);
		die "quantifier messed up first quantifier should be less than the second " if $n2 < $n1;
		my @rulearr=();
		push @rulearr,"$nt " x $_ for ($n1..$n2);
		my $extrarule = join "| ",@rulearr;
		$newnt = getNT();
		$extrarule="cfg $newnt := $extrarule;";	
		push @array,$extrarule;
     }
	
	if ( $quant =~ /\{(\d*)\}/ ){
        my $n = $1;
	   my $extrarule = "$nt " x $n;
	   $newnt = getNT();
	   $extrarule = "cfg $newnt := $extrarule;";
	   push @array,$extrarule;
	}
		
	
	if ( $newnt eq $nt and $quant ){
		die "\nunsupported quantifier $quant\n";
	}
	
	return $newnt;
}	
	

sub pcre_tohampi::anchor::tohampi { die "Can't handle anchor\n";}
sub pcre_tohampi::macro::tohampi { 
	my $self=shift;	
	return addRule(getNT(),$self->quant,$exp{$self->text});
	
}

sub pcre_tohampi::oct::tohampi { die "oct unsupported"; }
sub pcre_tohampi::hex::tohampi { 
  my $self=shift;
  my $rule= "";
  if($self->text =~ m/\\x([0-9a-f]{2})/i){
  $rule=numToHampi(hex($1));
  }else { die "hex string not right"; }
  return addRule(getNT(),$self->quant,$rule);
} 
sub pcre_tohampi::utf8hex::tohampi { die "utf8hex unsupported" ; }
sub pcre_tohampi::ctrl::tohampi { die "ctrl characters unsupported" ; }
sub pcre_tohampi::named::tohampi { die "named expressions unsupported";}
sub pcre_tohampi::Cchar::tohampi { die "cchars unsupported";}
sub pcre_tohampi::slash::tohampi { 
	my $self=shift;
	my $nt=getNT();
	my $str=$self->text;
	#bug bug bug .. security big stinking hole .. god save me
	$str = $slashhash{$str} || die "couldn't find $str in table";
	#print STDERR "slash string is $str";
	$str=charToHampi($str);
	return addRule($nt,$self->quant,$str);
	}
	
	
sub pcre_tohampi::any::tohampi { 
	my $self=shift;
	return addRule(getNT(),$self->quant,$exp{"."});
	}
sub pcre_tohampi::text::tohampi { 
	my $self=shift;
	my $nt=getNT();
	my $rhs="";
	if($case){
	#	print "\n\tinside text and case\n";
		my $str=lc($self->text);
		for my $char (split(//,$str)){
			my $asc=ord($char);
	#		print "asc is $asc\n";
			if($asc<97 || $asc>122){
				$rhs.=" ".charToHampi($char);
			}else{
				$rhs.=" $prefix\_alpha$char";
				$casehash{$char}="yes";
			}
		}
	#	print "\n\tending case: rule is $rhs";
	} else {
	$rhs = join " ",(map {numToHampi($_);} unpack("C*",$self->text));
	}
	#addRule($nt,$self->quant,$rhs);
	#print "wrote rule for ".$self->text."\n";
	return addRule($nt,$self->quant,$rhs);	
	
	}
sub pcre_tohampi::alt::tohampi { die " Can't handle alt\n"; }
sub pcre_tohampi::backref::tohampi { die "Can't handle backref\n";}
sub pcre_tohampi::class::tohampi {
	my $self=shift;
	my $class=$self->{TEXT};
	$class = $self->text if $self->{NEG} =~ /[pP]/;
	my $neg= ($self->{NEG} eq '^') ? 1: 0;
	my @numarr=();
	while ($class =~ s/^$cc_REx//) {
		my ($c1, $name, $pP, $utf8, $neg, $posix) = ($1,$2,$3,$4,$5,$6);
        #print "\n\t\t$c1 is c1\n";
		if($utf8 or $posix){ die "don't know what to do here \n"; }
		if ($c1 !~ /\\[wWdDsS]/ and $class =~ s/^-$cc_REx//) {
				my ($c2, $name, $pP, $utf8, $neg, $posix) = ($1,$2,$3,$4,$5,$6);
                #print "\n\t\tThe class $c1-$c2\n";
                my ($num1,$num2)=(ord($c1),ord($c2));
                $num1 =hex( $1) if($c1 =~ m/\\x([a-f0-9]{2})/i);
                $num2 = hex($1) if($c2 =~ m/\\x([a-f0-9]{2})/i);
                #print "\n\t\tpushing $num1 to $num2\n";
				push @numarr,$_ for($num1..$num2);
			} else {
				if ($c1 =~ /\\[wWdDsS]/){
					my $hampistring = $exp{$c1};
					while($hampistring =~ m/\[\\(\d{3})\s*-\s*\\(\d{3})\]/g){
						my ($n1,$n2) = ($1,$2);
						$n1 = $n1 + 0;
						$n2 = $n2 + 0;
						push @numarr,$n1..$n2;
					}
				}else {
                  my $num=-1;
                  $num = ord($c1) if (length $c1==1);
				  $num=ord($slashhash{$c1}) if ( length $c1 == 2 and exists $slashhash{$c1});
                  $num=hex($1) if ($c1 =~ m/\\x([a-f0-9]{2})/i);
                  die "error with char $c1 in class ".$self->{TEXT} if (length $c1 != 0 and $num==-1);
			  	  push @numarr,$num;
                }
				#print "just the char $c1 and value\n".ord($c1);
			} 
           
		}
#		print "c1 : $c1\t$name\t$pP\t$utf8\t$neg\t$posix\n";

	if($case){
	my @tmparr=();
	for my $charr (@numarr){
		push @tmparr,$charr+32 if($charr >=65 && $charr<=90);
		push @tmparr,$charr-32 if($charr >=97 && $charr<=122);
	}
	push @numarr,@tmparr;
	}
	
	if($neg){
		my %hash=();
		$hash{$_}=1 for(0...255);
		
		delete $hash{$_} for @numarr;
		@numarr=();
		push @numarr,$_ for (keys %hash);
	}
	my %seen ;
	$seen{$_}=1 for @numarr;
	@numarr= keys %seen;
	
	@numarr= sort {$a <=> $b} @numarr;
	my @rhsar=();
	my $start=shift @numarr;
	my $current=$start;
	for my $elem (@numarr){
		if ($elem == $current +1) {$current++; next;} ;
		my $rule=numToHampi($start);
		$rule="[$rule - ".numToHampi($current)."]" if ($current!=$start);
		push @rhsar ,$rule;
		$current=$elem;
		$start=$elem;
	}
	
      	my $rule=numToHampi($start);
      	$rule="[$rule - ".numToHampi($current)."]" if ($current!=$start);
      	push @rhsar,$rule;

	return addRule(getNT(),$self->quant,@rhsar);


	}
	

sub pcre_tohampi::comment::tohampi { die "can't handle comment\n"; }
sub pcre_tohampi::whitespace::tohampi { die "can't handle whitespace in regex \n";}
sub pcre_tohampi::flags::tohampi { die "can't handle flags \n";}
sub pcre_tohampi::code::tohampi { die "can't handle code\n"; }
sub pcre_tohampi::later::tohampi { die "can't handle later \n"; }
sub pcre_tohampi::capture::tohampi {
	# this is a non capturing group
	my $self=shift; 
	$capturenum++;
	my $nt = "$prefix\_flax$capturenum";
	
	my @rhsarr=();
	my $rhs="";
	#my @childarr=@{$self->{CONTENT}};
	#print $self->string; 
	for my $child (@{$self->{CONTENT}}){
		if($child->type eq "alt"){
			die "found an alt but there was no previous choice for".$self->fullstring if $rhs eq "";
			push @rhsarr,$rhs;
			$rhs="";
			next;
		}
		
		next if($child->type eq "anchor");
		  
		
		
		my $othernt = $child->tohampi;
		$rhs.=" $othernt";
			
	}
	
	push @rhsarr,$rhs ;
	return addRule($nt,$self->quant,@rhsarr);
	#now using the 
	
}


sub pcre_tohampi::group::tohampi { 
	my $self=shift; 
	my $nt = getNT();
	
	my @rhsarr=();
	my $rhs="";
	#my @childarr=@{$self->{CONTENT}};
	#print $self->string; 
	for my $child (@{$self->{CONTENT}}){
		if($child->type eq "alt"){
			die "found an alt but there was no previous choice " if $rhs eq "";
			push @rhsarr,$rhs;
			$rhs="";
			next;
		}
		
		next if($child->type eq "anchor");
		
		
		
		my $othernt = $child->tohampi;
		$rhs.=" $othernt";
			
	}
	
	push @rhsarr,$rhs;
	return addRule($nt,$self->quant,@rhsarr);
	
	
	}
sub pcre_tohampi::cut::tohampi { die " Can't handle cut \n"; }
sub pcre_tohampi::lookahead::tohampi { die "Can't handle lookahead\n"; }
sub pcre_tohampi::lookbehind::tohampi { die "Can't handle lookbehind\n"; }
sub pcre_tohampi::conditional::tohampi { die "Can't handle conditionals\n"; }

sub tothehampi{
	my $self=shift;
	$prefix=shift || "";
	my @nodes=@{ $self->{TREE} };
	my $regex=$self->display();
      
	$theregexstr=$regex;
	$case="";
	$case = "yes" if $regex =~ m/\([^-]*i-/;
	$counter=0;
	$capturenum=0;
	@array=();
	%casehash=();

	for my $node (@nodes){
		my $finalrule=$node->tohampi();
		
		my $rule = "cfg $prefix\_flax0 := $finalrule;\n";
		push @array,$rule;
		if($case){
			for my $char (keys %casehash){
				push @array,"cfg $prefix\_alpha$char := ".charToHampi($char)." | ".charToHampi(uc($char)).";";
			}
		}			
        return join("\n",@array);
	
	}
}



1;
