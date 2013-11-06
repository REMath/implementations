#/usr/bin/perl -w
#
#
# Author : Devdatta Akhawe
# Code under MIT license 
use strict;
use warnings;
use lib '.';
use pcre_tohampi;
use Cwd 'chdir';
my $startdir=$ENV{'PWD'};
chdir('../..');
my $count=0;
while(<>){
  chomp;
  my $regex=$_;
  next if $regex =~ m/^#/;
  #$regex=$1.$2 if( $regex =~ m/(\/.*?[^\\]\/[^\/g]*)g([^\/g]*)/);
  $regex=$1.$2 if( $regex =~ m/^(.*?)g([^\/]*)$/);
  $regex=eval 'qr'.$regex;
  my $p= pcre_tohampi->new($regex);
  $p->parse;
  my ($min,$max)=$p->getminmax();
  my $str=$p->tothehampi();
  die "error calculating minimum for regex" if $min<0;
  open(HMP,'>','/tmp/foo.hmp') or die $!;
  print HMP "\nvar string:$min;\n$str\nassert string in \_flax0;\n";
  $count++;
  #print HMP "\n cfg printablechar := [\\032-\\126];\n cfg printabletext := (printablechar)*;\n assert string in printabletext;\n";
  close(HMP);
  open(RES,"./hampi.sh /tmp/foo.hmp |") or die $!;
  $str="";
  $str.=$_ while(<RES>);
  close(RES);
  if($str =~ m/\n\{VAR\(string\)\=(.*?)\}$/s){
      die "Failure for $regex\n" if $1 !~ $regex;
      print "SUCCESS for $regex\n";
    } else {
      die "$regex : couldn't find a solution from hampi\n";
    }
}

chdir($startdir);
