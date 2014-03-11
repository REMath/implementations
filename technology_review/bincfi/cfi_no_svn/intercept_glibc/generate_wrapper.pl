#!/usr/bin/perl
sub trim
{
	my $string = shift;
	if($string eq ""){
		print "raw bytes is empty"."\n";
	}
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	return $string;
}
sub main
{
	$filename = "all_exported_glibc_funcs.txt";
	$outputfile = "glibc_wrapper.s";
	open(OUTPUT, '>'.$outputfile) or error("can't open file for output");
	open(FILE,'<',$filename) or error("cannot open file".$filename);
	while(<FILE>){
		$line = trim($_);
		print "generating function:".$line."\n";
		system('cat template.s|sed -e \'s/template/'.$line.'/g\'>>'.$outputfile);
	}
}

main();
