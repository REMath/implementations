#!/usr/bin/perl -w
use File::Basename;
use Switch;
my @lsda_func = ();
my @lsda_landing_pad =();
my @landing_pads = ();
my %eh_address = ();
my $eh_handler_tool = "true"; #path of katana
sub parse_eh_lsda {
	my $f = $_[0];
	open(my $eh, "<$f") or die("cannot read eh_lsda file: $f: $!\n");
	my $in_fde = 0;
	my $in_lsda = 0;
	my $cur_lsda_index = -1;

	my $func_addr = -1;
	my $lsda_idx = -1;
	while(<$eh>){
		if($_ =~ m/^\s*begin FDE\s*$/){
			$in_fde = 1;	
		}elsif($_ =~ m/^\s*end FDE\s*$/){
			$in_fde = 0;
			$func_addr = -1;
			$lsda_idx = -1;
		}elsif($_ =~ m/^initial_location:\s*0x([0-9a-f]+)\s*$/){
			my $addr = $1;
			$func_addr = hex($addr);
			#print "function address: $addr\n";
		}elsif($_ =~ m/^lsda_idx:\s*0x([0-9a-f]+)\s*$/){
			my $idx = hex($1);
			$lsda_idx = $idx;
			#print "function address: ".sprintf("%x",$func_addr)."\tlsda idx: $lsda_idx\n";
			if($func_addr == -1){
				print "function address error\n";
				exit(1);
			}
			$lsda_func[$lsda_idx] = $func_addr;
		}elsif($_ =~ m/^#LSDA\s*([0-9]+)\s*$/){
			$cur_lsda_index = int($1);
			@landing_pad =();
		}elsif($_ =~ m/^landing_pad:\s*0x([0-9a-f]+)\s*$/){
			my $pad_str = $1;
			my $pad_off = hex($pad_str);
			push @landing_pad, $pad_off;
			#print "function addr: ".sprintf("%x",$lsda_func[$cur_lsda_index])."\n";
			#print "landing pad: $pad_str\n";
			my $eh_addr = $lsda_func[$cur_lsda_index] + $pad_off;
			#if($pad_off != 0){
			#check out only live/effective landing pad address
				$eh_address{$eh_addr} = 1;
			#}
		}
	}
}
sub print_eh_addr {
	my $output = $_[0];
	my $mode = $_[1];
	my $OUT;
	if($mode eq "create"){
		open($OUT, ">$output") || die("cannot open file: $output for writing: $!\n");
	}elsif($mode eq "append"){
		open($OUT, ">>$output") || die("cannot open file: $output for writing: $!\n");
	}else{
		print "output mode unknown, no eh address will be dumped into file: $output\n";
		return;
	}
	print $OUT "EXCEPTION HANDLING ADDRESS:\n";
	foreach my $addr (keys(%eh_address)){
		print $OUT sprintf("%x",$addr)."\n";
	}	
}

sub invoke_katana {
	my $filename = $_[0];
	my $outfile = $_[1];
	my $path= $_[2];
	my $mode = $_[3];
	#generate script file for katana
	open(my $h, ">$path/$filename.katana")||die("cannot create file $filename.katana: $!\n");
	print $h "\$e=load\"$path/$filename\"\n";
	print $h "dwarfscript emit \$e \"$path/$filename.eh_lsda\"";
	print "dwarfscript for $filename is generated\n";
	close($h);
	my $cmd = "strip $path/$filename";
	system($cmd);
	if($eh_handler_tool ne "true"){
		$cmd = "$eh_handler_tool $path/$filename.katana";
		print "cmd: $cmd\n";
		system($cmd);
	}else{
		print "do not find tool for exception itargets, return\n";
		return;
	}
	my $lsda_file = "$path/$filename.eh_lsda";
	parse_eh_lsda($lsda_file);
	print_eh_addr("$path/$outfile", $mode);
}
sub load_config {
	#loading config file
	my $_configfile = "";
	$_configfile = $_[0];
	if(not defined $_[0]){
		open(CONFIG,'<'."./config") || open(CONFIG,'<'."../config") || die("can't open config file: $!");
	}else{
		open(CONFIG,'<'.$_configfile) || die("can't open config file: $!");
	}
	while(<CONFIG>){
		if($_ =~ m/^\s*#[^\n]*$/){
			print "skip comment lines in config\n";
		}elsif($_ =~ m/^\s*$/){
			print "skip empty lines in config\n";
		}elsif($_ =~ m/^([\S]+)\s*\=\s*([\S]+)\s*$/){
			$configopt = $1;
			$configval = $2;
			#print "config option:".$configopt."\n";
			switch( $configopt ){
				case "eh_handler_tool" {
					$eh_handler_tool = $configval;
				}
			}
		}
	}
}

if(@ARGV < 3){
	print "\n./get_eh_icf_address.pl [append|append] input_file output_filename\n";
	print "\tnote: input_file: absolute input file path name.\n";
	print "\tnote: output_filename: just file name.\n\n";
	exit(0);
}
my $output_mode = shift(@ARGV);
my $filepath = shift(@ARGV);
my $curpath = dirname($filepath);
my $filename = basename($filepath);
my $output = shift(@ARGV);
print "base: $curpath\n";
print "input: $filename\n";
print "output: $output\n";
#exit(0);
load_config();
invoke_katana($filename, $output, $curpath, $output_mode);
print "output file: $output\n";
