package CfiBinAnalyz;

#use strict;
use Exporter;
use Data::Dumper;
use feature 'say';

use vars qw($VERSION @ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

$VERSION     = 1.00;
@ISA         = qw(Exporter);
@EXPORT      = qw(cfi_analyze_pattern cfi_init_analyzer cfi_query_func_region cfi_query_taken_index_addr cfi_query_taken_code_addr);
@EXPORT_OK   = ();#qw(cfi_analyze_pattern);
#%EXPORT_TAGS = ( DEFAULT => [qw(&func1)],
#                 Both    => [qw(&func1 &func2)]);

use constant ORIG_POS    => 0;
use constant INSN_STR    => 1;
use constant RAW_BYTES   => 2;
use constant INSTRU_FLAG  => 3;
use constant BRANCH      => 4;
use constant BRAN_TARGET => 5;
use constant CALL_FLAG   => 6;

my $gpr ='\%eax|'.
	'\%ebx|'.
	'\%ecx|'.
	'\%edx|'.
	'\%esi|'.
	'\%edi|'.
	'\%esp|'.
	'\%ebp';

my $opcode_icf = 'call\s|calll\s|jmp\s|jmpl\s';	

my $cf_opcode = 'jmp\s|ljmp\s|jmpl\s|call\s|calll\s|jb\s|jnae\s|jc\s|jbe\s|jna\s|jcxz\s|jecxz\s|jl\s|jnge\s|jle\s|jng\s|jnb\s|jae\s|jnc\s|jnbe\s|ja\s|jnl\s|jge\s|jnle\s|jg\s|jno\s|jnp\s|jpo\s|jns\s|jnz\s|jne\s|jo\s|jp\s|jpe\s|js\s|jz\s|je\s';

my $insn_addr = '[0-9a-fA-F]{1,8}';
#instruction array format:
#	['orig_position','instruction string','raw bytes']

#=============================
#all global data structures are defined below
my @insn_array;
my %pos_mapping = ();
my %icf_target = ();
my @pos_get_pc_thunk;
my %pos_call_pop = ();
my @target_addr = ();
my @free_targets = ();
my @after_branch = ();

my %func_region = ();
#=============================
#all global variables are defined below
my $module_initialized = 0;
my $global_binname = "";
my $global_got_addr = "";


sub get_section_info {
	my $binname = $_[0];
	my $secname = $_[1];
	my $info = $_[2];
	my $cmd = "readelf -S ".$binname." |";
	open(BIN, $cmd) or die("cannot open file".$binname.": $!");
	while(<BIN>){
		if($_ =~ m/^\s*\[\s*([0-9]+)\]\s*([^\s]+)\s*([^\s]+)\s*([^\s]+)\s*([^\s]+)\s*([^\s]+)\s*([^\n]+)$/){
			if($2 eq $secname){
				if($info eq "addr"){
					return $4;
				}
				elsif($info eq "offset"){
					return $5;
				}
				elsif($info eq "size"){
					return $6;
				}
				elsif($info eq "num"){
					return $1;
				}
				elsif($info eq "type"){
					return $3
				}
			}
		}else{
			;#print $_;
		}
	}
	return "";
}




sub get_got_address {
	my $objname = $_[0];
	my $__got_addr;
	if($global_got_addr ne ""){
		return $global_got_addr;
	}
	$__got_addr = get_section_info($objname, ".got.plt","addr");
	if($__got_addr eq ""){
		$__got_addr = get_section_info($objname, ".got","addr");
	}				
	#print "got address:".$got_addr."\n";
	$global_got_addr = $__got_addr;
	return $__got_addr;
}

sub cfi_analyze_pattern {
	my $version = $_[0];
	my $direction = $_[1]; 	
	my $start_addr = $_[2];
	my $pattern_array = $_[3];
	my $match_insn = $_[4];
	my $aug_data = $_[5];
	my $distance = \@{$aug_data->{"distance"}};
	print "1st element: $$pattern_array[0]\n";
	print "2nd element: $$pattern_array[1]\n";
	my $index = $pos_mapping{$start_addr};
	if(not defined $pos_mapping{$start_addr}){
		@$match_insn = ();
		print "address: $start_addr does not exist in analyzer\n";
		return 0;
	}
	print "index is $index \n";
	my $x = $index - 1;
	my $y = 0;
	my $window = 64;
	my $search_end = $index - $window;	
	my $psize = @$pattern_array;
	my $cur_p = $$pattern_array[0];

	if($search_end < 0){
		$search_end = 0;
	}
	if($psize <=0){
		return 0;
	}
	@$match_insn = ();
	#say Dumper($distance);
	#say Dumper(@$distance);
	#say Dumper($$distance[0]);
	#say Dumper($$distance[1]);
	my $rest_distance = $$distance[0];
	say Dumper($rest_distance);
	print "initial distance between sub-pattern is $rest_distance\n";
	while($x >= $search_end){
		if($insn_array[$x][INSN_STR] =~ m/$$pattern_array[$y]/){	
			print "matching sub-pattern $y\n";
			if($y >= $psize -1){
				print "whole pattern matched!\n";
				my @insn = ($insn_array[$x][ORIG_POS], $insn_array[$x][INSN_STR], $insn_array[$x][RAW_BYTES]);
				push @$match_insn, [@insn];
				return 1;
			}else{
				my @insn = ($insn_array[$x][ORIG_POS], $insn_array[$x][INSN_STR], $insn_array[$x][RAW_BYTES]);
				push @$match_insn, [@insn];
				$y += 1;
				$rest_distance = $$distance[$y]; #renew distance between sub-pattern here
				print "distance between sub-pattern is $rest_distance\n";
			}
		}else{
			$rest_distance -= 1;
			if($rest_distance <= 0){
				print "distance use up when search for sub-pattern $y\n";
				return 0;
			}
		}
		if($insn_array[$x][INSN_STR] =~ m/^\s*jmp/ or $insn_array[$x][INSN_STR] =~ m/^\s*ret/){
			#print "fail to find match at $start_addr: meeting jmp or ret\n";
			return 0;
		}
		$x -= 1;
	}
	#print "fail to find match at $start_addr: window exceed\n";
	return 0;
}

sub cfi_init_analyzer {
	my $filename = $_[0];
	my $binname = $_[1];
	$global_binname = $binname;
	if($module_initialized == 1){
		return;
	}
	disasm_insn($filename, $binname);
	$module_initialized = 1;
}

sub cfi_query_func_region {
	my $addr = hex($_[0]);
	my @a = sort keys(%func_region);
	my $size = @a;
	my $start = hex($insn_array[0][ORIG_POS]);
	my $end = $start;
	for my $x (0 .. $size -1){
		if($addr < hex($a[$x])){
			$end = hex($a[$x]);
			last;
		}elsif($addr >= hex($a[$x])){
			$start = hex($a[$x]);
		}
	}
	$end = sprintf("%x",$end);
	$start = sprintf("%x",$start);
		#print "func region: $func\n";
		
	
	return ($start, $end);

}
sub cfi_query_taken_index_addr {
	my $start = $_[0];
	my $end = $_[1];
	my $size = @insn_array;
	if((not defined $pos_mapping{$start}) or (not defined $pos_mapping{$end})){
		print "invalide code region is given, abort\n";
		exit(1);
	}
	my $id_start = $pos_mapping{$start}; 
	my $id_end = $pos_mapping{$end}; 

	my %a = ();
	for my $x ($id_start .. $id_end){
		if($insn_array[$x][INSN_STR] =~ m/(mov[l]*|add[l]*)\s*-0x([0-9a-f]+)\(%ebx,%[a-z]+,[1248]\),/){
			my $off = hex($2);
			my $base = hex(get_got_address($global_binname));
			my $addr = sprintf("%x", $base-$off);
			$a{$addr} = 1;	
		}
	}

	return %a;
}

sub cfi_query_taken_code_addr {
	my $start = $_[0];
	my $end = $_[1];
	my $size = @insn_array;
	if((not defined $pos_mapping{$start}) or (not defined $pos_mapping{$end})){
		print "invalide code region is given, abort\n";
		exit(1);
	}
	my $id_start = $pos_mapping{$start}; 
	my $id_end = $pos_mapping{$end}; 

	my %a = ();
	for my $x ($id_start .. $id_end){
		if($insn_array[$x][INSN_STR] =~ m/lea[l]*\s*-0x([0-9a-f]+)\(%ebx\),/){
			my $off = hex($1);
			my $base = hex(get_got_address($global_binname));
			my $addr = sprintf("%x", $base-$off);
			if(defined $pos_mapping{$addr}){
				$a{$addr} = 1;	
			}
		}
	}

	##my @a = ("8048111", "8048222");
	return %a;

}
#disasm_insn dump instructions using objdump and lift up 
#but this is just a preprocessing stage, so the representation 
#may be different with the one in disasm_lift()
sub disasm_insn {
	print "binary analyzer: start disassembling and loading instructions\n";
	my $filename = $_[0];
	my $binname = $_[1];
	my $target = '[\$\%\w\d\_\@\-\.\+]+';
	my $INSN;
	my $cur_index = 0;
	my $cur_sym_index = 0;
	my @insn;
	@insn_array = ();
	%pos_mapping = ();
	@target_addr = ();
	@after_branch = ();
	my $cmd = "objdump -d $binname >$filename";
	system($cmd);
	open $INSN, $filename or print "cannot open file:$filename\n" and die $!;
	while(<$INSN>){
		#print $_;
		if($_ =~ m/^\s*([0-9a-f]+):\s+([^\t]+)\t([^\n]+)$/){
			#print $_;
			my $cur_pos = $1;
			my $cur_bytes = $2;
			my $cur_insn = $3;
			if($cur_insn =~ /^\s*lock[l]*/){
				#print "regard lock prefix as an independent insn\n";
				my $_bytes = "f0";
				my $_insn_str = ".byte 0xf0";
				@insn = ($cur_pos, $_insn_str, $_bytes);
				push @insn_array, [@insn];
				$pos_mapping{$cur_pos} = $cur_index;
				$cur_index = $cur_index+1;
				$cur_bytes =~ s/^\s*f0\s*//;
				$cur_insn =~ s/lock[l]*\s*//;
				$cur_pos = sprintf("%x", hex($cur_pos)+1);
			}

			if($cur_insn =~ m/^\s*($cf_opcode)\s+($insn_addr)\s+\<($target)\>\s*$/){
				my $__t = $2;
				if(hex($__t) != 0){
					push @target_addr, $2;
				}else{
					#when objdump tells you a call 0, or jump 0, either the code 
					#will not be executed or will be patched later.
					;
				}
			}elsif($cur_insn =~ /^\s*\(bad\)/){
				@insn = ($cur_pos, $cur_insn, trim($cur_bytes));
				print "analyzer warning: there is disassembly error\n";
				print $_;
				#last;
			}elsif($cur_bytes =~ /^\s*(00 )+/){
				if($insn_array[$cur_index -1][RAW_BYTES] =~ m/^\s*00 00\s*$/){
					push @after_branch, $cur_pos;
				}elsif($insn_array[$cur_index -1][INSN_STR] =~ m/^\s*(jmp[l]*|call[l]*|ret)/){
					push @after_branch, $cur_pos;
				}
			}
			@insn = ($cur_pos, $cur_insn, $cur_bytes);
			push @insn_array, [@insn];
			$pos_mapping{$cur_pos} = $cur_index;
			$cur_index = $cur_index +1;
		}elsif( $_ =~ m/^\s*([0-9a-f]+)\s*<([^>]+)>:\s*$/){
		#matching exported symbols
			my $sym_addr = $1;
			my $sym_name = $2;
			#print "$sym_addr\t$sym_name\n";
			$func_region{$sym_addr} = $sym_name;
		}
	}
	
	print "binary analyzer: loading disassembly done!";
}


1;
