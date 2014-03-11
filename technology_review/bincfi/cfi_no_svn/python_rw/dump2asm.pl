#!/usr/bin/perl -w
use Switch;
use Fcntl;
use Data::Dumper;
use Cwd;
use feature 'say';
use Digest::MD5 qw(md5_hex);
#use lib '..';
#use strict;
#use CfiBinAnalyz; #qw(cfi_analyze_pattern);
#=============================
#all global data are defined below
my $cur_pos = 0;
my $tapping = 0;
my $pre_pos = "";
my $objname = "";
my $cur_func = "";
my $cur_abi = "";
my $cur_section = "";
my $entry_begin = "";
my $global_binname ="";
my $exec_begin=0;
my $exec_end=0;


my $elf_type = ""; #EXEC ; DYN
my $bin_type = ""; #EXEC ; LIB
my $got_addr = "";
my $outputfile_fd;
my $testfile_fd;

my $after_branch_count = 0;

my $hICFT;#file handler for icf target
my $hICFT_opened = 0;
my $hICFTi;#file handler for icf target
my $hICFTi_opened = 0;
my $hRET;#file handler for ret target
my $hRET_opened = 0;

#=============================
#configuration value are defined below:
my $translate_ret_to_lookup = 0;
my $call_to_pushjmp=0;
my $translate_plt=0;
my $enforce_ret=0;
my $speculate_icf=0;
my $translate_jmp_table=0;
my $fix_disasm=1;
my $transparent_call=0;
my $save_eflags=1;
my $disasm_get_icf=0;
my $enforce_plt=0;
my $do_not_trans_syscall=1;
my $dump_direct_cf_target=1;
#=============================
#all const variables are defined below:
use constant BUNDLE_ALIGN => 5 ;
use constant BUNDLE_SIZE => 2 ** BUNDLE_ALIGN;

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
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=0']
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=1', 'position'(optional)]
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=1', 'position'(optional), callflag=1]
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=2']
#	instru_flag = 0: an original instruction (not instrumented)
#	instru_flag = 1: an instrumented instruction (indicates, the raw_bytes field is meaningless except the length)
#	instru_flag = 2: an newly added instruction (indicates, the raw_bytes field is meaningless except the length)
#	instru_flag = 3: an instrumented instruction that should NOT be touched by following passes
#	branch_flag = 0 or undefined: normal instructions
#	branch_flag = 1: direct control transfer; 'position' is the target
#	branch_flag = 1 & callflag=1: direct call; 'position' is the target
#	branch_flag = 2: indirect control transfer using return
#	callflag = 2: indirect call
#	branch_flag = 3 & callflag=2: indirect call
#	branch_flag = 3 & callflag=3: indirect jump in .text
#	branch_flag = 3 & callflag=4: indirect jump in .plt

#instru_flag options, static variables
my $I_ORIGINAL = 0;
my $I_TRANSLATED = 1;
my $I_ADDED = 2;
my $I_NEVER_TOUCH = 3;

# branch_flag options
my $B_IS_NON_CF = "0";
my $B_IS_DIRECT_CF = "1";
my $B_IS_RETURN = "2";
my $B_IS_INDIRECT_CALLJMP = "3";

# call_flag options, only valid when branch_flag is "1" or "3"
my $C_INVALID = 0;
my $C_CALL = 1;
my $C_ICALL = 2;
my $C_IJMP_TEXT = 3;
my $C_IJMP_PLT = 4;

#=============================
#all global data structures are defined below
my @insn_array;
my %pos_mapping = ();
my %icf_target = (); # target address ==> src_address_table (src_address ==> 1);  
my @pos_get_pc_thunk;
my %pos_call_pop = ();
my @target_addr = ();
my @free_targets = ();
my %free_branches = ();
my @after_branch = ();
my @disasm_bad = ();

my %reverse_target = ();#currently only support one reverse target
my %speculate_jmp_table = ();#record symbols of a speculated jmp table
my $speculate_table_size = 0x1000;
# hash tables for icf targets information
# used when speculate_icf=1
# the info comes from dynamic translation using PIN
my %ret_target = ();
my %jmp_target = ();
my %call_target = ();

my %cmd_map = ();

my %func_region = ();
#=============================
#all routines/functions are defined below

sub get_filename_from_cmd {
	my $cmd = $_[0];
	my $filename = "";
	if(not defined $cmd_map{$cmd}){
		$filename = "/tmp/".substr( md5_hex($cmd), 0, 16);
		$cmd_map{$cmd} = $filename;
		chop($cmd); #remove the last "|" in cmd
		$cmd = $cmd. " >".$filename;
		system($cmd);
	}else{
		$filename = $cmd_map{$cmd};
	}
	return $filename;
}

sub trim
{
	my $string = shift;
	if($string eq ""){
		;#print "raw bytes is empty"."\n";
	}
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	return $string;
}

sub translation_abort {
	unlink("./generated_asm.s");
	unlink("./myrodata.s");
	unlink("./analysis_done");
	exit(1);
}

sub get_elf_type {
	my $binname = $_[0];
	my $cmd = "readelf -h ".$binname." |";
	$cmd = get_filename_from_cmd($cmd);
	open(BIN, $cmd) or die("cannot open file".$cmd.": $!");
	while(<BIN>){
		if($_ =~ m/^\s*Type:\s*([^\s]+)\s*\([^)]+\)\s*$/){
			if($1 eq "DYN"){
				print "this is a shared library from elf format\n";
				$elf_type = "DYN";
			}elsif($1 eq "EXEC"){
				print "this is an executable file from elf format\n";
				$elf_type = "EXEC";
			}
		}
		else{
			;#print $_;
		}
	}




}
sub get_section_info {
	my $binname = $_[0];
	my $secname = $_[1];
	my $info = $_[2];
	#my $cmd = "readelf -S ".$binname." |";
	my $cmd = "readelf -S ".$binname." |";
	$cmd = get_filename_from_cmd($cmd);
	#open(BIN, $cmd) or die("cannot open file".$binname.": $!");
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
	if($got_addr ne ""){
		return $got_addr;
	}
	$__got_addr = get_section_info($objname, ".got.plt","addr");
	if($__got_addr eq ""){
		$__got_addr = get_section_info($objname, ".got","addr");
	}				
	#print "got address:".$got_addr."\n";
	$got_addr = $__got_addr;
	return $__got_addr;
}

sub setup_bin_type {
	my $_bname = $_[0];
	my $sonname_line = "";
	my $soname = "";
	get_elf_type($_bname);
	if($elf_type eq "EXEC"){
		$bin_type = "EXEC";
	}elsif($elf_type eq "DYN"){
	
		$cmd = "readelf -d ".$_bname." |"."awk \'{print \$2}\'|";
		$cmd = get_filename_from_cmd($cmd);
		open(BIN, $cmd) or die("cannot open file".$_bname.": $!");
		while(<BIN>){
			if($_ =~ m/\s*\(SONAME\)\s*/){
				print "this is a shared library from dynamic section\n";
				$sonname_line = $_;
				$bin_type = "LIB";
			}
		}
		if($bin_type eq ""){
			print "this is a PIE code\n";
			$bin_type = "EXEC";
		}
		close(BIN);
		if($sonname_line =~ m/(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$/){
		$soname = $_[5];
		if($soname =~ m/\s*\[ld-linux\.so\.2\]\s*/){
			print "line:".$_;
			print "this is dynamic linker, regard it as EXEC\n";
			$bin_type = "EXEC";
		}elsif($soname =~ m/\s*\[linux-ld\.so\.[0-9]\]\s*/){
			print "line:".$_;
			print "this is dynamic linker, regard it as EXEC\n";
			$bin_type = "EXEC";
		}
		}
	}
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
				case "bundle_align" {
					#print "option:".$configopt."\n";
					#print "value:".$configval."\n";
				}
				case "return2lookup" {
					if($configval != 1 and $configval != 0 and $configval !=2){
						print "return2lookup error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$translate_ret_to_lookup = $configval;

				}
				case "call_to_pushjmp" {
					if($configval != 1 and $configval !=0){
						print "call_to_pushjmp error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$call_to_pushjmp = $configval;
				}
				case "transform_plt"{
					if($configval != 1 and $configval !=0){
						print "call_to_pushjmp error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$translate_plt = $configval;
				}
				case "enforce_plt"{
					if($configval != 1 and $configval !=0){
						print "enforce_plt error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$enforce_plt = $configval;
				}

				case "enforce_ret"{
					if($configval != 1 and $configval !=0){
						print "enforce_ret error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$enforce_ret = $configval;
				}
				case "speculate_icf"{
					if($configval != 1 and $configval !=0){
						print "speculate_icf error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$speculate_icf = $configval;
				}
				case "translate_jmp_table"{	
					if($configval != 1 and $configval !=0){
						print "translate_jmp_table error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$translate_jmp_table = $configval;
				}
				case "transparent_call"{	
					if($configval != 1 and $configval !=0){
						print "transparent_call error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$transparent_call = $configval;
				}
				case "save_eflags"{	
					if($configval != 1 and $configval !=0){
						print "save_eflags error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$save_eflags = $configval;
				}
				case "disasm_get_icf"{	
					if($configval != 1 and $configval !=0){
						print "disasm_get_icf error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$disasm_get_icf = $configval;
		

				}
				case "do_not_trans_syscall"{	
					if($configval != 1 and $configval !=0){
						print "do_not_trans_syscall error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$do_not_trans_syscall = $configval;
		

				}
				case "dump_direct_cf_target"{	
					if($configval != 1 and $configval !=0){
						print "dump_direct_cf_target error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$dump_direct_cf_target = $configval;
		

				}

				case "fix_disasm"{	
					if($configval != 1 and $configval !=0){
						print "fix_disasm error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						translation_abort();
					}
					$fix_disasm = $configval;
		

				}else{
					#print "unknown config option:".$configopt."\n";
					#translation_abort();
			
				}
			}
		}else{
			print "unknown recognized option:".$_."\n";
			translation_abort();
		}
	}
	close(CONFIG);
	#==================================================
	#all the preparation work should be done below here!
	print "global_binname is: $global_binname\n";
	get_elf_type($global_binname);
	setup_bin_type($global_binname);
	get_got_address($global_binname);

	print "the end of initialization work\n";
}
#=======================================================
# fixing disassembly issue related functions
sub convert_vma_to_offset {
	my $vma = $_[0];
	my $offset = -1;
	my $binname = $_[1];
	print "convert: binname is:$binname\n";
	#$cmd = "readelf -W -l $binname |sed -e '1,/^\\s*\$/d'|sed  '/^\\s*\$/q'|";
	$cmd = "readelf -W -l $binname |sed -e '1,/^\\s*\$/d'|sed  '/^\\s*\$/q' |";
	$cmd = get_filename_from_cmd($cmd);
	open(MYBIN, $cmd) or die("cannot open file".$binname." $!");
	#open(MYBIN, $cmd) or die("cannot open file".$binname." $!");
	while(<MYBIN>){
		if($_ =~ m/^\s*[a-zA-Z_]+\s*0x([0-9a-f]+)\s*0x([0-9a-f]+)\s*0x([0-9a-f]+)\s*0x([0-9a-f]+)\s*0x([0-9a-f]+)/){
			$offset_base = $1;
			$vma_base = $2;
			$file_size = $4;
			$mem_size = $5;
			print $_;
			if((hex($vma) < hex($vma_base)) or (hex($vma) > (hex($vma_base)+hex($mem_size)))){
				next;
			}else{
				$offset_in_base = hex($vma) - hex($vma_base);
				if($offset_in_base <= hex($file_size)){
					$offset = $offset_in_base + hex($offset_base);
					return $offset;
				}else{
				#vma is in bss section, where file offset is fixed
					$offset = hex($offset_base) + hex($file_size);
					return $offset;
				}
			}
		}
	}
}
sub zero_padding_len {
	my $loc = shift;
	my $binname = shift;
	my $byte = 0xff;
	my $zcount = 0;
	my $offset =  convert_vma_to_offset($loc, $binname);
	open my $binfh, '+<',$binname or die("cannot open file: $binname, $!\n");

	seek $binfh, $offset+1, 0;
	read($binfh, $byte, 1);

	my $hex_byte = sprintf("%x",unpack('C',$byte));
	
	while($hex_byte =~ m/^\s*0/){
		$zcount +=1;
		read($binfh, $byte, 1);
		$hex_byte = sprintf("%x",unpack('C',$byte));
	}
	return $zcount;
}

sub do_padding_zero {
	#magic_offset is hex
	my $magic_loc = $_[0];
	my $binname = $_[1];
	my $magic_offset =  convert_vma_to_offset($magic_loc, $binname);
	open my $binfh, '+<',$binname or die("cannot open file: $binname, $!\n");
	binmode($binfh);
	seek $binfh, $magic_offset, 0;
	my $hex_magic = sprintf("%x", $magic_offset);
	print "magic offset is $hex_magic\n";
	my $zcount = 0;
	while(read($binfh, $byte, 1)!=0){
		my $hex_byte = sprintf("%x",unpack('C',$byte));
		if($hex_byte =~ m/^\s*0/){
			print "current byte is zero, $hex_byte, pad it with 0x90\n";
			$zcount = $zcount +1;
		}else{
			print "current byte is not zero: $hex_byte\n";
			last;
		}
	}
	if($zcount >0){
		print "zcount: $zcount\n";
		seek $binfh, -($zcount+1),1;
		vec($buffer, 0, 8) = 0x90;
		#print "buffer $buffer\n";
		print $binfh $buffer for (1 .. $zcount); 
	}

}
sub disasm_insn {
	print "fixing disassembly: this pass will try to fix disassembly issues after, 1\n";
	my $filename = $_[0];
	my $binname = $_[1];
	my $target = '[\$\%\w\d\_\@\-\.\+\*]+';
	my $INSN;
	my $cur_index = 0;
	my $disasm_error = 0;
	my $insn_count = 400; #heuristic: continue disassembling $insn_count before exit

	my @insn;
	@insn_array = ();
	%pos_mapping = ();
	%target_addr = ();
	%free_branches = ();
	@after_branch = ();
	@disasm_bad = ();
	my $cmd = "objdump -w -d $binname >$filename";
	print "fixing disassembly: this pass will try to fix disassembly issues after 2\n";
	print "fixing disassembly: $cmd\n";
	#system($cmd);
	print "fixing disassembly: this pass will try to fix disassembly issues after 3\n";
	open $INSN, $filename or print "cannot open file:$filename\n" and die $!;
	print "disasm_insn: try to disassemble file; binname is :$binname\n";
	while(<$INSN>){
		if($_ =~ m/^\s*([0-9a-f]+):\s+([^\t]+)\t([^\n]+)$/){
			#print $_;
			my $cur_pos = $1;
			my $cur_bytes = $2;
			my $cur_insn = $3;
			if($cur_insn =~ /^\s*lock[l]*/){
				#print "regard lock prefix as an independent insn\n";
				my $_bytes = "f0";
				my $_insn_str = ".byte 0xf0";
				@insn = ($cur_pos, $_insn_str, $_bytes, $I_ADDED);
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
					$target_addr{$cur_pos} = $__t;
				}else{
					#when objdump tells you a call 0, or jump 0, either the code 
					#will not be executed or will be patched later.
					;
				}
			}elsif($cur_insn =~ /^\s*\(bad\)/){
				print "there is disassembly error\n";
				print $_;
				#@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL);
				#push @insn_array, [@insn];
				#$pos_mapping{$cur_pos} = $cur_index;
				push @disasm_bad, $cur_pos;
				#continue disassembling
				$disasm_error = 1;
				#last;
			}elsif($cur_bytes =~ /^\s*(00 )+/){
				if($insn_array[$cur_index -1][RAW_BYTES] =~ m/^\s*00 00\s*$/){
					push @after_branch, $cur_pos;
				}elsif($insn_array[$cur_index -1][INSN_STR] =~ m/^\s*(jmp[l]*|call[l]*|ret)/){
					push @after_branch, $cur_pos;
				}
			}
			@insn = ($cur_pos, $cur_insn, $cur_bytes, $I_ORIGINAL);
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
		if($disasm_error == 1){
			#continue disassembling $insn_count number of instructions
			$insn_count = $insn_count - 1;
			if($insn_count <=0){ last};
		}

	}
}
sub check_disasm_issue {
	my $index;
	my $found = 0;	
	my $size = @insn_array;
	print "this routine will check disassembly issues.\n";
	if($insn_array[$size -1][1] =~ m/^\s*\(bad\)/){
		return 1;
	}
	if(@disasm_bad > 0){
		return 1;
	}
	@free_targets = ();
	foreach my $x (keys(%target_addr)){
		if(not defined $pos_mapping{$target_addr{$x}}){
			print "free target address: $target_addr{$x}\n";
			push @free_targets, $target_addr{$x};
			$free_branches{$x} = $target_addr{$x};
			$found =1 ;
		}
	}

	if($found == 1){
		return 1;
	}
	#if((@after_branch > 0)  and ($after_branch_count < 1)){
	#	print "continue searching padding after branch. $after_branch_count\n";
	#	return 1;
	#}
	print "no disassembly issue found, moving forward\n";
	return 0;
}

sub check_invalid_icf_target {
	foreach my $x (keys(%icf_target)){
		if(not defined $pos_mapping{$x}){
			printf "inconsistant icf_target found: $icf_target{$x} becomes invalid\n";
			return 2;	
		}
	}
	return 0;
}


sub _fix_free_branch {
	my $loc = $_[0];
	my $binname = $_[1];
	#my $insn_loc = $_[2];
	my $w = 0;
	my $magic_loc;
	my $found = 0;
	if(if_within_exec($loc) == 0){
		#print "exec_begin: $exec_begin\n";
		#print "exec_end: $exec_end\n";
		return 0;
	}
	#step 1: find the nearest valid insn boundary
	while(not defined $pos_mapping{$loc}){
		$loc = sprintf("%x",hex($loc)-1);
	}
	#print "nearest insn boundary is $loc\n";
	my $index = $pos_mapping{$loc};
	if($insn_array[$index][RAW_BYTES] =~ m/^\s*(00 )+/){
		#confirm that it is zero padding
		print "zero padding possible\n";
		while($w < 16){
			if($insn_array[$index - $w][RAW_BYTES] =~ m/^\s*(00 )+/){
				$w = $w+1;
				next;
			}elsif($insn_array[$index - $w][RAW_BYTES] =~ m/^\s*00 00\s*$/){
				$w = $w+1;
				next;
			}elsif($insn_array[$index - $w][INSN_STR] =~ m/^\s*(jmp[l]*|call[l]*|ret[l]*)/){
				$magic_loc = $insn_array[$index - $w][ORIG_POS];
				my $_bytes = $insn_array[$index - $w][RAW_BYTES];
				$_bytes =~ s/ //g;
				my $len = length($_bytes)/2;
				$magic_loc = sprintf("%x", hex($magic_loc)+$len);
				$found = 1;
				last;
			}else{
				$found = 0;
				last;
			}
			print "window: $w\n";
			$w = $w +1;
		}
		if($found == 1){
			#step 2: patch binary
			print "begin to pad zero\n";
			do_padding_zero($magic_loc, $binname);
			return 1;
		}else{
			print "pattern mismatch, return\n";
			return 0;
		}
	}else{
		return 0;
	}
}

sub save_insn {
	my $pos = shift;
	my $binname = shift;
	open my $P, ">>./bin_patch";
	print $P "$pos: $insn_array[$pos_mapping{$pos}][RAW_BYTES]\n";
	close($P);
}
sub pad_all_data {
	my $binname = shift;
	open my $P, "<./bin_patch" or die("cannot open file: bin_patch, $!\n");
	open my $binfh, '+<',$binname or die("cannot open file: $binname, $!\n");
	binmode($binfh);
	while(<$P>){
		if($_ =~ m/^\s*([0-9a-f]+):\s*([^\n]+)$/){
			my $pos = $1;
			my $raw_bytes = trim($2);	
			my $offset = convert_vma_to_offset($pos, $binname);
			seek $binfh, $offset, 0;
			foreach my $s ( split(' ',$raw_bytes)){
				my $buf =0;
				print $s."\n";
				vec($buf, 0, 8) = 0x90;
				#vec($buf, 0, 8) = hex($s);
				print $binfh $buf;
			}

		}
	}
	close($binfh);
	close($P);
}
sub patch_back_insn {
	my $binname = shift;
	open my $P, "<./bin_patch" or (print "cannot open file: bin_patch, $!\n" and return);
	open my $binfh, '+<',$binname or die("cannot open file: $binname, $!\n");
	binmode($binfh);
	while(<$P>){
		if($_ =~ m/^\s*([0-9a-f]+):\s*([^\n]+)$/){
			my $pos = $1;
			my $raw_bytes = trim($2);	
			my $offset = convert_vma_to_offset($pos, $binname);
			seek $binfh, $offset, 0;
			foreach my $s ( split(' ',$raw_bytes)){
				my $buf =0;
				print $s."\n";
				vec($buf, 0, 8) = hex($s);
				#vec($buf, 0, 8) = hex($s);
				print $binfh $buf;
			}

		}
	}
	close($binfh);
	close($P);
}
#pad instruction with 0x90
sub pad_insn {
	my $pos = shift;
	my $binname = shift;
	my $idx = $pos_mapping{$pos};
	my $raw_bytes = trim($insn_array[$idx][RAW_BYTES]);
	my $offset = convert_vma_to_offset($pos, $binname);
	open my $binfh, '+<',$binname or die("cannot open file: $binname, $!\n");
	binmode($binfh);
	seek $binfh, $offset, 0;
	foreach my $s ( split(' ',$raw_bytes)){
		my $buf =0;
		print $s."\n";
		vec($buf, 0, 8) = 0x90;
		#vec($buf, 0, 8) = hex($s);
		print $binfh $buf;
	}
	close($binfh);

}

sub _fix_after_branch {
	my $loc = $_[0];
	my $binname = $_[1];
	return _fix_free_branch($loc, $binname);
}

sub do_fix_disasm_after_branch {
	my $binname = $_[0];
	my $size = @after_branch;
	print "begin to fix padding after branch\n";
	if($size <= 0){
		print "there is no free branch, return\n";
		return;
	}
	for $x (0 .. $size -1){
		if(not defined $target_addr{$after_branch[$x]}){
			print "try to fix after branch;  target location: $after_branch[$x]\n";
			if(_fix_after_branch($after_branch[$x], $binname) == 1){
				print "fixed one free branch, regenerate disassembly\n";
				return;
			}
		}
	}

}

sub do_fix_disasm_bad {
	my $location = $_[0];
	my $binname = $_[1];
	my $offset = 0;
	my $index;
	my $window = 0;
	my $magic_loc = "";
	my $byte;
	my $buffer = 0;
	vec($buffer, 0, 8) = 0x90;
	print "fixing (bad); target location: $location\n";
	$offset = convert_vma_to_offset($location, $binname);
	$hex_off = sprintf("%x",$offset);
	print "vma: $location\t offset:$hex_off\n";

	if(not defined $pos_mapping{$location}){
		print "error in do_fix_disasm_bad, abort\n";
		translation_abort();
	}
	$index = $pos_mapping{$location};

	#step 1: figure out the nearest ret or jmp/call *
	while($window < 32){
		#print "current index: $index\tinsn:$insn_array[$index - $window][INSN_STR]\n";
		print "$insn_array[$index - $window][ORIG_POS]:\tcurrent insn: ".$insn_array[$index - $window][INSN_STR]."\n";
		#finding a ret followed by at least 3 zero bytes
		if($insn_array[$index - $window][INSN_STR] =~ m/^\s*ret/){
		#	 and 
		#	$insn_array[$index - $window + 1][RAW_BYTES] =~ m/^\s*00/ and
		#	(hex($insn_array[$index - $window + 1][ORIG_POS]) - hex($insn_array[$index - $window][ORIG_POS]) >= 3)){
			if(zero_padding_len($insn_array[$index-$window][ORIG_POS], $binname) >= 3){
				$magic_loc = $insn_array[$index - $window][ORIG_POS];
				my $_bytes = $insn_array[$index - $window][RAW_BYTES];
				print "insn bytes: $_bytes\n";
				$_bytes =~ s/\s*//g;
				my $len = length($_bytes)/2;
				print "insn str: $_bytes\tinsn length: $len\n";
				$magic_loc =sprintf("%x", hex($magic_loc)+$len);
				last;
			}else{
				print "not sure if there is padding issue here\n";
			}
		}elsif($insn_array[$index - $window][INSN_STR] =~ m/^\s*jmp\s*([0-9a-f]+)/){
			my $tgt = $1;
			print "direct control flow insn, target: $tgt\n";
			if(hex($tgt) > hex($insn_array[$index - $window][ORIG_POS])){
				print "forward jump/call\n";
				if(hex($tgt) > hex($insn_array[$index][ORIG_POS])){
					print "forward jump with target passing disassembly error\n";
					my $idx = $pos_mapping{$tgt};
					my $i = $index - $window + 1;
					while($i < $idx){
						pad_insn($insn_array[$i][ORIG_POS], $binname);
						$i = $i+1;
					}
					last;
				}
			}
			#translation_abort();
		}elsif($insn_array[$index - $window][INSN_STR] =~ m/^\s*jmp[lq]?\s*\*/){
			if(zero_padding_len($insn_array[$index-$window][ORIG_POS], $binname) >= 3){
				$magic_loc = $insn_array[$index - $window][ORIG_POS];
				my $_bytes = $insn_array[$index - $window][RAW_BYTES];
				print "insn bytes: $_bytes\n";
				$_bytes =~ s/\s*//g;
				my $len = length($_bytes)/2;
				print "insn str: $_bytes\tinsn length: $len\n";
				$magic_loc =sprintf("%x", hex($magic_loc)+$len);
				last;
			}else{
				print "not sure if there is padding issue here, pad (bad) with nop. Pad it with nop\n";
				pad_insn($insn_array[$index][ORIG_POS],$binname);
				last;
			}
		}
		$window = $window +1;
	}
	#step 2: patch the binary content after magic location
	if($magic_loc eq ""){
		print "magic location not found, return\n";
		return;
	}

	do_padding_zero($magic_loc, $binname);

}

sub do_fix_disasm_after_branch {
	my $binname = $_[0];
	my $size = @after_branch;
	print "begin to fix padding after branch\n";
	if($size <= 0){
		print "there is no free branch, return\n";
		return;
	}
	for $x (0 .. $size -1){
		if(not defined $target_addr{$after_branch[$x]}){
			print "try to fix after branch;  target location: $after_branch[$x]\n";
			if(_fix_after_branch($after_branch[$x], $binname) == 1){
				print "fixed one free branch, regenerate disassembly\n";
				return;
			}
		}
	}

}

sub do_fix_disasm_free_branch {
	my $binname = $_[0];
	#my $size = @free_targets;
	my $size = keys(%free_branches);
	if($size <= 0){
		print "there is no free branch, return\n";
		return;
	}
	foreach $x (keys(%free_branches)){
		print "try to fix free branch; insn location: $x;  target location: $free_branches{$x}\n";
		if(_fix_free_branch($free_branches{$x}, $binname) == 1){
			print "fixed one free branch, regenerate disassembly\n";
			return;
		}
	}
	
	foreach $x (keys(%free_branches)){
		print "regard insn at location: $x as data\n";
		#save_insn($x, $binname);
		#pad_insn($x, $binname);
	}
#	for $x (0 .. $size -1){
#		print "try to fix free branch;  target location: $free_targets[$x]\n";
#		if(_fix_free_branch($free_targets[$x], $binname) == 1){
#			print "fixed one free branch, regenerate disassembly\n";
#			return;
#		}
#	}
}

sub do_fix_disasm {
	my $size = @insn_array;
	my $binname = $_[0];
	print "do_fix_disasm: this routine starts fixing disassembly issues\n";
	if($insn_array[$size -1][1] =~ /^\s*\(bad\)/){
		do_fix_disasm_bad($insn_array[$size-1][0], $binname);
		return 1;
	}
	if(@disasm_bad > 0){
		do_fix_disasm_bad($disasm_bad[0], $binname);
		return 1;
	}
	$size = @free_targets;
	if($size > 0){
		do_fix_disasm_free_branch($binname);
		return 1;
	}
#	$size = @after_branch;
#	if($size > 0){
#		do_fix_disasm_after_branch($binname);
#		$after_branch_count = $after_branch_count +1;
#		return 1;
#	}
	return 0;#nothing has been done
}


sub fix_disasm_issue {
	my $dump_asm = $_[0];
	my $binname = $_[1];

	($exec_begin, $exec_end) = get_elf_exec_range($binname);

#	disasm_insn($dump_asm, $binname);
#
#	if($fix_disasm == 0){
#		return;
#	}

#	print "fix disasm issue: this pass will try to fix disassembly issues\n";
#	system("rm -f ./bin_patch");
#	my $issue_found = check_disasm_issue();
#	while($issue_found != 0){
#		do_fix_disasm($binname);
#		disasm_insn($dump_asm, $binname);	
#		analyze_icf_target($binname);
#		fix_disasm_using_invalid_target($binname, $dump_asm);
#
#		$issue_found = check_disasm_issue();
#	}
	$issue_found = 1;
	while($issue_found){
		print "beginning disassembing instructions...phase #1\n";
		my $cmd = "objdump -w -d $binname >$dump_asm";
		system($cmd);
		my $pid = fork();
		die "cannot fork() : $!\n" unless defined $pid;
		if ($pid){
		#parent process
			print "child pid $pid\n";
			if (waitpid($pid, 0) > 0){
				my ($rc, $sig, $core) = ($? >> 8, $? & 127, $? & 128);
				if ($core){
					print "$pid dumped core\n";
				}elsif($sig == 9){
					print "$pid was murdered!\n";
				}else{
					print "$pid returned value: $rc";
					print ($sig?" after receiving signal $sig\n":"\n");
					if($rc == 100){
						$issue_found = 1;
					}elsif($rc == 50){
						$issue_found = 0;
						last;
					}
				}
   			}else{
      				print "$pid... um... disappeared...\n";
   			}
		}else{
		#child process
			system("rm -f ./bin_patch");
			disasm_insn($dump_asm, $binname);
			$issue_found = check_disasm_issue();
			if($issue_found == 0){
				exit(50);
			}
			do_fix_disasm($binname);
			#analyze_icf_target($binname);
			#fix_disasm_using_invalid_target($binname, $dump_asm);
			exit(100);
		}
		#======================================================
		print "beginning disassembing instructions...phase #2\n";
		$cmd = "objdump -w -d $binname >$dump_asm";
		system($cmd);
		$pid = fork();
		if ($pid){
		#parent process
			print "child pid $pid\n";
			if (waitpid($pid, 0) > 0){
				my ($rc, $sig, $core) = ($? >> 8, $? & 127, $? & 128);
				if ($core){
					print "$pid dumped core\n";
				}elsif($sig == 9){
					print "$pid was murdered!\n";
				}else{
					print "$pid returned value: $rc";
					print ($sig?" after receiving signal $sig\n":"\n");
					if($rc == 100){
						$issue_found = 1;
					}elsif($rc == 50){
						$issue_found = 0;
						last;
					}
				}
   			}else{
      				print "$pid... um... disappeared...\n";
   			}

		}else{
		#child process
			system("rm -f ./bin_patch");
			disasm_insn($dump_asm, $binname);
			analyze_icf_target($binname);
			fix_disasm_using_invalid_target($binname, $dump_asm);
			$issue_found = check_disasm_issue();
			if($issue_found == 0){
				exit(50);
			}
			exit(100);
		}
	}
	do {
	#	analyze_icf_target($binname);
	#	fix_disasm_using_invalid_target($binname, $dump_asm);
		disasm_insn($dump_asm, $binname);
		analyze_icf_target($binname);
		$issue_found = check_invalid_icf_target();
	}while($issue_found != 0);

	patch_back_insn($binname);
}

#==================================================
# reading icf related functions
sub read_all_icf {
	my $icf = $_[0];
	my $ICF;
	my $icf = "./icf_final.out";
	my $record = 0;
	if($speculate_icf != 1){
		print "$speculate_icf\n";
		return;
	}
	open $ICF, $icf or print "cannot open file: $icf\n" and return;
	my @RET_SET = ();
	while(<$ICF>){
		if($_ =~ m/^\s*([0-9]+)\s*([0-9a-f]+)\t([^\t]+)\t([0-9a-f]+)$/){
			my $num = $1;
			my $src_addr=$2;
			my $src_insn=$3;
			my $target_addr=$4;
			if($src_insn =~ m/^ret/){
				if(not defined $ret_target{$src_addr}){
					my %ret_instance = ();
					$ret_instance{$target_addr} = int($num);
					$ret_target{$src_addr} = {%ret_instance};
					$record = $record +1;
				}else{
					my $a = $ret_target{$src_addr};
					if(not defined $a->{$target_addr}){
						$a->{$target_addr} = int($num);
						#say Dumper(%$a);
						$record = $record +1;
					}else{
					#tolerate duplicate src -> target
						$a->{$target_addr} = $a->{$target_addr} + int($num);
					}
				}	
			}
			
		}
	}
	print "$record itarget summary record has been read\n";
}

sub read_all_icf_v2 {
	my $icf = $_[0];
	my $ICF;
	my $icf = "./icf.out";
	my $record = 0;
	if($speculate_icf != 1){
		print "$speculate_icf\n";
		return;
	}
	open $ICF, $icf or die("cannot open file: $icf; $!");
	while(<$ICF>){
		if($_ =~ m/^\s*0x([0-9a-f]+)\t([^\t]+)\t0x([0-9a-f]+)$/){
			my $src_addr=$1;
			my $src_insn=$2;
			my $target_addr=$3;
			if($src_insn =~ m/^ret/){
				if(not defined $ret_target{$src_addr}){
					my %ret_instance = ();
					#$ret_instance{$target_addr} = 1;
					$ret_target{$src_addr} = {%ret_instance};
				}
				$r = $ret_target{$src_addr};
				if(not defined $r->{$target_addr}){
					$r->{$target_addr} = 1;	
				}else{
					$r->{$target_addr} = $r->{$target_addr}+1;	
				}
					#say Dumper(%$a);
				$record = $record + 1;
			}
		}
	}
	close($ICF);
	print "$record raw itarget records have been read\n";
	print "now start to write summary info into icf_final.out\n";

	open(my $ICFF,'>'."./icf_final.out") || die("cannot open file icf_final.out for writing. $!\n");
	while ( (my $isrc, my $itargets) = each %ret_target ){
		print "src address: $isrc\tdst hash: $itargets\n";
		while((my $itarget, my $num) = each %$itargets){
			print $ICFF "$num\t$isrc\tret\t$itarget\n";
		}
	}
	close($ICFF);
}

sub read_icf_check {
	my $f1 = "./icf_final.out";
	my $f2 = "./icf.out";
	print "this pass will accumulate indirect cf targets\n";	
	if($speculate_icf != 1){
		print "$speculate_icf\n";
		return;
	}
	if( -e $f1){
		print "$f1 exists, read it instead\n";
		read_all_icf();
	}elsif( -e $f2){
		print "$f2 exists, read this raw data\n";
		read_all_icf_v2();
	}else{
		print "no indirect control flow target info found\n";
	}
}
#====================================================
#analyse icf target related functions
sub analyze_icf_target {
	my $gbinname = $_[0];
	#cfi_analyze_pattern(1,"BACKWARD","80493e0", \@a);
	system("rm -f ./icf_target_addr");
	system("rm -f ./ret_target_addr");
	system("rm -f ./icf_target_addr_invalid");
	
	%icf_target = ();

	open($hICFT,'>'."./icf_target_addr") || die("can't open icf_target_addr file: $!");
	$hICFT_opened = 1;

	open($hRET,'>'."./ret_target_addr") || die("can't open ret_target_addr file: $!");
	$hRET_opened = 1;

	open($hICFTi,'>'."./icf_target_addr_invalid");
	if( !$hICFi){
		print("can't open icf_target_addr_invalid file: $!");
		$hICFTi_opened = 0;
	}else{
		$hICFTi_opened = 1;
	}

	if($elf_type eq "EXEC"){
		analyze_icf_target_exe();
	}elsif($elf_type eq "DYN"){
		analyze_icf_target_pic();
		if(@insn_array < 23000000){
		#currently, analyzer cannot handle library larger than 
		#two million instrutions, due to insufficient memory
			#cfi_init_analyzer("ana_log", $gbinname);
		}
	}
	#adding the 1st instruction address into hICFT
	#because the 1st instruction is probably the entry point
	print $hICFT "\n$insn_array[0][ORIG_POS]\n";
	print $hICFT "\n$insn_array[@insn_array - 1][ORIG_POS]\n";
	

	#now we are analyzing the landing pad addresses for exception handling
	$cmd = "./get_eh_icf_address.pl append $gbinname icf_target_addr";
	system($cmd);
	$cmd = "./get_eh_icf_address.pl append $gbinname ret_target_addr";
	system($cmd);

}
sub analyze_icf_target_pic_special_wrapper {
	my $dump_asm = $_[0];
	my $gbinname = $_[1];
	my $pid = fork();
	if($pid){
		if (waitpid($pid, 0) > 0){
			my ($rc, $sig, $core) = ($? >> 8, $? & 127, $? & 128);
			print "child $pid: returned value: $rc\n";
		}else{
			print "child $pid... um... disappeared...\n";
		}
	}else{
		disasm_insn($dump_asm,$gbinname);
		analyze_icf_target_pic_special($gbinname);
		dump_dcf_target();
		exit(0);
	}
}

sub analyze_icf_target_pic_special {
	my $gbinname = $_[0];
	my $size = @insn_array;
	my @match_insn;
	if(@insn_array > 73000000){
	#currently, analyzer cannot handle library larger than 
	#two million instrutions, due to insufficient memory
		#cfi_init_analyzer("ana_log", $gbinname);
		return;
	}
	my $anyreg ='\%eax|'.
	'\%ebx|'.
	'\%ecx|'.
	'\%edx|'.
	'\%esi|'.
	'\%edi|'.
	'\%esp|'.
	'\%ebp';

	my $cnt_p1 = 0;	
	my $cnt_p2 = 0;		
	my $cnt_p3 = 0;		
	my $cnt_p4 = 0;		
	my $cnt_no_interest = 0;
	my $cnt_unknown = 0;
	my %augument_data_p1 = ();
	my %augument_data_p2 = ();
	my %augument_data_p3 = ();
	my %augument_data_p4 = ();
	my %augument_data_p5 = ();
	my %augument_data_p6 = ();
	my %augument_data_p7 = ();
	my $window = 64;
	my @p1_distance = ( $window, $window);
	my @p2_distance = ( $window, 1, $window);
	my @p3_distance = ( $window, $window);
	my @p4_distance = ( $window, 16);
	my @p5_distance = ( $window, $window, 1);
	my @p6_distance = ( 1);
	my @p7_distance = ( 5, $window);
	$augument_data_p1{"distance"} =\@p1_distance;
	$augument_data_p2{"distance"} =\@p2_distance;
	$augument_data_p3{"distance"} =\@p3_distance;
	$augument_data_p4{"distance"} =\@p4_distance;
	$augument_data_p5{"distance"} =\@p5_distance;
	$augument_data_p6{"distance"} =\@p6_distance;
	$augument_data_p7{"distance"} =\@p7_distance;

	%handled_icf = ();
	%handled_p4_region = (); #key: start, value: end
	print "1st pass, handling pattern 1 & 2\n";
	for my $x (0 .. $size -1) {
		if($insn_array[$x][INSN_STR] =~ m/^\s*jmp[l]*\s*\*/){
			if($insn_array[$x][INSN_STR] =~ m/^\s*jmp[l]*\s*\*(%[a-z]+)\s*$/){
				my $gpr = $1;
				my @p1 = ('add[l]*\s*%(ebx|ecx),'.$gpr.'\s*$','mov[l]*\s*-0x([0-9a-f]+)\((%ebx|ecx),%[a-z]+,[1248]\),'.$gpr);
				my @p2 = ('add[l]*\s*\('.$gpr.',%[a-z]+,[1248]\),'.$gpr ,'add[l]*\s*\$0x([0-9a-f]+),'.$gpr, 'call');
				my @p5 = ('lea 0x[0-9a-f]+\('.$gpr.','.$anyreg.',[1248]\),'.$gpr, 'pop\s*'.$anyreg, 'call');
				my @p6 = ('call');
				print "non-excetional case for indirect jump\n";
				@match_insn = ();
				if(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p1, \@match_insn, \%augument_data_p1) == 1){
					$cnt_p1 += 1;
					print "pattern 1 matched at $insn_array[$x][ORIG_POS]\n";
					$handled_icf{$insn_array[$x][ORIG_POS]} = 1;
					#no need to do analysis here, since all these targets can be handled by analyze_icf_target_pic()
				}elsif(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p2, \@match_insn, \%augument_data_p2) == 1){
					$cnt_p2 += 1;
					print "pattern 2 matched at $insn_array[$x][ORIG_POS]\n";
					if($match_insn[1][INSN_STR] =~ m/$p2[1]/){
						my $off = $1;
						my $base_addr = $match_insn[1][ORIG_POS];
						my $index_addr = hex($base_addr) + hex($off);
						$index_addr = sprintf("%x", $index_addr);
						extract_icf_tgt($gbinname, ".rodata", "BASE_INDEX", $index_addr,
								$index_addr, $insn_array[$x][ORIG_POS]);
						$handled_icf{$insn_array[$x][ORIG_POS]} = 1;
					}else{
						print "exception: fail to match insn 2 when pattern 1 get matched\n";
						translation_abort();
					}
					
					$handled_icf{$insn_array[$x][ORIG_POS]} = 1;

				}elsif(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p5, \@match_insn, \%augument_data_p5) == 1){
					my $code_base = 0;
					my $stride = 0;
					my $offset = 0;
					my $code_base_reg = "";
					if($match_insn[0][INSN_STR] =~ m/lea\s*0x([0-9a-f]+)\(($anyreg),$gpr,([0-9])\),$gpr/){
						$offset = hex($1);
						$stride = hex($3);
						$code_base_reg = $2;
					}else{ next;}
					if($match_insn[1][INSN_STR] =~ m/pop\s*$code_base_reg/){
					}else {next;}
					if(($match_insn[2][INSN_STR] =~ m/call\s*0x([0-9a-f]+)/) or
					$match_insn[2][INSN_STR] =~ m/call\s*([0-9a-f]+)/){
						my $t = $1;
						if($t eq $match_insn[1][ORIG_POS]){
							my $_i = $pos_mapping{$match_insn[2][ORIG_POS]};
							$_i = $_i +1;
							$code_base = hex($insn_array[$_i][ORIG_POS]);
							$code_base = $code_base + $offset;
							print "last insn matched: $match_insn[2][INSN_STR]\n";
						}else{next;}
					}
					print "match pattern 5!!!\n";
					#starting to compute code addresses
					my $code_base_str = sprintf("%x", $code_base);
					if(defined $pos_mapping{$code_base_str}){
						print "code address valid: $code_base_str\n";
						print $hICFT "$code_base_str\n";
						add_icf_target($code_base_str, $insn_array[$x][ORIG_POS]);
					}
					my $current_addr = $code_base+$stride;
					my $current_addr_str = sprintf("%x",$current_addr);
					while(defined $pos_mapping{$current_addr_str}){
						print "code address valid: $current_addr_str\n";
						print $hICFT "$current_addr_str\n";
						add_icf_target($current_addr_str, $insn_array[$x][ORIG_POS]);
						$current_addr = $current_addr+$stride;
						$current_addr_str = sprintf("%x",$current_addr);
					}
					#translation_abort();
					$handled_icf{$insn_array[$x][ORIG_POS]} = 1;

				}elsif(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p6, \@match_insn, \%augument_data_p6) == 1){
					my $num = add_icf_targets_until_ret($x+1);
					print "$num icf targets has been added\n";
					print "match pattern 6\n";
					$handled_icf{$insn_array[$x][ORIG_POS]} = 1;

				}else{
					#print "fail to find pattern at $insn_array[$x][ORIG_POS]\n";
				}
			
			}elsif($insn_array[$x][INSN_STR] =~ m/^\s*jmp[l]*\s*\*0x[0-9a-f]+\(%ebx\)$/){
				#print "not interesting indirect jump type\n";
				$cnt_no_interest +=1;

				$handled_icf{$insn_array[$x][ORIG_POS]} = 1;
			}else{
				$cnt_unknown += 1;
				print "unknown indirect jump type at $insn_array[$x][ORIG_POS]\n";
			}
		}
	}
	print "2nd pass, handling pattern 3\n";
	for my $x (0 .. $size -1) {
		if($insn_array[$x][INSN_STR] =~ m/^\s*jmp[l]*\s*\*/ and (not defined $handled_icf{$insn_array[$x][ORIG_POS]})){
			if($insn_array[$x][INSN_STR] =~ m/^\s*jmp[l]*\s*\*(%[a-z]+)\s*$/){
				my $gpr = $1;
				my @p3 = ('add[l]*\s*\(%ebx,%[a-z]+,[1248]\),%ebx' ,'add[l]*\s*\$0x([0-9a-f]+),%ebx');
				my @p4 = ('add[l]*\s*-0x[0-9a-f]+\((%ebp|%esp)\),'.$gpr ,'mov[l]*\s*-0x[0-9a-f]+\(%ebx,%[a-z]+,[1248]\),'.$gpr);
				my @p7 = ('pop\s*'.$gpr, 'call');
				if(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p3, \@match_insn, \%augument_data_p3) == 1){
					$cnt_p3 += 1;
					print "pattern 3 matched at $insn_array[$x][ORIG_POS]\n";
					if(defined $icf_target{$match_insn[1][ORIG_POS]}){
						my $src_addr = $icf_target{$match_insn[1][ORIG_POS]};
						my $analysis_done = 0;
						# in version 95 (svn) $src_addr could be any addr in the region (between two exported symbols)
						foreach my $src_addr (keys(%$src_addr)){
							my $idx = $pos_mapping{$src_addr};
							if($insn_array[$idx][INSN_STR] =~ m/jmp[l]*\s*\*%ebx/){
								#only now can we make sure that %ebx is the address of insn_match[1][ORIG_POS] !
								if($analysis_done == 0){
									#do analysis only once
									if($match_insn[1][INSN_STR] =~ m/$p3[1]/){
										my $off = hex($1);
										my $index_addr =sprintf("%x", hex($match_insn[1][ORIG_POS])+$off);
										extract_icf_tgt($gbinname, ".rodata", "BASE_INDEX", $index_addr,
											$index_addr, $insn_array[$x][ORIG_POS]);
										$analysis_done = 1;
									}else{
										print "exception: fail to match insn 2 when pattern 3 get matched\n";
										translation_abort();
									}
								}
							}else{
								
								print "exception case: pattern 3 not targeted by jmp *%ebx\n";

							}
						}
						#print "normal case: pattern 3 is targeted by an address\n";
					}else{
						print "exception case: pattern 3 not targeted by any address\n";
					}
				}elsif(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p4, \@match_insn, \%augument_data_p4) == 1){
					print "match pattern 4 at :$insn_array[$x][ORIG_POS]\n";
					$cnt_p4 += 1;
					my ($start_addr, $end_addr) = cfi_query_func_region($insn_array[$x][ORIG_POS]);
					if(defined $handled_p4_region{$start_addr}){
						next;
					}
					$handled_p4_region{$start_addr} = $end_addr;
					print "pattern 4: start addr: $start_addr\tend addr: $end_addr\n";
					my %code_addr = cfi_query_taken_code_addr($start_addr, $end_addr);
					my %index_addr = cfi_query_taken_index_addr($start_addr, $end_addr);
					say Dumper($code_addr);
					say Dumper($index_addr);
					#print "pattern 4: code addr: $code_addr[0], $code_addr[1]\n";
					foreach my $c_addr ( keys(%code_addr) ) {
						print "code addr: $c_addr\n";
					}
					foreach my $i_addr ( keys(%index_addr) ) {
						print "index addr: $i_addr\n";
					}

					foreach my $c (keys(%code_addr)){
						foreach my $i (keys(%index_addr)){
							extract_icf_tgt($gbinname, ".rodata", "BASE_INDEX", $c,
								$i, $insn_array[$x][ORIG_POS]);
						}
					}

				}elsif(cfi_analyze_pattern(1,"BACKWORD", $insn_array[$x][ORIG_POS], \@p7, \@match_insn, \%augument_data_p7) == 1){
					if(($match_insn[1][INSN_STR] =~ m/call\s*0x([0-9a-f]+)/) or
						$match_insn[1][INSN_STR] =~ m/call\s*([0-9a-f]+)/){
						my $t = $1;
						if($t ne $match_insn[0][ORIG_POS]){next;}
					}
					my $num = add_icf_targets_until_ret($x+1);
					print "$num icf targets has been added\n";
					print "match pattern 7\n";
					$handled_icf{$insn_array[$x][ORIG_POS]} = 1;
				}else{

					print "fail to find pattern at $insn_array[$x][ORIG_POS]\n";
				}
			}
		}
	}

	print "pattern1 match times; $cnt_p1\n";
	print "pattern2 match times; $cnt_p2\n";
	print "pattern3 match times; $cnt_p3\n";
	print "pattern4 match times; $cnt_p4\n";
	print "uninteresting ijmp: $cnt_no_interest\n";


}
sub add_icf_targets_until_ret {
	my $start = $_[0];
	my $idx = $_[0];
	my $end = @insn_array;
	while($idx < $end){
		print "adding $insn_array[$idx][ORIG_POS] into icf targets\n";
		print $hICFT $insn_array[$idx][ORIG_POS]."\n";
		add_icf_target($insn_array[$idx][ORIG_POS], "");
		$idx = $idx+1;
		if($insn_array[$idx][INSN_STR] =~ m/^ret/){ last;}
	}
	return $idx - $start;
}

sub cfi_analyze_pattern {
	my $version = $_[0];
	my $direction = $_[1]; 	
	my $start_addr = $_[2];
	my $pattern_array = $_[3];
	my $match_insn = $_[4];
	my $aug_data = $_[5];
	my $distance = \@{$aug_data->{"distance"}};
	#print "1st element: $$pattern_array[0]\n";
	#print "2nd element: $$pattern_array[1]\n";
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
		translation_abort();
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
		translation_abort();
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



sub add_icf_target {
	my $target =$_[0];
	my $src = $_[1];
	if(defined $pos_mapping{$target}){
		if( not defined $icf_target{$target}){
			%icf_tgt_instance = ();
			if($src ne ""){
				$icf_tgt_instance{$src} = 1;
			}
			$icf_target{$target} = {%icf_tgt_instance};
		}else{
			$tgt_instance = $icf_target{$target};
			if($src eq ""){
				return;
			}
			if(not defined $tgt_instance{$src}){
				$tgt_instance{$src} = 1;
			}else{
				$tgt_instance{$src} += 1;
			}
		}
	}
}

sub speculate_icf_tgt {
	my $base_addr = $_[0];
	my $call_site = $_[1];
	my $gbinname = $global_binname;
	print "come to speculate_icf_tgt, base addr: $base_addr\n";
	my $base_offset = convert_vma_to_offset($base_addr, $gbinname);
	my $cur_off = $base_offset;
	open my $binfh, '<',$gbinname or die("cannot open file: $gbinname, $!\n");
	binmode($binfh);
	seek $binfh, $base_offset, 0;
	my $value = 0;
	if(read($binfh, $value, 4) != 4){
		die("error reading ELF file when speculating icf targets in rodata \n");
	}
	my $off = unpack('i',$value);
	my $addr = sprintf("%x",hex($base_addr) + $off);
	while(defined $pos_mapping{$addr}){
		add_icf_target($addr, "");
		print  "special itarget:\n$addr\n";
		print $hICFT "$call_site to special itarget:\n$addr\n";
		if(read($binfh, $value, 4) != 4){
			die("error reading ELF file when speculating icf targets in rodata \n");
		}
		$off = unpack('i',$value);
		$addr = sprintf("%x",hex($base_addr) + $off);
	}
	close($binfh);
	
}

sub extract_icf_tgt {
	my $gbinname = $_[0];
	my $secname = $_[1];
	my $mode = $_[2]; #mode = "GOTOFF" | "GOT"|"BASE_INDEX"
	my $tb_code_base;#address of code address base
	my $tp_data_base;#address that stores index
	my $call_site;
	if($mode eq "BASE_INDEX"){
		$secname = ".rodata"; 
		$tb_code_base = hex($_[3]);
		$tp_data_base = $_[4];
		$call_site = $_[5];
	}
	my $got_addr = hex(get_got_address($gbinname));
	my $section_offset = hex(get_section_info($gbinname, $secname, "offset"));
	my $section_size = hex(get_section_info($gbinname, $secname, "size"));
	if($section_size == 0 and $section_offset == 0){
		print "section: $secname does not exist\n";
		return;
	}
	my $last_offset = $section_offset + $section_size - 3;
	my $cur_off = $section_offset;
	if($mode eq "BASE_INDEX"){
		$cur_off = convert_vma_to_offset($tp_data_base, $gbinname); 
	}
	print "extract_icf_target: now reading raw binary file\n";
	open my $binfh, '<',$gbinname or die("cannot open file: $gbinname, $!\n");
	binmode($binfh);
	seek $binfh, $cur_off, 0;
	while($cur_off < $last_offset){
		my $value = 0;
		if(read($binfh, $value, 4) != 4){
			die("error reading ELF file when reading section\n");
		}
		if($mode eq "GOTOFF"){
			my $off = unpack('i',$value);#here it should be a negative integer (signed int);
			my $addr = $off + $got_addr;
			$addr = sprintf("%x", $addr);
			if(defined $pos_mapping{$addr}){
				print $hICFT "$addr\n";
				add_icf_target($addr, "");
			}
		}elsif($mode eq "GOT"){
			my $addr = unpack('i',$value);
			$addr = sprintf("%x", $addr);
			if(defined $pos_mapping{$addr}){
				print $hICFT "$addr\n";
				add_icf_target($addr, "");
			}
		}elsif($mode eq "BASE_INDEX"){
			my $off = unpack('i',$value);
			my $addr = $off + $tb_code_base;
			$addr = sprintf("%x", $addr);
			if(defined $pos_mapping{$addr}){
				print $hICFT "base_index callsite: $call_site\n";
				print $hICFT "$addr\n";
				add_icf_target($addr, $call_site);
			}
		}
		$cur_off += 1;
		seek $binfh, -3, 1;# move backward by 3 bytes
	}
	close($binfh);
}

sub check_get_pc_thunk {
	my $_target = $_[0];
	my $_cur_index = $_[1];
	if(not defined $_target){
		return 0;
	}
	my $_index = $pos_mapping{$_target};
	if(not defined $_index){
		return 0;
	}	
	if(defined $pos_get_pc_thunk[$_index]){
		if($pos_get_pc_thunk[$_index] == 1){
			return 1;
		}elsif($pos_get_pc_thunk[$_index] == 2){
			return 0;
		}
	}

	my $_insn = $insn_array[$_index][INSN_STR];
	my $bytes = $insn_array[$_index][RAW_BYTES];
	my $next_insn = $insn_array[$_index+1][INSN_STR];
	my $next_bytes = $insn_array[$_index+1][RAW_BYTES];
	if(($bytes =~ m/^\s*8b\s1c\s24\s*$/) or
		#mov    (%esp),%ebx 8b 1c 24
		($bytes =~ m/^\s*8b\s0c\s24\s*$/) or
		#mov    (%esp),%ecx
		($bytes =~ m/^\s*8b\s14\s24\s*$/)){
		#mov    (%esp),%edx
		if( $next_bytes =~ m/^\s*c3\s*$/){
			#ret     c3
			#print "call target:".$_insn." ".$bytes."\n\t".$next_insn." ".$next_bytes."\n";
			#$pos_get_pc_thunk[$_index] = 1;
			return 1;
		}else{
			#$pos_get_pc_thunk[$_index] = 2;
			return 0;
		}
	}else{
		if(($_insn =~ m/^mov\s*\(%esp\),($gpr)\s*/) and ($next_bytes =~ m/^\s*c3\s*$/)){
		#get_pc_thunk without using ebx or ecx
			print "get_pc_thunk without using ebx, ecx or edx, abort\n";
			print $insn_array[$_index][ORIG_POS].":\n";
			print $_insn."\n";
			print $insn_array[$_index+1][INSN_STR]."\n";
			#translation_abort();

		}else{
			#print "call target:".$insn." ".$bytes."\n";
			#$pos_get_pc_thunk[$_index] = 2;
			return 0;
		}
	}
}

sub check_call_pop_trampoline {	
	my $_cur_index = -1;
	my $_target = "-1";

	$_cur_index = $_[0];
	$_target = $_[1];
	if($_cur_index == -1){
		return 0;
	}
	if($_target eq "-1"){
		return 0;
	}
	
	if(defined $pos_mapping{$_target} and $pos_mapping{$_target} == ($_cur_index + 1)){
	#probably a call-pop trampoline
		print $_target.":\tprobably a call-pop tram\n";	
		if((defined $pos_call_pop{$_target}) and ($pos_call_pop{$_target} == 1)){
			return 1;
		}
		$_target_index = $_cur_index + 1;
		print "instruction: ".$insn_array[$_target_index][INSN_STR]."\n";
		if($insn_array[$_target_index][INSN_STR] =~ m/^\s*(pop|popl)\s*\%(ebx|ecx|edx)$/){
			#now, for sure it is
			print $_target.":\tfor sure,it is a call-pop tram\n";
			$pos_call_pop{$_target} = 1;
			return 1;
		}elsif($insn_array[$_target_index][INSN_STR] =~ m/^\s*(pop|popl)\s*($gpr)$/){
			print "find a call-pop trampoline without using ebx or ecx, abort\n";
			#translation_abort();
			$pos_call_pop{$_target} = 1;
			return 1;
		}

	}elsif(defined $pos_mapping{$_target} and $insn_array[$pos_mapping{$_target}][INSN_STR] =~ m/^\s*(pop|popl)\s*($gpr)$/){
		#this is another form of call-pop, between call and target, probably there is
		#a jump table.
		print CALLPOP "find a call-pop at pos: $insn_array[$_cur_index][ORIG_POS]\n";
		if(fix_jmp_table_case_1($_cur_index) == 1){
			print "fix a type-1 jump table\n";
		}
	}
	return 0;
}
sub fix_jmp_table_case_1 {
	my $index = $_[0];
	#not implemented yet
	return 0;
}

sub analyze_icf_target_pic {
	my $size = @insn_array;
	my $count = 0;
	my $ret_count = 0;
	my $gbinname = $global_binname;
	my $got_addr = hex(get_got_address($gbinname));
	print "got address : ". get_got_address($gbinname) . "\n";
	#check out next of call inside disassembly
	print $hICFT "return address:\n";
	print $hRET "return address:\n";
	for my $x (0 .. $size-1){
		#print "$insn_array[$x][INSN_STR]\n";
		if($insn_array[$x][INSN_STR] =~ m/^call[l]*\s+/){
			#add return address into icf_target
			if($insn_array[$x][INSN_STR] =~ m/^call[l]*\s+([0-9a-f]+)/){
				my $t = $1;
				if(check_get_pc_thunk($t, $x) ==1){
					next;
				}elsif(check_call_pop_trampoline($x,$t) == 1){
					next;
				}
			}
			add_icf_target($insn_array[$x+1][ORIG_POS], "");
			$ret_count += 1;
			print $hICFT "$insn_array[$x+1][ORIG_POS]\n";
			print $hRET "$insn_array[$x+1][ORIG_POS]\n";
		}
	}
	#check out the constant in the form of GOT OFFSET
	print $hICFT "GOT offset addresses in assembly:\n";
	for my $x (0 .. $size-1){
		if($insn_array[$x][INSN_STR] =~ m/-0x([0-9a-fA-F]+)/){
			#print "$1\n";
			my $offset = hex($1);
			my $_addr = sprintf("%x",$got_addr - $offset);
			if(defined $pos_mapping{$_addr}){
				add_icf_target($_addr, "");
				print $hICFT "gotoff address:\n";
				print $hICFT "$_addr\n";
			}elsif(if_within_exec($_addr)){
				print $hICFTi "gotoff address:\n";
				print $hICFTi "$_addr\n";
			}
		}
	}

	print $hICFT "GOT offset addresses in rodata:\n";
	print $hICFT "jmptable-gotoff address:\n";
	extract_icf_tgt($gbinname, ".rodata", "GOTOFF");
	
	print $hICFT "Relocatable addresses in metadata:\n";
	print $hICFT "including tdata ctor dtor init_array libc_* data.rel.ro dynamic got .got.plt .data:\n";

	open my $binfh, '<',$gbinname or die("cannot open file: $gbinname, $!\n");

	my $cmd = "readelf -r $gbinname| grep R_386_ |sort -k1|cut -f1 -d \' \'|";
	$cmd = get_filename_from_cmd($cmd);
	my $first_reloc = 0x7fffffff;
	my $first_reloc_str = "";
	my $last_reloc = 0;
	my $last_reloc_str = "";
	open(my $hREL, $cmd) or die("cannot read cmd ".$cmd.": $!");
	while(<$hREL>){
		if($_ =~ m/^([0-9a-f]+)$/){
			my $addr_str = $1;
			my $addr = hex($addr_str);
			if($addr < $first_reloc ){
				$first_reloc = $addr;
				$first_reloc_str = $addr_str;
			}
			if($addr > $last_reloc ){
				$last_reloc = $addr;
				$last_reloc_str = $addr_str;
			}
		}
	}
	$first_reloc = convert_vma_to_offset($first_reloc_str, $gbinname);
	$last_reloc = convert_vma_to_offset($last_reloc_str, $gbinname);
	#print "last_reloc: $last_reloc_str\n";
	#printf "last_reloc: %x\n" , $last_reloc;
	#translation_abort();
	#$last_reloc =$last_reloc - 3;
	$cur_off = $first_reloc;
	seek $binfh, $cur_off, 0;
	while($cur_off <= $last_reloc){
		my $value = 0;
		if(read($binfh, $value, 4) != 4){
			die("error reading ELF file when reading metadata\n");
		}
		my $addr = unpack('V',$value);#here it should be a negative integer (signed int);
		$addr = sprintf("%x", $addr);
		if(defined $pos_mapping{$addr}){
			print $hICFT "pic absolute addresses taken:\n";
			print $hICFT "$addr\n";
			add_icf_target($addr, "");
		}elsif(if_within_exec($addr)){
			print $hICFTi "pic absolute addresses taken:\n";
			print $hICFTi "$addr\n";
		}

		$cur_off += 1;
		seek $binfh, -3, 1;# move backward by 3 bytes
	}
	close($binfh);

	print $hICFT "GOT offset addresses in dynsym:\n";
	print $hICFT "exported address:\n";
	if($enforce_plt ==0){
		extract_icf_tgt($gbinname, ".dynsym", "GOT");
	}

	print $hICFT "GOT offset addresses in symtab:\n";
	print $hICFT "exported address:\n";
	extract_icf_tgt($gbinname, ".symtab", "GOT");

	print $hICFT "GOT offset addresses in dynamic:\n";
	print $hICFT "exported address:\n";
	extract_icf_tgt($gbinname, ".dynamic", "GOT");

	my $entry_point = get_entry_addr($gbinname);
	print $hICFT "$entry_point\n";
}

sub analyze_icf_target_exe {
	my $size = @insn_array;
	my $count = 0;
	my $ret_count = 0;

	#check out constants inside disassembly
	for my $x (0 .. $size-1){
		#print "$insn_array[$x][INSN_STR]\n";
		if($insn_array[$x][INSN_STR] =~ m/^call[l]*\s+/){
			#add return address into icf_target

			print $hICFT "return address:\n";
			print $hRET "return address:\n";
			print $hICFT "$insn_array[$x+1][ORIG_POS]\n";
			print $hRET "$insn_array[$x+1][ORIG_POS]\n";

			add_icf_target($insn_array[$x+1][ORIG_POS], "");
			$ret_count += 1;
		}
		if($insn_array[$x][INSN_STR] =~ m/^[^\$]+\$0x([0-9a-fA-F]+).*$/){
			#print "$1\n";
			my $int = $1;
			if(defined $pos_mapping{$int}){
				print $hICFT "absolute address:\n";
				print $hICFT "$int\n";
				add_icf_target($int, "");
			}
		}
	}
	#check out the constant in the form of GOT OFFSET
	print $hICFT "GOT offset addresses in assembly:\n";
	for my $x (0 .. $size-1){
		if($insn_array[$x][INSN_STR] =~ m/-0x([0-9a-fA-F]+)/){
			#print "$1\n";
			my $offset = hex($1);
			my $_addr = sprintf("%x",hex($got_addr) - $offset);
			if(defined $pos_mapping{$_addr}){	
				print $hICFT "gotoff address:\n";
				print $hICFT "$_addr\n";
				add_icf_target($_addr, "");
			}
		}
	}

	#check out constants inside metadata
	$count = keys(%icf_target);
	print "ret_count: $ret_count\n";
	print "count:$count\n";
	print "now reading raw binary file\n";
	print $hICFT "all absolute addresses taken:\n";
	open my $binfh, '<',$global_binname or die("cannot open file: $global_binname, $!\n");
	binmode($binfh);
	my $value = 0;
	while(read($binfh, $value, 4) == 4){
		my $addr = sprintf("%x",unpack('I',$value));
		add_icf_target($addr, "");
		seek $binfh, -3, 1;
		if(defined $pos_mapping{$addr}){
			print $hICFT "$addr\n";
		}
	}

	print $hICFT "jmptable-gotoff address:\n";
	extract_icf_tgt($global_binname, ".rodata", "GOTOFF");
	print $hICFT "jmptable-abs address:\n";
	extract_icf_tgt($global_binname, ".rodata", "GOT");
	print $hICFT "exported address:\n";
	extract_icf_tgt($global_binname, ".dynsym", "GOT");
	#extract_icf_tgt($global_binname, ".ctors", "GOT");
	#extract_icf_tgt($global_binname, ".dtors", "GOT");
	#extract_icf_tgt($global_binname, ".fini_array", "GOT");
	#extract_icf_tgt($global_binname, ".init_array", "GOT");

	#extract_icf_tgt($global_binname, ".jcr", "GOT");
	extract_icf_tgt($global_binname, ".dynamic", "GOT");

	print $hICFT "whole address:\n";
	$count = keys(%icf_target);
	print "count:$count\n";	
	foreach  my $addr ( keys(%icf_target) ){
		print $hICFT "$addr\n";
	}
}

sub get_elf_exec_range {
	my $binname = shift;
	my $exec_begin=0x7fffffff;
	my $exec_end=0;
	my $exec_end_size = 0;
	$cmd='readelf -W -S ' .$binname." | sed 's/\\[\\s*//g'|grep ' AX '| awk '{print \$4 \" \" \$5 \" \" \$6}'|";
	$cmd = get_filename_from_cmd($cmd);
	open(my $BIN , $cmd) or die("cannot execute: $cmd; $!\n");
	while(<$BIN>){
		if($_ =~ m/(\S+)\s+(\S+)\s+(\S+)/){
			my $addr = hex($1);
			my $size = hex($3);
			if($addr < $exec_begin){
				$exec_begin = $addr;
			}
			if($addr > $exec_end){
				$exec_end = $addr;
				$exec_end_size = $size;
			}
		}
	}
	$exec_end += $exec_end_size;
	return ($exec_begin, $exec_end);
}
sub get_entry_addr {
	my $binname = $_[0];
	my $cmd = "readelf -h ".$binname." |";
	$cmd = get_filename_from_cmd($cmd);
	open(BIN, $cmd) or die("cannot open file". $binname." $!");
	while(<BIN>){
		if($_ =~ m/^\s*Entry point address:\s*0x([^\n]+)$/){
			$_entry_begin = $1;
			return $_entry_begin; 
		}	
	}
}

sub if_within_exec {
	my $addr = shift;
	#print "addr:$addr\n";
	if((hex($addr) >= $exec_begin) and (hex($addr) <$exec_end)){
		return 1;	
	}else{
		return 0;
	}
}
sub fix_disasm_using_invalid_target {
	my $binname = shift;
	my $asmdump = shift;
	my $pwd = getcwd();
	open(my $BIN, '<./icf_target_addr_invalid');
	if(!$BIN){
		print "no invalid target lies within code region\n"; 
		return;
	}
	while(<$BIN>){
		#print $_;
		if($_ =~ m/^\s*([0-9a-f]+)\s*$/){
			my $addr = $1;
			$addr =~ s/^0+//;
			#print $addr."\n";
			_fix_free_branch($addr, $binname);
		}
	}
	#$cmd = "objdump -w -d $binname >$asmdump";
	#system($cmd);

}
sub dump_dcf_target {
	if($dump_direct_cf_target != 1){
		return;
	}
	$dcf_file="./dcf_target_addr";
	open(my $DCF, ">".$dcf_file) or die("cannot open $dcf_file: $!\n");
	foreach my $x (keys(%target_addr)){
		print $DCF "$x\n";
	}
}
sub notify_analysis_done {
	system("touch analysis_done");
}

my $asmdump = shift(@ARGV);
my $binname = shift(@ARGV);
my $configfile = shift(@ARGV);
$global_binname = $binname;

load_config($configfile);
read_icf_check();
fix_disasm_issue($asmdump, $binname);
#analyze_icf_target_pic_special($global_binname);
analyze_icf_target_pic_special_wrapper($asmdump, $global_binname);
notify_analysis_done();
