#!/usr/bin/perl -w
package bin_translate;
use Switch;
use Fcntl;
use Data::Dumper;
use feature 'say';
use lib '..';
require Exporter;
@ISA = qw(Exporter);
#exported on default
@EXPORT = qw(	transform
		only_disasm
		sbt_insert_before_insn 
		sbt_insert_after_insn 
		sbt_insert_before_insn_v2
		sbt_insert_after_insn_v2
		sbt_instrument_lookup
		sbt_instrument_indirect_call
		sbt_instrument_direct_call

		%insn_array_before
		%insn_array_after
		%icf_lookup_routine_name

		@insn_array
		%pos_mapping

		ORIG_POS
		INSN_STR
		RAW_BYTES
		INSTRU_FLAG
		BRANCH
		BRAN_TARGET
		CALL_FLAG

		$B_IS_NON_CF
		$B_IS_DIRECT_CF
		$B_IS_RETURN
		$B_IS_INDIRECT_CALLJMP

		$C_INVALID
		$C_CALL
		$C_ICALL
		$C_IJMP_TEXT
		$C_IJMP_PLT

		$I_ORIGINAL
		$I_TRANSLATED
		$I_ADDED
		$I_NEVER_TOUCH

		$B_IS_NON_CF
		$B_IS_DIRECT_CF
		$B_IS_RETURN
		$B_IS_INDIRECT_CALLJMP

);

#exported when asked for
@EXPORT_OK = qw($client_routine
		$client_change_lookup_routine
		$client_hook_icf_instrumentation

		@direct_target_addr
		INSTRU_FLAG
		BRANCH
		BRAN_TARGET
		CALL_FLAG

	);

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

my $elf_type = ""; #EXEC ; DYN
my $bin_type = ""; #EXEC ; LIB
my $got_addr = "";
my $outputfile_fd;
my $testfile_fd;

my $after_branch_count = 0;

my $hICFT;#file handler for icf target
my $hICFT_opened = 0;
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
my $hijack_entry=0;
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

my $cf_opcode = 'jmp\s|ljmp\s|jmpl\s|call\s|calll\s|jb\s|jnae\s|jc\s|jbe\s|jna\s|jcxz\s|jecxz\s|jl\s|jnge\s|jle\s|jng\s|jnb\s|jae\s|jnc\s|jnbe\s|ja\s|jnl\s|jge\s|jnle\s|jg\s|jno\s|jnp\s|jpo\s|jns\s|jnz\s|jne\s|jo\s|jp\s|jpe\s|js\s|jz\s|je\s|loop\s';
my $cond_cf_opcode = 'jb\s|jnae\s|jc\s|jbe\s|jna\s|jcxz\s|jecxz\s|jl\s|jnge\s|jle\s|jng\s|jnb\s|jae\s|jnc\s|jnbe\s|ja\s|jnl\s|jge\s|jnle\s|jg\s|jno\s|jnp\s|jpo\s|jns\s|jnz\s|jne\s|jo\s|jp\s|jpe\s|js\s|jz\s|je\s|loop\s';

my $insn_addr = '0x[0-9a-fA-F]{1,8}|[0-9a-fA-F]{1,8}';

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

#=============================
#all exported data structures are defined below

#instru_flag options, static variables, should not be changed
our $I_ORIGINAL = 0;
our $I_TRANSLATED = 1;
our $I_ADDED = 2;
our $I_NEVER_TOUCH = 3;

# branch_flag options
our $B_IS_NON_CF = "0";
our $B_IS_DIRECT_CF = "1";
our $B_IS_RETURN = "2";
our $B_IS_INDIRECT_CALLJMP = "3";

# call_flag options, only valid when branch_flag is "1" or "3"
our $C_INVALID = 0;
our $C_CALL = 1;
our $C_ICALL = 2;
our $C_IJMP_TEXT = 3;
our $C_IJMP_PLT = 4;

our @insn_array;
our %pos_mapping = ();
our @direct_target_addr = ();
our $client_routine = "";
our $client_change_lookup_routine = "";
our $client_hook_icf_instrumentation = "";
#=============================
#all global data structures are defined below
my %icf_target = (); # target address ==> src_address_table (src_address ==> 1);  
my @pos_get_pc_thunk;
my %pos_call_pop = ();

my @free_targets = ();
my @after_branch = ();

my %reverse_target = ();#currently only support one reverse target
my %speculate_jmp_table = ();#record symbols of a speculated jmp table
my $speculate_table_size = 0x1000;
# hash tables for icf targets information
# used when speculate_icf=1
# the info comes from dynamic translation using PIN
%ret_target = ();
%jmp_target = ();
%call_target = ();

our %insn_array_before = ();
our %insn_array_after = ();

# addr <=> name
our %icf_lookup_routine_name = ();
#=============================
#all routines/functions are defined below

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
	exit(1);
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

my $__MYRODATA; # file descriptor pointing to rodata translation assembly
my $__REST_JMP; # file descriptor pointing to unhandled jmp tables
my $__rodata_opened = 0;
my $__BIN; # file descriptor pointing to binary file
my $__bin_opened = 0;
my $rodata_addr;
my $rodata_offset;
my $rodata_size;
sub instrument_jmp_table {
	my $icf = $_[0];
	my $itarget = $_[1];
	my $idx = $_[2];
	my $cur_insn ="";
	if($elf_type ne "EXEC"){
		return "";
	}
	if($__rodata_opened == 0){
		print "openning a file\n";
		open($__MYRODATA,'>'."./myrodata.s") || die("can't open myrodata file: $!");
		print $__MYRODATA ".p2align 4\n";
		$__rodata_opened = 1;	
		open($__REST_JMP,'>'."./unhandled_table_jmp.s") || die("can't open unhandled_table_jmp.s: $!");
	}

	if($translate_jmp_table == 0){
		return "";
	}

	if($__bin_opened == 0){
		print "openning a file\n";
		open($__BIN,'<'.$global_binname) || die("can't open binary file: $!");	
		binmode($__BIN);
		$__bin_opened = 1;
		$rodata_addr = get_section_info($global_binname, ".rodata","addr");
		$rodata_offset = get_section_info($global_binname, ".rodata","offset");
		$rodata_size = get_section_info($global_binname, ".rodata","size");
		#print "rodata_address: $rodata_addr\n";
		#seek $binfh, $magic_offset, 0;

	}
	if($itarget =~ m/^\s*0x([0-9a-f]+)\(,($gpr),([1248])\)\s*$/){
		print "this is a jmp table icf: $icf $itarget\n";
		print "prev insn:$insn_array[$idx-1][INSN_STR]\n";
		my $base_addr = $1;
		my $reg = $2;
		my $stride = $3;

		my $bound = backward_jmp_table_boundy_analysis($idx,$reg);	
		print $__MYRODATA "jmp_table_$insn_array[$idx][ORIG_POS]:\n";
		my $offset = hex($base_addr) - hex($rodata_addr) + hex($rodata_offset);
		my $default_target = "\nijmp_next_$insn_array[$idx][ORIG_POS]";
		$cur_insn =  generate_jmp_table_content($offset,$bound,$default_target, $__MYRODATA, $__BIN, $reg, $stride, $idx, $base_addr);
		if($bound != 0){	
		}else{
			print "unhandled table jmp\n";
			print $__REST_JMP "$insn_array[$idx][INSN_STR]\n";
		}
		return $cur_insn;
			
	}
	return "";

}
sub discover_cmp_nearby {
	my $cur = shift;
	my $src_operand = shift;
	my $bound = 0;
	my $neighbour = 0;
	while($neighbour < 5){
		#searching cmp insn nearby
		if($insn_array[$cur-$neighbour][INSN_STR] =~ m/^\s*cmp.\s*\$0x([0-9a-f]+),($src_operand)\s*$/){
			$bound = hex($1)+1;
			last;
		}
		$neighbour = $neighbour +1;
	}
	return $bound;
}

sub discover_mov_nearby {
	my $cur = shift;
	my $reg = shift;
	my $src_operand = $reg;
	my $neighbour = 1;
	while($neighbour < 3){
		#searching cmp insn nearby
		if($insn_array[$cur-$neighbour][INSN_STR] =~ m/^\s*(cmp|ja|jae|jbe)/){
			return ($cur, $src_operand);
		}
		if($insn_array[$cur-$neighbour][INSN_STR] =~ m/^\s*mov[zbwl]{0,3}\s*([^,]+),($reg)\s*$/ or
			$insn_array[$cur-$neighbour][INSN_STR] =~ m/^\s*mov[zbwl]{0,3}\s*(\([^\)]+\)),($reg)\s*$/){
			$src_operand = $1;
			$cur = $cur - $neighbour;
			print "find mov: $insn_array[$cur][INSN_STR] at $insn_array[$cur][ORIG_POS]\n";	
			$src_operand =~ s/\(/\\\(/; #escape brackets to avoid being regarded as regex
			$src_operand =~ s/\)/\\\)/;
			return ($cur, $src_operand);
		}
		$neighbour = $neighbour +1;
	}
	return ($cur, $src_operand);
}
sub backward_jmp_table_boundy_analysis {
	my $idx = shift;
	my $reg = shift;
	my $bound = 0;
	#begin pattern matching
	my $matched = 0;
	if($matched == 0 and $insn_array[$idx-1][INSN_STR] =~ m/^\s*ja/ and $insn_array[$idx-2][INSN_STR] =~ m/^\s*cmp[l]*/){
		print "trying to match pattern 1 prefix!\n";
		



		my $cur = $idx -1;
		$src_operand = $reg;
		if($insn_array[$cur][INSN_STR] =~ m/^\s*ja/){
			$bound = discover_cmp_nearby($cur, $src_operand);
			if($bound != 0){
				print "match pattern 1-1! $insn_array[$idx][ORIG_POS]\n";	
				print "bound size: $bound\n";
				$matched = 1;
			}
			return $bound;
		}
	}
	if( $matched == 0 ){
		print "trying to match pattern 2 prefix! $insn_array[$idx][ORIG_POS]\n";
		my $src_operand = "";
		my $cur = $idx;
		($cur, $src_operand) = discover_mov_nearby($cur, $reg);
		#$cur = $cur -1;
		if($insn_array[$cur-1][INSN_STR] =~ m/^\s*ja/){
			$cur = $cur -1;
			$bound = discover_cmp_nearby($cur, $src_operand);
			if($bound != 0){
				print "match pattern 2-1! $insn_array[$idx][ORIG_POS]\n";	
				print "bound size: $bound\n";
				$matched = 1;
			}
			return $bound;
		}elsif($insn_array[$idx-3][INSN_STR] =~ m/^\s*jae/){
			print "match pattern 2-3 prefix! $insn_array[$idx][ORIG_POS]\n";
			$bound = discover_cmp_nearby($idx-3, $src_operand);
			if($bound != 0){
				print "match pattern 2-3! $insn_array[$idx][ORIG_POS]\n";
				$bound = $bound -1;
				print "bound size: $bound\n";
				$matched = 1;
			}
			return $bound;
		}
		if($cur != $idx and defined $reverse_target{$insn_array[$cur][ORIG_POS]}){
			print "match pattern 2-2 prefix! $insn_array[$idx][ORIG_POS]\n";
			my $src_pos = $reverse_target{$insn_array[$cur][ORIG_POS]};
			$cur = $pos_mapping{$src_pos};
			if($insn_array[$cur][INSN_STR] =~ m/^\s*jbe/){
				$bound = discover_cmp_nearby($cur, $src_operand);
				if($bound != 0){
					print "match pattern 2-2! $insn_array[$idx][ORIG_POS]\n";	
					print "bound size: $bound\n";
					$matched = 1;
				}
				return $bound;
			}
			return $bound;
		}
	}
	if( $matched == 0 and
		$insn_array[$idx-1][INSN_STR] =~ m/^\s*and[l]*\s*\$0x([0-9a-f]+),($reg)\s*$/){
		print "match pattern 3 prefix! $insn_array[$idx][ORIG_POS]\n";
		$bound = hex($1)+1;
		print "bound size: $bound\n";
		$matched = 1;
		return $bound;
	}
	if(defined $reverse_target{$insn_array[$idx][ORIG_POS]}){
		print "match pattern 4 prefix! $insn_array[$idx][ORIG_POS]\n";
		my $src_pos = $reverse_target{$insn_array[$idx][ORIG_POS]};
		$cur = $pos_mapping{$src_pos};
		#print "match pattern 4 position: $src_pos\n";
		if($insn_array[$cur][INSN_STR] =~ m/^\s*jbe/){
			print "match pattern 4 prefix! $insn_array[$idx][ORIG_POS]\n";
			#$src_operand = $reg;
			($cur, $src_operand) = discover_mov_nearby($cur, $reg);
			$bound = discover_cmp_nearby($cur, $src_operand);
			if($bound != 0){
				print "match pattern 4! $insn_array[$idx][ORIG_POS]\n";	
				print "bound size: $bound\n";
				$matched = 1;
			}
			return $bound;
		}
		return $bound;
	}
	return $bound;
}

sub generate_jmp_table_content {
	my $offset = shift;
	my $size = shift;
	my $default_tgt = shift;
	my $ro_fh = shift;
	my $bin_fh = shift;
	my $reg = shift;
	my $stride = shift;
	my $idx = shift;
	my $base_addr = shift;
	my $cur_insn;
	my $guess = 0;#flag whether the jmp table is speculated or not
	my $actual_size = 0;
	seek($bin_fh, $offset, 0);
	if($size == 0){
		$guess = 1;
		$size = $speculate_table_size;
	}
	for my $x (0 .. $size-1){
		my $addr_hex;
		read($bin_fh, $addr_hex, 4);
		my $addr = sprintf("%x",unpack('I',$addr_hex));
		#print "jmp table content: $addr\n";
		$addr =~ s/^\s*0*//;
		$actual_size = $actual_size + 1;
		if(defined $pos_mapping{$addr}){
			#print "defined\n";
			print $ro_fh ".long trans_$addr\n";
		}else{
			#print "undefined\n";
			#print $ro_fh ".long $default_tgt\n";
			print $ro_fh ".long 0\n";
			last;
		}
		
	}
	$size = $actual_size;
	if($size <= 128){
		$cur_insn = "andl \$0x0000007f, $reg\n";	
	}elsif($size <= 256){
		$cur_insn = "andl \$0x000000ff, $reg\n";	
	}elsif($size <= 0x10000){
		$cur_insn = "andl \$0x0000ffff, $reg\n";	
	}elsif($size <= 0x01000000){
		$cur_insn = "andl \$0x00ffffff, $reg\n";	
	}else{
		print "jmp table size larger than 0x01000000, abort\n";
		translation_abort();
	}
	$cur_insn = $cur_insn .
		"jmp   \*jmp_table_$insn_array[$idx][ORIG_POS]\(,$reg,$stride\)\n".
		"ijmp_next_$insn_array[$idx][ORIG_POS]:\n";
	return $cur_insn;
	
}
my $__FCALLSTUB; #file handler for transparent call code stubs
my $callstub_opened=0;
my $callstub_filename = "./transparent_callstubs.S";
sub instrument_indirect_control {	
	#handle indirect control transfer
	my $icf = shift;
	my $itarget = shift;
	my $type = shift;#direct=1 directly to global lookup
	my $idx = shift;
	my $cur_insn = "";
	if($icf =~ m/^\s*(call|calll)\s*$/){
		#matching a indirect call using register
		#print "indirect call:".$cur_insn."\n";

		#$transparent_call == 0: non-transparent mode
		if($transparent_call == 0){
			$cur_insn = 
				#'movl   $1,%gs:0x3c'."\n".	
				'movl	%eax,%gs:0x44'."\n".#save caller save register
				"movl   ".$itarget.',%eax'."\n";
			if($translate_ret_to_lookup == 0){
				$cur_insn = $cur_insn .
				'.p2align '.BUNDLE_ALIGN."\n".
				'.byte 0x8d,0xbc,0x27,0x00,0x00,0x00,0x00'."\n".
				'.byte 0x8d,0xb4,0x26,0x00,0x00,0x00,0x00'."\n".
				'.byte 0x8d,0xbc,0x27,0x00,0x00,0x00,0x00'."\n";
			}
				$cur_insn = $cur_insn .
				'movl   %eax,%gs:0x40'."\n";
				if($save_eflags ==1){
					$cur_insn = $cur_insn .
						'lahf'."\n";
				}
				$cur_insn = $cur_insn .
					'calll  binsearch_save';

		}elsif($transparent_call == 1){
			if($callstub_opened ==0){
				print "openning the callstub file\n";
				open($__FCALLSTUB,'>'.$callstub_filename) || die("can't open callstub file: $!");
				$callstub_opened = 1;
			}
			my $stub_code = "CALLSTUB_$insn_array[$idx][ORIG_POS]:\n".
					"#include \"callstub_icall_pre.h\"\n".
					"subl \$offset_$insn_array[$idx+1][ORIG_POS], (%esp)\n".
					"#include \"callstub_icall_post.h\"\n";
			
			if(not defined $icf_lookup_routine_name{$insn_array[$idx][ORIG_POS]}){
 				$stub_code = $stub_code .
					"jmp    binsearch_save\n".
					"CALLSTUB_NEXT_$insn_array[$idx][ORIG_POS]:";
			}else{
				$stub_code = $stub_code . "\tjmp ".$icf_lookup_routine_name{$insn_array[$idx][ORIG_POS]}."_save\n";
			}
			print $__FCALLSTUB $stub_code;
			$cur_insn = 	"movl  %eax, %gs:0x44\n".
					"movl   ".$itarget.',%eax'."\n".
					'movl   %eax,%gs:0x40'."\n";
			if($save_eflags ==1){
				$cur_insn = $cur_insn .
					'lahf'."\n";
			}
			$cur_insn = $cur_insn .
					"call CALLSTUB_$insn_array[$idx][ORIG_POS]\n";#.
					#"jmp CALLSTUB_NEXT_$insn_array[$idx][ORIG_POS]\n";
			#$cur_insn = $cur_insn . $stub_code;
		}else{
			print "unhandled indirect call:".$cur_insn."\n";
			print "this is because transparent_call has an unsupported value: $transparent_call\n";
			translation_abort();
		}
		
	}elsif($icf =~ m/^\s*(jmp|jmpl)\s*$/){
		#matching a indirect jump using register
		#print "indirect jmp:".$cur_insn."\n";
		if($type == 1){
			$cur_insn = #'movl   $1,%gs:0x3c'."\n".
				'movl	%eax,%gs:0x44'."\n".#save caller save register	
				'movl   '.$itarget.',%eax'."\n".
				'movl   %eax,%gs:0x40'."\n".
				'inter_module_jmp:'."\n".
				'movl	%ecx,%gs:0x48'."\n".
				'movl	%edx,%gs:0x4c'."\n".
				'movl	%esi,%gs:0x50'."\n".
				'movl	%edi,%gs:0x54'."\n".
				'movl	$0x03000000, %eax'."\n".
				'jmp	*%eax'."\n";
		}elsif($type == 0){
			$cur_insn = instrument_jmp_table($icf, $itarget, $idx);
			#ATTN: don't modify the following code
			#it will largely affect the performance !!
			if($cur_insn eq ""){
				$cur_insn = $cur_insn .
					'movl	%eax,%gs:0x44'."\n".	
					'movl   '.$itarget.',%eax'."\n".
					'movl   %eax,%gs:0x40'."\n";
				if($save_eflags ==1){
					$cur_insn = $cur_insn .
						'lahf'."\n";
				}
				$cur_insn = $cur_insn .
					'jmp   binsearch_save'."\n";
			}
			#end of ATTN
		}elsif($type == 2){
			$cur_insn = 
				'movl	%eax,%gs:0x44'."\n".	
				'movl   '.$itarget.',%eax'."\n".
				'movl   %eax,%gs:0x40'."\n".
				'jmp    inter_module_jmp'."\n";
		}elsif($type == 3){
			#type = 3 is used for enforce_plt
			$cur_insn = $cur_insn .
				'movl	%eax,%gs:0x44'."\n".	
				'movl   '.$itarget.',%eax'."\n".
				'movl   %eax,%gs:0x40'."\n".
				'jmp   plt_search_save'."\n";
		}
	
		#if($translate_ret_to_lookup == 0){
		#	$cur_insn = $cur_insn .
		#		'.p2align '.BUNDLE_ALIGN."\n";
		#}
		
#		$cur_insn = $cur_insn .
#				'movl   %eax,%gs:0x40'."\n";
#		if($type == 1){
#			$cur_insn = $cur_insn .
#				'movl	$0x03000000, %eax'."\n".
#				'jmp	*%eax'."\n";
#		}else{
#			$cur_insn = $cur_insn .
#				'jmp   binsearch_save'."\n";
#		}
#			#print "unhandled indirect jump:".$cur_insn."\n";
	}
	#print "cur_insn: $cur_insn\n";
	return $cur_insn;
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
						exit(1);
					}
					$translate_ret_to_lookup = $configval;

				}
				case "call_to_pushjmp" {
					if($configval != 1 and $configval !=0){
						print "call_to_pushjmp error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$call_to_pushjmp = $configval;
				}
				case "transform_plt"{
					if($configval != 1 and $configval !=0){
						print "call_to_pushjmp error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$translate_plt = $configval;
				}
				case "enforce_plt"{
					if($configval != 1 and $configval !=0){
						print "enforce_plt error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$enforce_plt = $configval;
				}

				case "enforce_ret"{
					if($configval != 1 and $configval !=0){
						print "enforce_ret error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$enforce_ret = $configval;
				}
				case "speculate_icf"{
					if($configval != 1 and $configval !=0){
						print "speculate_icf error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$speculate_icf = $configval;
				}
				case "translate_jmp_table"{	
					if($configval != 1 and $configval !=0){
						print "translate_jmp_table error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$translate_jmp_table = $configval;
				}
				case "transparent_call"{	
					if($configval != 1 and $configval !=0){
						print "transparent_call error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$transparent_call = $configval;
				}
				case "save_eflags"{	
					if($configval != 1 and $configval !=0){
						print "save_eflags error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$save_eflags = $configval;
				}
				case "disasm_get_icf"{	
					if($configval != 1 and $configval !=0){
						print "disasm_get_icf error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$disasm_get_icf = $configval;
		

				}
				case "hijack_entry"{	
					if($configval != 1 and $configval !=0){
						print "hijack_entry error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$hijack_entry = $configval;
				}
				case "do_not_trans_syscall"{	
					if($configval != 1 and $configval !=0){
						print "do_not_trans_syscall error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$do_not_trans_syscall = $configval;
		

				}

				case "fix_disasm"{	
					if($configval != 1 and $configval !=0){
						print "fix_disasm error\n";
						print "please change the config option in config file:\n";
						print $_."\n";
						exit(1);
					}
					$fix_disasm = $configval;
		

				}else{
					#print "unknown config option:".$configopt."\n";
					#exit(1);
			
				}
			}
		}else{
			print "unknown recognized option:".$_."\n";
			exit(1);
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
sub setup_bin_type {
	my $_bname = $_[0];
	my $sonname_line = "";
	my $soname = "";
	get_elf_type($_bname);
	if($elf_type eq "EXEC"){
		$bin_type = "EXEC";
	}elsif($elf_type eq "DYN"){
	
		$cmd = "readelf -d ".$_bname." |"."awk \'{print \$2}\'|";
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

sub disasm_lift {
	#initialize some global value:
	my $cur_bytes = "";
	my $cur_index = 0;
	my $cur_insn = "";

	my $insn_bin = '([0-9a-fA-F]{2}\s)+';
	#this following is a full list of (un)conditional jump/call insn opcodes
	#href: http://ref.x86asm.net/coder32-abc.html#J
	my $addr = '0x[0-9a-fA-F]{1,8}|[0-9a-fA-F]{1,8}';
	my $no_0x_addr = '[0-9a-fA-F]{1,8}';

	my $objdump_file = $_[0];#shift(@ARGV);
	#my $output = shift(@ARGV);
	my $configfile = shift(@ARGV);
	my $testfile = 'test.s';
	my $outputfile = 'generated_asm.s';

	my $objfile = '[\w\d\.\_\-\+\/\@]+';
	my $abi = '[\w\d\-]+';
	my $secname = '[\w\d\.\_\-\@]+';

	my $func_entry = '[0-9a-fA-F]{8}';
	my $target = '[\$\%\w\d\_\@\-\.\+\*]+';
	#open(OUTPUT,'>'.$output) or die("can't open output file".": $!");

	%pos_mapping = ();
	@insn_array = ();
	@direct_target_addr = ();
	close(TEST);
	close(OUTPUT);
	close(ASM);
	close(CALLPOP);	
	open(TEST, '>'.$testfile) or die("can't open file for testing: $!");
	open(OUTPUT, '>'.$outputfile) or die("can't open file for err: $!");
	open(ASM, '<'.$objdump_file) or die("can't open input file:$objdump_file: $!");
	open(CALLPOP,">/tmp/callpop") or die("can't open callpop file: $!");
	while(<ASM>){
		if( $_ =~ m/^\s*([^\:]+)\:\t([^\t]+)\t([^\n]+)$/){
		#processing valid instructions
			$cur_pos = $1;
			$cur_bytes = $2;
			$cur_insn = trim($3);
			if($entry_begin eq $cur_pos){
				if(($bin_type eq "EXEC") or ($hijack_entry == 1)){
					print "insert a call at entry point\n";
					@insn = ($cur_pos, "pusha\ncall   __my_trap_redirector\npopa","e8 00 00 00 00",$I_ADDED,$B_IS_DIRECT_CF,0,$C_CALL);
					#@insn = ($cur_pos, "call   __my_trap_redirector\n","e8 00 00 00 00",$I_ADDED,$B_IS_DIRECT_CF,0,$C_CALL);
					push @insn_array, [@insn];
					$pos_mapping{$cur_pos} = $cur_index;
					$cur_index = $cur_index+1;
					$cur_pos = "__orig_entry_point";
				}
			}elsif($cur_insn =~ m/^\s*lock/){
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
				#print "without lock, cur_insn is: $cur_insn\n";
				#print "without lock, cur_bytes is: $cur_bytes\n";
				#print "without lock, cur_pos is: $cur_pos\n";
			}
			if($cur_bytes eq ""){
				print "raw bytes is empty, exit";	
				print $_;
				close(OUTPUT);
				unlink($outputfile);
				close(TEST);
				unlink($testfile);
				exit(1);
			}
			if($cur_insn eq "(bad)"){
				print "disassembly error!!\n";
				print $_;
				close(OUTPUT);
				unlink($outputfile);
				close(TEST);
				unlink($testfile);
				exit(1);
			}
			#$cur_bytes = "0x".$cur_bytes;
			#$cur_bytes =~ s/ /,0x/g;
			#print "raw bytes is ".$cur_bytes."\n";
			#print "insn is ".$cur_insn."\n";
			#print a label
			print TEST "_".$cur_pos.":\n";

			if($cur_insn =~ m/^\s*($cf_opcode)\s+($insn_addr)/){#\s+\<($target)\>\s*$/){
				#handle direct control transfer
				print TEST $1.' _'.$2."\n";
				$cur_opcode = $1;
				$cur_target = $2;
				$reverse_target{$cur_target} = $cur_pos;
				if($cur_insn =~ m/^\s*($opcode_icf)\s+($insn_addr)/){#\s+\<($target)\>\s*$/){
				#unconditional control transfer
					$_opcode = $1;
					$_target = $2;
					$_target =~ s/^\s*0x//;
					if( $_opcode =~ m/^call|calll\s*$/){
					#handle call
						@insn = ($cur_pos, $_opcode.' _'.$_target, trim($cur_bytes), $I_ORIGINAL ,$B_IS_DIRECT_CF, $_target, $C_CALL);
					}else{
					#handle jmp
						@insn = ($cur_pos, $_opcode.' _'.$_target, trim($cur_bytes), $I_ORIGINAL, $B_IS_DIRECT_CF, $_target);
					}
					push @insn_array, [@insn];
	
				}elsif($cur_insn =~ m/^\s*($cond_cf_opcode)\s+($insn_addr)/){#\s+\<($target)\>\s*$/){
					$cur_opcode = $1;
					$cur_target = $2;
					$cur_target =~ s/^\s*0x//;
				#conditional control transfer
					@insn = ($cur_pos, $cur_opcode.' _'.$cur_target, trim($cur_bytes), $I_ORIGINAL, $B_IS_DIRECT_CF, $cur_target);
					push @insn_array, [@insn];
					#print $cur_insn."\n";
				}else{
					print "unhandled direct control flow instruction, abort";
					translation_abort();
				}
				push @direct_target_addr, $cur_target;
			}elsif($cur_insn =~ m/^\s*($opcode_icf)\s*\*([^\n]+)$/){
				#handle indirect control transfer
				$icf = $1;
				$itarget = $2;
				if($cur_section eq '.plt' and $translate_plt == 1){
					#do not instrument the icf(indirect jumps) in .plt section
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL, $B_IS_INDIRECT_CALLJMP, "", $C_IJMP_PLT);
				}else{
					#print "instrumenting a ijmp/icall instruction at location: $cur_pos\n";
					#$_insn = instrument_indirect_control($icf,$itarget,0,$x);
					if($icf =~ m/^\s*(call|calll)/){
						#@insn = ($cur_pos, $_insn, "", 0, "3", "", 2);
						@insn = ($cur_pos, $cur_insn, "", $I_ORIGINAL, $B_IS_INDIRECT_CALLJMP, "", $C_ICALL);
					}else{
						
						#@insn = ($cur_pos, $_insn, "", 0, "3","", 3);
						@insn = ($cur_pos, $cur_insn, "", $I_ORIGINAL, $B_IS_INDIRECT_CALLJMP,"", $C_IJMP_TEXT);
					}
				}
				push @insn_array, [@insn];

			#}elsif($cur_insn =~ m/^\s*ret\s*$/){
			#	#handle ret as indirect control transfer
			#	@insn = ($cur_pos, $cur_insn, trim($cur_bytes), 0,"0");
			#	push @insn_array, [@insn];
			}elsif($cur_insn ne ""){
			#handl all the other instructions
				if($cur_insn =~ m/^\s*lea\s+0x0\(($gpr)\,\%eiz\,1\)\,($gpr)$/){
					if($1 eq $2){
						print TEST "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n";
						@insn = ($cur_pos, ".p2align 4", trim($cur_bytes), $I_ORIGINAL);
						push @insn_array, [@insn];
					}else{
						print "strange instruction here\n";
						translation_abort();
					}
				}elsif($cur_insn =~ m/^\s*repz\s+(ret|retl)\s*$/){
					#handling repz ret
					#print "handling illegal instruction:".$cur_insn."\n";
					$cur_opcode = "ret";
					$cur_insn = 'ret';
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes), $I_ORIGINAL, $B_IS_RETURN);
					push @insn_array, [@insn];
				
				}elsif($cur_insn =~ m/^\s*(ret|retl)\s*$/){
					#handling ret
					if($translate_ret_to_lookup == 1){
						#$cur_insn = handle_ret("", $cur_pos);
					}
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL, $B_IS_RETURN);
					push @insn_array, [@insn];
				}elsif($cur_insn =~ m/^\s*(ret|retl)\s*([^\n]+)$/){
					#handling ret
					if($translate_ret_to_lookup == 1){
						#$cur_insn = handle_ret($2, $cur_pos);
					}
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL, $B_IS_RETURN);
					push @insn_array, [@insn];
				}else{
					print TEST $cur_insn."\n";
					#push insn into array
					if($cur_bytes eq ""){
						print "raw bytes is empty\n";
						print "insn: ".$cur_insn."\n";
					}
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL);
					push @insn_array, [@insn];
				}
			}
			$pos_mapping{$cur_pos} = $cur_index;
			#print $pos_mapping{ $cur_pos }."\n";
			$cur_index = $cur_index+1;
		}
		elsif($_ =~ m/^($objfile):\s*file\sformat\s($abi)$/){
		#recognize objfile name and abi
			$objname = $1;
			#print TEST $objname."\n";
			$cur_abi = $2;
			#print TEST $cur_abi."\n";
			print TEST ".file\t".'"'.$objname.'"'."\n";
			#print TEST "\t.text\n";	
			$entry_begin = get_entry_addr($objname);
			get_elf_type($objname);
			setup_bin_type($objname);
			get_got_address($objname);
			print "entry point is 0x".$entry_begin."\n";

		}
		elsif( $_ =~ m/^\s*([^\:]+)\:\t([^\n]+)$/){
			#this line only contains raw byte for the previous instruction
			#print "raw bytes ". $2."\n";
			#print "current index ".$cur_index."\n";
			#print "previous instruction: ".$insn_array[$cur_index-1][INSN_STR]."\n"; 
			$insn_array[$cur_index-1][RAW_BYTES] = trim($insn_array[$cur_index-1][RAW_BYTES])." " .trim($2);

		}elsif($_ =~ m/^(\s*)$/){
		#recognize empty lines
		#do nothing here
		}
		elsif($_ =~ m/^(\s*)[\.]{3}(\s)*$/){
		#recognize omited line (objdump specific)
			$tapping = 1;
			$pre_pos = $cur_pos;		
		}
		elsif($_ =~ m/^Disassembly\sof\ssection\s($secname)\:$/){
		#recognize the section name
			$cur_section = $1;
			#print TEST $cur_section."_:\n";
			if($cur_section eq '.text'){
				print "text section index:".$cur_index."\n";
			}elsif($cur_section eq '.init'){
				$cur_pos = "_my_init";
				$cur_insn = "";
				$cur_bytes = "";
				@insn = ($cur_pos, $cur_insn, trim($cur_bytes),$I_ORIGINAL);
				push @insn_array, [@insn];
				$pos_mapping{$cur_pos} = $cur_index;
				$cur_index = $cur_index+1;
			}
		}
		elsif($_ =~ m/^($func_entry)\s*\<($target)\>\:$/){
		#function definition
			#print TEST $2.":\n";
		}
		else{
			#This should be errors:
			print "error in parsing: ".$_."\n";
		}
		#print OUTPUT $_;
		#print $_;
	}

}
sub instrument_all_icf {
	my $size = @insn_array;
	my $insn = "";
	my $total_ret = 0;
	my $speculate_ret = 0;
	my $syscalls = 0;

	if( $client_hook_icf_instrumentation ne ""){
		$client_hook_icf_instrumentation->();
	}

	for $x (0 .. $size-1){
		if((defined $insn_array[$x][BRANCH]) and ($insn_array[$x][BRANCH] eq $B_IS_RETURN) and ($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL)){
			#handle return
			if($translate_ret_to_lookup == 1){
				$total_ret = $total_ret +1;
				if($insn_array[$x][INSN_STR] =~ m/^\s*(ret|retl)\s*$/){
					if(handle_ret("", $insn_array[$x][ORIG_POS]) == 1){
						$speculate_ret = $speculate_ret+1;
					}
				}elsif($insn_array[$x][INSN_STR] =~ m/^\s*(ret|retl)\s*([^\n]+)$/){
					my $imm = $2;
					if(handle_ret($imm, $insn_array[$x][ORIG_POS]) == 1){
						$speculate_ret = $speculate_ret+1;
					}				
				}
			}
		}elsif((defined $insn_array[$x][BRANCH]) and ($insn_array[$x][BRANCH] eq $B_IS_INDIRECT_CALLJMP) and 
			($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL)){
			#handle indirect jmp/call
			#print "translating icf: $insn_array[$x][INSN_STR]\n";
			if($do_not_trans_syscall==1 and $insn_array[$x][INSN_STR]=~ m/^\s*(call|calll)\s*\*%gs:0x10\s*$/){
				$insn_array[$x][INSTRU_FLAG] = $I_TRANSLATED;
				$syscalls +=1;
				next;
			}elsif($insn_array[$x][INSN_STR]=~ m/^\s*($opcode_icf)\s*\*([^\n]+)$/){
				my $icf = $1;
				my $itarget = $2;
				$insn_array[$x][INSN_STR] = instrument_indirect_control($icf,$itarget,0, $x);
				$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH;
			}else{
				print "indirect icf instruction should not have opcode: $icf. abort\n";
				translation_abort();
			}
		}
	}
	print "total returns: $total_ret\t speculated returns: $speculate_ret\ntotal syscalls: $syscalls\n";
}
sub speculate_ret {
	my $speculate = 0;
	my $__insn = "";
	my $src_addr = $_[0];
	my $first_addr = $_[1];
	my $last_addr = $_[2];
	
	my $lookup_cost = 5;
	my $cmp_cost = 1;
	my $total_cost = 0;
	my $total_cmp_cost = 0;
	my $total_lookup_cost;
	my $cur = 0;
	my $r = $ret_target{$src_addr};
	my @a = sort {$r->{$b} <=> $r->{$a}} keys %$r;
	my $size = @a;
	#compute the whole cost
	for $x (0 .. $size-1){
		$total_cost = $total_cost + 5*int($r->{$a[$x]});
	}
	$total_lookup_cost = $total_cost;
	$total_cmp_cost = 0;
	print "total cost: $total_cost\n";
	for $x (0 .. $size -1){
		if((hex($a[$x]) < $first_addr) or (hex($a[0]) >$last_addr)){
			print "find external ret at 0x$src_addr, stop speculating\n";
			print "target address:$a[$x]\n";
			print "first address: $first_addr\n";
			print "last address: $last_addr\n";
			return ($__insn, $speculate);
		}
		if($r->{$a[$x]} < 500){
			print "size smaller than 500, return\n";
			return ($__insn, $speculate);
		}
		#if(($x+1)*$cmp_cost >= $lookup_cost){
		#	print "too many compare, return\n";
		#	return ($__insn, $speculate);
		#}
		#compute updated cost
		for $y ($x .. $size-1){
			$total_cmp_cost  = $total_cmp_cost + $cmp_cost*$r->{$a[$y]};
		}
		$total_lookup_cost = $total_lookup_cost - $lookup_cost*$r->{$a[$x]};
		my $cur_cost = $total_lookup_cost + $total_cmp_cost;

		if(($cur_cost -200) >= $total_cost){
			print "cost too high, return\n";
			return ($__insn, $speculate);
		}
		#adding cmp stub
		if($transparent_call == 0){
			$__insn = $__insn."cmpl \$trans_$a[$x], (%esp)\n".
				"jne speculate_ret_$src_addr".'_'."$a[$x]\n".
				#".byte 0xf3\nret\nspeculate_ret_$src_addr".'_'."$a[$x]:\n";
				"ret\nspeculate_ret_$src_addr".'_'."$a[$x]:\n";
		}elsif($transparent_call == 1){
			$__insn = $__insn."cmpl \$0x$a[$x], (%esp)\n".
				"jne speculate_ret_$src_addr".'_'."$a[$x]\n".
				"movl \$trans_$a[$x], (%esp)\n".
				"ret\nspeculate_ret_$src_addr".'_'."$a[$x]:\n";
		}else{
			print "incorrect transparent_call value\n";
			translation_abort();
		}
		$speculate = 1;
	}
	return ($__insn, $speculate);
}
sub handle_ret {
	my $__imm = $_[0];
	my $src_addr = $_[1];
	my $__index = $pos_mapping{$src_addr};
	my $speculate = 0;
	my $__insn = "";
	my $size = @insn_array;
	my $first_addr = 0;
	for $x (0 .. $size -1){
		if($insn_array[$x][ORIG_POS] =~ m/^\s*[0-9a-f]+\s*$/){
			$first_addr = hex($insn_array[$x][ORIG_POS]);
			last;
		}
	}
	my $last_addr = hex($insn_array[$size-1][ORIG_POS]);
	if($__imm eq ""){
		if(defined $ret_target{$src_addr}){
			print "find ret at location $src_addr has targets discovered\n";
			($__insn, $speculate) = speculate_ret($src_addr, $first_addr, $last_addr);
		}else{
			;#print "do not find ret targets at location $src_addr\n";
		}

		if(not defined $icf_lookup_routine_name{$insn_array[$__index][ORIG_POS]}){
			if($enforce_ret==1){
				if($transparent_call ==1){
					$__insn = $__insn . "\t".'jmp ret_search_save'."\n";
				}else{
					$__insn = $__insn . "\t".'jmp ret_local_search_save'."\n";
				}
			}else{
				$__insn = $__insn . "\t".'jmp local_search_save'."\n";
			}
		}else{
			$__insn = $__insn . "\tjmp ".$icf_lookup_routine_name{$insn_array[$__index][ORIG_POS]}."_save\n";
		}

		#print "index: $__index\n";
		my $str =  $__insn;
		$insn_array[$__index][INSN_STR] = $str;
		$insn_array[$__index][INSTRU_FLAG] = $I_TRANSLATED;
		#print "addr: $insn_array[$__index][ORIG_POS]\n";
		#print "insn: $insn_array[$__index][INSN_STR]";
	}else{
		$__insn = 	
		"\t".'movl %eax,%gs:0x44'."\n".
		"\t".'movl %ecx,%gs:0x48'."\n".
		"\t".'movl %edx,%gs:0x4c'."\n".	
		"\t".'movl %esi,%gs:0x50'."\n".
		"\t".'movl %edi,%gs:0x54'."\n".
		"\t".'movl (%esp),%eax'."\n".
		"\t".'movl %eax, %gs:0x40'."\n".
		"\t".'addl '.$__imm.",%esp\n".
		"\t".'addl $4, %esp'."\n";
		if(not defined $icf_lookup_routine_name{$insn_array[$__index][ORIG_POS]}){
			if($enforce_ret==1){
				if($transparent_call ==1){
					$__insn = $__insn . "\t".'jmp ret_search'."\n";
				}else{
					$__insn = $__insn . "\t".'jmp ret_local_search'."\n";
				}
			}else{
				$__insn = $__insn . "\t".'jmp local_search'."\n";
			}
		}else{
			$__insn = $__insn . "\tjmp ".$icf_lookup_routine_name{$insn_array[$__index][ORIG_POS]}."\n";
		}
		$insn_array[$__index][INSN_STR] = $__insn;
		$insn_array[$__index][INSTRU_FLAG] = $I_TRANSLATED;
	}
	#print "ret insn: $insn_array[$__index][INSN_STR]\n";
	return $speculate;
}

sub transform_insn_to_rawbytes {

}

sub print_direct_calls() {
	$size = @insn_array;
	print "array size is ". $size."\n";
	for $x (0 .. $size-1) {
		if(defined($insn_array[$x][BRAN_TARGET]) and $insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF){
			print OUTPUT $insn_array[$x][INSN_STR]."\n";
		}
	}
}
sub print_pos_mapping() {
	while (($key, $value) = each %pos_mapping){
		print $key. " ==> ".$value."\n";
	}

}
sub print_insn() {
	$size = @insn_array;
	print "array size is ". $size."\n";
	print OUTPUT "\t.file\t".'"'.$objname.'"'."\n";
	#print OUTPUT "\t.text\n";

	for $x (0 .. $size-1) {
		print OUTPUT "_".$insn_array[$x][ORIG_POS].":\n";
		print_insn_before(OUTPUT, $x);
		print OUTPUT "\t".$insn_array[$x][INSN_STR]."\n";
		print_insn_after(OUTPUT, $x);
		#print OUTPUT $insn_array[$x][RAW_BYTES]."\n";
	}

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
			return 1;

		}else{
			#print "call target:".$insn." ".$bytes."\n";
			#$pos_get_pc_thunk[$_index] = 2;
			return 0;
		}
	}
}

sub get_entry_addr {
	my $binname = $_[0];
	my $cmd = "readelf -h ".$binname." |";
	open(BIN, $cmd) or die("cannot open file".$binname." $!");
	while(<BIN>){
		if($_ =~ m/^\s*Entry point address:\s*0x([^\n]+)$/){
			$_entry_begin = $1;
			return $_entry_begin; 
		}	
	}
}

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
sub get_elf_type {
	my $binname = $_[0];
	my $cmd = "readelf -h ".$binname." |";
	open(BIN, $cmd) or die("cannot open file".$binname.": $!");
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

#parameter1: target address
sub analyze_pic_code {
	$size = @insn_array;
	for $x (0 .. $size-1) {
		if(defined($insn_array[$x][BRANCH]) and ($insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF) and
			($insn_array[$x][INSN_STR] =~ m/^\s*call/)){
			$target = $insn_array[$x][BRAN_TARGET];
			#print $insn_array[$x][ORIG_POS].":";
			#print $insn_array[$x][INSN_STR]."\t";
			#print $insn_array[$x][BRAN_TARGET]."\t";
			#print "insn index:".$pos_mapping{$insn_array[$x][ORIG_POS]}."\t";
			#print "current x:".$x."\t";
			#print "index:".$pos_mapping{$target}."\n";
			#print $insn_array[$x][INSN_STR]."\n";
			#print $insn_array[$x+1][INSN_STR]."\n";
			if( check_get_pc_thunk($target, $x) == 1){
				$next_insn = $insn_array[$x+1][INSN_STR];
				if($next_insn =~ m/^\s*add\s+([^,]+)\,($gpr)\s*$/){
					my $__offset = $1;
					my $__register = $2;
					$__offset =~ s/\$//;
					$__orig_addr = hex($__offset) + hex($insn_array[$x+1][ORIG_POS]);

					if(hex($got_addr) !=$__orig_addr){
						print "current postion + offset DO NOT EQUAL to GOT address in get-pc-thunk trampoline\n";
						if($elf_type eq "EXEC"){
							print "this could happen, when binary is statically linked with glibc code\n";
							print "old instruction:".$next_insn."\n";
							$__orig_addr_str = sprintf("%x",$__orig_addr);
							$new_insn = "\tadd\t".'$pic_'.$__orig_addr_str."_".$insn_array[$x+1][ORIG_POS].",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+1][INSN_STR] = $new_insn;
							$insn_array[$x+1][RAW_BYTES] = "81 c3 00 00 00 00";
							$insn_array[$x+1][INSTRU_FLAG] = $I_TRANSLATED;

						}elsif($elf_type eq "DYN"){
							print "old instruction:".$next_insn."\n";
							$__orig_addr_str = sprintf("%x",$__orig_addr);
							$new_insn = "\tadd\t".'$pic_'.$__orig_addr_str."_".$insn_array[$x+1][ORIG_POS].",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+1][INSN_STR] = $new_insn;
							$insn_array[$x+1][RAW_BYTES] = "81 c3 00 00 00 00";
							$insn_array[$x+1][INSTRU_FLAG] = $I_TRANSLATED;
							#speculate_icf_tgt($__orig_addr_str, $insn_array[$x][ORIG_POS]); 
						}else{
							print "unknown ELF type, abort\n";
							translation_abort();

						}
					}else{
						if($elf_type eq "EXEC"){
							print "next instruction:".$next_insn."\n";
							$new_insn = 'mov   $0x'.$got_addr.",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+1][INSN_STR] = $new_insn;
							$insn_array[$x+1][RAW_BYTES] = "bb 00 00 00 00";
							$insn_array[$x+1][INSTRU_FLAG] = $I_TRANSLATED;
						}elsif($elf_type eq "DYN"){
							print "next instruction:".$next_insn."\n";
							$new_insn = "\tadd\t".'$pic_'.$insn_array[$x+1][ORIG_POS].",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+1][INSN_STR] = $new_insn;
							$insn_array[$x+1][RAW_BYTES] = "81 c3 00 00 00 00";
							$insn_array[$x+1][INSTRU_FLAG] = $I_TRANSLATED;


						}else{
							print "unknown ELF type, abort\n";
							translation_abort();

						}
					}	
					#change get_pc_thunk to callpop
					$str = "call   _$insn_array[$x+1][ORIG_POS]\n";
					$insn_array[$x][INSN_STR] = $str;
					$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH; #should not be touched by following passes
					$insn_array[$x][CALL_FLAG] = $C_INVALID;#this is no longer a call instruction
					#add a pop after call get_pc_thunk
					$insn_array[$x+1][INSN_STR] = "pop $__register\n".$insn_array[$x+1][INSN_STR];
					$insn_array[$x+1][INSTRU_FLAG] = $I_NEVER_TOUCH; #should not be touched by following passes
				}
			}elsif( check_call_pop_trampoline($x,$target) == 1){
				$next_insn = $insn_array[$x+2][INSN_STR];
				$insn_array[$x][CALL_FLAG] = $C_INVALID;#this is no longer a call instruction, should not be translated
				$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH;#this is no longer a call instruction, should not be translated
				print "next instruction:".$next_insn."\n";
				if($next_insn =~ m/^\s*(add|addl)\s+([^,]+)\,\s*($gpr)\s*$/){
					my $__offset = $2;
					my $__register = $3;
					$__offset =~ s/\$//;
					$__orig_addr = hex($__offset) + hex($insn_array[$x+1][ORIG_POS]);
					if(hex($got_addr) !=$__orig_addr){
						print "current postion + offset DO NOT EQUAL to GOT address in call-pop trampoline\n";
						if($elf_type eq "EXEC"){
							print "this should not happen, unless specified\n";
							translation_abort();
						}elsif($elf_type eq "DYN"){
							print "old instruction:".$next_insn."\n";
							$__orig_addr_str = sprintf("%x",$__orig_addr);
							$new_insn = "\tadd\t".'$pic_'.$__orig_addr_str."_".$insn_array[$x+1][ORIG_POS].",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+2][INSN_STR] = $new_insn;
							$insn_array[$x+2][RAW_BYTES] = "81 c3 00 00 00 00";
							$insn_array[$x+2][INSTRU_FLAG] = $I_TRANSLATED;

						}else{
							print "unknown ELF type, abort\n";
							translation_abort();

						}
					}else{
						if($elf_type eq "EXEC"){
							print "next instruction:".$next_insn."\n";
							$new_insn = "\tmov\t".'$0x'.$got_addr.",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+2][INSN_STR] = $new_insn;

							#5 zeros indicates the length is 5 bytes, as expected in gcc-4.6
							#in the future, it subjects to changes in gcc
							$insn_array[$x+2][RAW_BYTES] = "bb 00 00 00 00";#
							$insn_array[$x+2][INSTRU_FLAG] = $I_TRANSLATED;
						}elsif($elf_type eq "DYN"){
							print "next instruction:".$next_insn."\n";
							$new_insn = "\tadd\t".'$pic_'.$insn_array[$x+1][ORIG_POS].",".$__register;
							print "new instruction: ".$new_insn."\n";
							$insn_array[$x+2][INSN_STR] = $new_insn;
							$insn_array[$x+2][RAW_BYTES] = "81 c3 00 00 00 00";#
							$insn_array[$x+2][INSTRU_FLAG] = $I_TRANSLATED;

						}else{
							print "unknown ELF type, abort\n";
							translation_abort();
						}
					}
						$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH;
						$insn_array[$x+1][INSTRU_FLAG] = $I_NEVER_TOUCH;
						$insn_array[$x+2][INSTRU_FLAG] = $I_NEVER_TOUCH;

				}else{
					print "call_pop is not followed by add \n";
					print "$insn_array[$x+2][ORIG_POS]:$insn_array[$x+2][INSN_STR]\n";	
					$insn_array[$x][CALL_FLAG] = $C_CALL;
					$insn_array[$x][INSTRU_FLAG] = $I_ORIGINAL;
					#$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH;
					#$insn_array[$x+1][INSTRU_FLAG] = $I_NEVER_TOUCH;
					#$insn_array[$x+2][INSTRU_FLAG] = $I_NEVER_TOUCH;
					#FIXME: This exception case should be loged at least!
					#translation_abort();
				}
			}
		}
	}

}

sub insn_len {
	$insn = $_[0];
	$len = length($insn);
	if($len != 0){
		$len = ($len + 1) / 3;
		return $len;
	}else{
		#for instrumented instruction
		return 0;
	}

}
sub transform_jecxz {
	print "This routine will rewrite jecxz" ."\n";
	$size = @insn_array;
	for $x (0 .. $size-1) {
		if($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL and 
			(defined $insn_array[$x][BRANCH]) and 
			($insn_array[$x][BRANCH] eq  $B_IS_DIRECT_CF)){

			$_insn_str = $insn_array[$x][INSN_STR];
			if($_insn_str =~ m/^($cf_opcode)\s*([^\n]+)$/){
				my $opcode = $1;
				my $target = $2;
				#print "transforming ".$opcode." instruction\n";
				$opcode = trim($opcode);
				switch ($opcode) {
					case "jecxz" {		
					print "find a jecxz,location:$insn_array[$x][ORIG_POS]\n";
					#print "jcxz cannot be handled. aborted\n";
					#exit(1);
					$str = 'jecxz _TRAMPO_'.$insn_array[$x][ORIG_POS]."\n";
					$str.='jmp _NEXT_'.$insn_array[$x][ORIG_POS]."\n";#this must be a two-byte jump
					$str.='_TRAMPO_'.$insn_array[$x][ORIG_POS].":\n";
					$str.='.byte 0xe9'."\n";#opcode for 5-byte jump
					$str.='.long '.$target.' - . -4'."\n";
					$str.='_NEXT_'.$insn_array[$x][ORIG_POS].":";
					$insn_array[$x][INSN_STR] = $str;
					$insn_array[$x][RAW_BYTES] ="e3 00 eb 00 e9 00 00 00 00"; }#should be 9 bytes
				}
			}
		}
	}
}

sub transform_direct_branch {
	my $x = $_[0];
	my $target;
	my $opcode;
	my $str;
	my $insn_str = $insn_array[$x][INSN_STR];
	if($insn_str =~ m/^($cf_opcode)\s*([^\n]+)$/){
		$opcode = $1;
		$target = $2;
		#print "transforming ".$opcode." instruction\n";
		$opcode = trim($opcode);
		switch ($opcode) {
			case "jmp" {	
				$str = '.byte 0xe9'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="e9 00 00 00 00"; }
			case "jb" {	
				$str = '.byte 0x0f,0x82'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 82 00 00 00 00"; }
			case "jnae" {	
				$str = '.byte 0x0f,0x82'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 82 00 00 00 00"; }
			case "jc" {	
				$str = '.byte 0x0f,0x82'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 82 00 00 00 00"; }
			case "jbe" {	
				$str = '.byte 0x0f,0x86'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 86 00 00 00 00"; }
			case "jna" {	
				$str = '.byte 0x0f,0x86'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 86 00 00 00 00"; }
			case "jcxz" {
				#print "jcxz cannot be handled. aborted\n";
				#exit(1);
				$str = 'jcxz _TRAMPO_'.$insn_array[$x][ORIG_POS]."\n";
				$str.='jmp _NEXT_'.$insn_array[$x][ORIG_POS]."\n";#this must be a two-byte jump
				$str.='_TRAMPO_'.$insn_array[$x][ORIG_POS].":\n";
				$str.='.byte 0xe9'."\n";#opcode for 5-byte jump
				$str.='.long '.$target.' - . -4'."\n";
				$str.='_NEXT_'.$insn_array[$x][ORIG_POS].":";
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="e3 00 eb 00 e9 00 00 00 00"; }#should be 9 bytes
			case "jecxz" {		
				#print "jcxz cannot be handled. aborted\n";
				#exit(1);
				$str = 'jecxz _TRAMPO_'.$insn_array[$x][ORIG_POS]."\n";
				$str.='jmp _NEXT_'.$insn_array[$x][ORIG_POS]."\n";#this must be a two-byte jump
				$str.='_TRAMPO_'.$insn_array[$x][ORIG_POS].":\n";
				$str.='.byte 0xe9'."\n";#opcode for 5-byte jump
				$str.='.long '.$target.' - . -4'."\n";
				$str.='_NEXT_'.$insn_array[$x][ORIG_POS].":";
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="e3 00 eb 00 e9 00 00 00 00"; }#should be 9 bytes
			case "jl" {	
				$str = '.byte 0x0f,0x8c'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8c 00 00 00 00"; }

			case "jnge" {	
				$str = '.byte 0x0f,0x8c'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8c 00 00 00 00"; }

			case "jle" {	
				$str = '.byte 0x0f,0x8e'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8e 00 00 00 00"; }
			case "jng" {	
				$str = '.byte 0x0f,0x8e'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8e 00 00 00 00"; }
			case "jnb" {	
				$str = '.byte 0x0f,0x83'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 83 00 00 00 00"; }
			case "jae" {	
				$str = '.byte 0x0f,0x83'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 83 00 00 00 00"; }
			case "jnc" {	
				$str = '.byte 0x0f,0x83'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 83 00 00 00 00"; }

			case "jnbe" {	
				$str = '.byte 0x0f,0x87'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 87 00 00 00 00"; }

			case "ja" {	
				$str = '.byte 0x0f,0x87'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 87 00 00 00 00"; }

			case "jnl" {	
				$str = '.byte 0x0f,0x8d'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8d 00 00 00 00"; }

			case "jge" {	
				$str = '.byte 0x0f,0x8d'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8d 00 00 00 00"; }

			case "jnle" {	
				$str = '.byte 0x0f,0x8f'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8f 00 00 00 00"; }

			case "jg" {	
				$str = '.byte 0x0f,0x8f'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8f 00 00 00 00"; }
			case "jno" {	
				$str = '.byte 0x0f,0x81'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 81 00 00 00 00"; }
			case "jnp" {	
				$str = '.byte 0x0f,0x8b'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8b 00 00 00 00"; }

			case "jpo" {	
				$str = '.byte 0x0f,0x8b'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8b 00 00 00 00"; }
			case "jns" {	
				$str = '.byte 0x0f,0x89'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 89 00 00 00 00"; }
			case "jnz" {	
				$str = '.byte 0x0f,0x85'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 85 00 00 00 00"; }

			case "jne" {	
				$str = '.byte 0x0f,0x85'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 85 00 00 00 00"; }

#my $cf_opcode = 'jmp\s|ljmp\s|jmpl\s|call\s|calll\s|jb\s|jnae\s|jc\s|jbe\s|jna\s|jcxz\s|jecxz\s|jl\s|jnge\s|jle\s|jng\s|jnb\s|jae\s|jnc\s|jnbe\s|ja\s|jnl\s|jge\s|jnle\s|jg\s|jno\s|jnp\s|jpo\s|jns\s|jnz\s|jne\s|jo\s|jp\s|jpe\s|js\s|jz\s|je\s';
			case "jo" {	
				$str = '.byte 0x0f,0x80'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 80 00 00 00 00"; }
			case "jp" {	
				$str = '.byte 0x0f,0x8a'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8a 00 00 00 00"; }
			case "jpe" {	
				$str = '.byte 0x0f,0x8a'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 8a 00 00 00 00"; }
			case "js" {	
				$str = '.byte 0x0f,0x88'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 88 00 00 00 00"; }
			case "jz" {	
				$str = '.byte 0x0f,0x84'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 84 00 00 00 00"; }
			case "je" {	
				$str = '.byte 0x0f,0x84'."\n";
				$str.='.long '.$target.' - . -4';
				$insn_array[$x][INSN_STR] = $str;
				$insn_array[$x][RAW_BYTES] ="0f 84 00 00 00 00"; }
			case "call"{
				;#do nothing here for call
			}


			else { 
				print "unable to recognize instruction opcode, abort.\n";
				translation_abort();
			}

		}
	}else{
		print "error recognizing a direct branch insn!! \n";
		translation_abort();
	}
}


sub transform_insn {
	print "This routine will rewrite instructions" ."\n";
	my $size = @insn_array;
	for $x (0 .. $size-1) {
		if($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL and (not defined $insn_array[$x][BRANCH])){
		#check if it is a normal instruction
			#print "this is a normal instruction\n";
			$insn_str = $insn_array[$x][RAW_BYTES];
			$insn_str =~ s/ /,0x/g;
			$insn_str = '.byte 0x'.$insn_str;
			$insn_array[$x][INSN_STR] = $insn_str;	
		}elsif($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL and ($insn_array[$x][BRANCH] eq  $B_IS_DIRECT_CF)){
		#handling a direct call instruction
			transform_direct_branch($x);
		
		#}elsif($insn_array[$x][INSN_STR] =~ m/^\s*ret\s*$/){	
		}elsif(defined ($insn_array[$x][BRANCH]) and ($insn_array[$x][BRANCH] eq $B_IS_RETURN)){	
		#handing a ret instruction
				$insn_array[$x][INSN_STR] = 'andl $0x07ffffe0,(%esp)'."\n".$insn_array[$x][INSN_STR];
				$insn_array[$x][RAW_BYTES] = '81 24 24 00 00 00 00 '.$insn_array[$x][RAW_BYTES];
			#adding a nop in front of ret, just debugging
				
			#$insn_array[$x][INSN_STR] = '.byte 0x8d,0xbc,0x27,0x00,0x00,0x00,0x00'."\n".$insn_array[$x][INSN_STR];
			#$insn_array[$x][RAW_BYTES] = '8d bc 27 00 00 00 00 '.$insn_array[$x][RAW_BYTES];
		}
	}
}

#This routine (pass) will bundle instructions into 32-byte blocks
#Note: this routine will make the position mapping useless, so any passes
#that will use this mapping should be done before this routine.
sub bundle_instruction(){
	my $size = @insn_array;
	my $cur_bsize = 0;
	print "This routine will bundle the instructions" ."\n";
	print "bundle size is: ".BUNDLE_SIZE."\n";
	print "entry begin is".$entry_begin."\n";
	for $x (0 .. $size-1) {
		$len = insn_len($insn_array[$x][RAW_BYTES]);
		#print "length:".$len."\t";
		if($len != int($len)){
			print "error in instruction length, not an integer\n";
			print "original bytes: ".$insn_array[$x][RAW_BYTES]."\n";
			translation_abort();
		}
		if($len == 0){
		#this is an instrumented instruction, make sure it is aligned
			$insn_array[$x-1][INSN_STR] = $insn_array[$x-1][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
			$insn_array[$x][INSN_STR] = $insn_array[$x][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
			#print "length-0 instruction is:".$insn_array[$x][INSN_STR]."\n";
			#print "raw bytes is:".$insn_array[$x][RAW_BYTES]."\n";
			$cur_bsize = 0;
			next;
		}

		#check if it is a direct call instruction, make sure it is at the bottom of a bundle
		elsif(defined $insn_array[$x][CALL_FLAG] and $insn_array[$x][CALL_FLAG] == $C_CALL){
			#a direct call will always take 5 bytes
			$len = 5;
			$padding = BUNDLE_SIZE - $len - $cur_bsize;
			#print "padding length: ".$padding."\n";
			if($padding >=0){
				while($padding >0){
					#padding should precede call
					$insn_array[$x][INSN_STR] ="\n"."nop"."\n".$insn_array[$x][INSN_STR];
					$padding--;
				}
			}else{
				$insn_array[$x-1][INSN_STR] =$insn_array[$x-1][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
				$padding = 27;
				while($padding >0){
					#padding should precede call
					$insn_array[$x][INSN_STR] ="nop\n".$insn_array[$x][INSN_STR];
					$padding--;
				}

			}
			#make sure no error propagation
			$insn_array[$x][INSN_STR] = $insn_array[$x][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
			$cur_bsize = 0;
			next;
		}
		#check if it is ret, do instrumentation for it

#		if($insn_array[$x][BRANCH] ==$B_IS_RETURN){
			#ret will be instrumented to the following:
			#0:	8b 14 24             	mov    (%esp),%edx
			#3:	83 c4 04             	add    $0x4,%esp
			#6:	23 15 e0 ff ff ff    	and    0xffffffe0,%edx
			#c:	ff e2                	jmp    *%edx
			#the above takes 13 bytes
#			$insn_string = 'mov    (%esp),%edx'."\n".
#					'add    $0x4,%esp'."\n".
#					'and    0xffffffe0,%edx'."\n".
#					'jmp    *%edx'."\n".
#					'.p2align '.BUNDLE_ALIGN;
#			$insn_array[$x][INSN_STR] = $insn_string;
#			$len = 13;
#
#			if( $cur_bsize + $len > BUNDLE_SIZE){
#				$insn_array[$x-1][INSN_STR] = $insn_array[$x-1][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
#			}
#			$cur_bsize = 0;
#			next;
#		}
		

		#print $insn_array[$x][RAW_BYTES]."\n";
		if( $cur_bsize + $len <= BUNDLE_SIZE){
			$cur_bsize += $len;
		}else{
			$insn_array[$x-1][INSN_STR] = $insn_array[$x-1][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN;
			#print "instruction string is ". $insn_array[$x][INSN_STR];
			$cur_bsize = $len;
		}
		#beginning of text section should be aligned
		if( $pos_mapping{$entry_begin} == $x){
			$insn_array[$x-1][INSN_STR] = $insn_array[$x-1][INSN_STR]."\n".'.p2align '.BUNDLE_ALIGN."\n"."__entry_begin:";
			$cur_bsize = $len;
			next;
		}

		#if($cur_bsize + $len 
	}
}


sub gen_random_p2align_v2 {
	my $size = @insn_array;
	my $threshold =  1;
	my $entry_index = $pos_mapping{$entry_begin};
	print "This routine will randomly generate nop pesudo instruction" ."\n";
	print "bundle size is: ".BUNDLE_SIZE."\n";
	print "entry begin is".$entry_begin."\n";
	for $x (0 .. $size-1) {	
		if($x >= $entry_index and $x <= $entry_index + 30){
			next;
		}
		$rand_num = rand();
		if($rand_num < $threshold){
			$rand_nop = BUNDLE_SIZE - insn_len($insn_array[$x][RAW_BYTES]);#= rand(32);
			while($rand_nop >0){
				$insn_array[$x][INSN_STR] ="\n".'.byte 0x90'."\n".$insn_array[$x][INSN_STR];
				$rand_nop--;
			}
		}
	}
}
sub gen_random_p2align {
	my $size = @insn_array;
	my $threshold =  1;
	my $entry_index = $pos_mapping{$entry_begin};
	print "This routine will randomly generate p2align pesudo instruction" ."\n";
	print "bundle size is: ".BUNDLE_SIZE."\n";
	print "text begin is".$entry_begin."\n";
	for $x (0 .. $size-1) {
		my $rand_num = rand();

		if($x >= $entry_index and $x < $entry_index + 30){
			next;
		}
		if($rand_num < $threshold){
			$insn_array[$x][INSN_STR] .="\n".'.p2align '.BUNDLE_ALIGN;
		}
	}
}
sub parse_clang_code {
	my $size = @insn_array;
	print "parsing out clang alignment code\n";

	for $x (0 .. $size-1) {
		if($insn_array[$x][INSN_STR] =~ m/(data32 )+[^\n]+$/){
			print "parsing: ".$insn_array[$x][INSN_STR]."\n";
			$insn_array[$x][INSN_STR] = '.p2align 4';
		}
		#print OUTPUT $insn_array[$x][RAW_BYTES]."\n";
	}

}
sub check_invalid_branch_target {
	my $size = @insn_array;
	my $_file = "invalid_branch";
	my $_file1 = "invalid_after_branch";
	print "beginning to check invalid branch targets\n";
	print "beginning to check potentially invalid insn after a branch insn\n";
	open(INBRAN,'>'.$_file) or die("cannot open file for invalid branch");
	open(IN_AF_BRAN,'>'.$_file1) or die("cannot open file for invalid branch");
	for $x (0 .. $size-1) {
		if((defined $insn_array[$x][BRANCH]) and ($insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF) and ($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL)){
			my $_target = $insn_array[$x][BRAN_TARGET];
			my $_index = $pos_mapping{$_target};
			if(not defined $_index or $_index eq ""){
				if($insn_array[$x][RAW_BYTES] =~ m/^\s*74 01\s*$/){
					$insn_array[$x][INSN_STR] = ".byte 0x74\n.byte 0x01\n";
				}else{
					print INBRAN $insn_array[$x][ORIG_POS]."\t".$insn_array[$x][RAW_BYTES]."\t".$insn_array[$x][INSN_STR]."\n";
				}
			}

		}
		if((defined $insn_array[$x][BRANCH]) and 
			($insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF or $insn_array[$x][BRANCH] eq $B_IS_RETURN) and 
			($insn_array[$x][INSTRU_FLAG] !=$I_ADDED) and
			($x < $size-1)){
			my $next_bytes = $insn_array[$x+1][RAW_BYTES];
			if(defined $next_bytes and $next_bytes =~ m/^\s*00\s/){
				print IN_AF_BRAN $insn_array[$x][ORIG_POS]."\t".$insn_array[$x][RAW_BYTES]."\t".$insn_array[$x][INSN_STR]."\n";
				print IN_AF_BRAN $insn_array[$x+1][ORIG_POS]."\t".$insn_array[$x+1][RAW_BYTES]."\t".$insn_array[$x+1][INSN_STR]."\n";
			}
		}
	}
}


sub convert_vma_to_offset {
	my $vma = $_[0];
	my $offset = -1;
	my $binname = $_[1];
	print "convert: binname is:$binname\n";
	$cmd = "readelf -l $binname |sed -e '1,/^\\s*\$/d'|sed  '/^\\s*\$/q'|";
	open(MYBIN, $cmd) or die("cannot open file".$binname." $!");
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


sub transform_call_to_pushjmp  {
	if($call_to_pushjmp == 0){
		return;
	}
	print "call_to_pushjmp: $call_to_pushjmp\n";
	my $size = @insn_array;
	print "this routine will rewrite all call instructions\n";
	for $x (0 .. $size-1){
		if((defined $insn_array[$x][BRANCH]) and 
			($insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF) and
			(defined $insn_array[$x][CALL_FLAG]) and
			($insn_array[$x][CALL_FLAG] ==$C_CALL) and
			($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL)){
			my $str = $insn_array[$x][INSN_STR];
			$str =~ s/call[l]*\s*//;
			print "::this is a call: $insn_array[$x][INSN_STR]\n";
			print "::target: $str\n";
			print "::next address: $insn_array[$x+1][ORIG_POS]\n";
			$insn_array[$x][INSN_STR] = "push \$0x$insn_array[$x+1][ORIG_POS]\n"."jmp $str";
			print "::after translation: $insn_array[$x][INSN_STR]\n";
		}elsif($insn_array[$x][INSTRU_FLAG] == $I_TRANSLATED){
			$str = "push \$0x$insn_array[$x+1][ORIG_POS]\n"."jmp ";
			$insn_array[$x][INSN_STR] =~ s/call[l]*/$str/;
			print "::this is a translated instruction: $insn_array[$x][INSN_STR]\n";
		}
	}
}
sub transform_direct_call_to_transparent {
	if($transparent_call == 0){
		return;
	}
	print "this pass will translate all direct call into a transprant mode\n";
	my $size = @insn_array;
	for $x (0 .. $size-1){
		if((defined $insn_array[$x][BRANCH]) and 
			($insn_array[$x][BRANCH] eq $B_IS_DIRECT_CF) and
			(defined $insn_array[$x][CALL_FLAG]) and
			($insn_array[$x][CALL_FLAG] ==$C_CALL) and
			($insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL)){
			my $target_str = $insn_array[$x][INSN_STR];
			$target_str =~ s/call[l]*\s*//;
			print "::this is a call: $insn_array[$x][INSN_STR]\n";
			print "::target: $target_str\n";
			print "::next address: $insn_array[$x+1][ORIG_POS]\n";
			$insn_array[$x][INSN_STR] = "call CALLSTUB_$insn_array[$x][ORIG_POS]\n";#.
						#"jmp CALLSTUB_NEXT_$insn_array[$x][ORIG_POS]\n";
			if($callstub_opened ==0){
				print "openning the callstub file\n";
				open($__FCALLSTUB,'>'.$callstub_filename) || die("can't open callstub file: $!");
				$callstub_opened = 1;
			}
			my $stub_code = "CALLSTUB_$insn_array[$x][ORIG_POS]:\n".
					"#include \"callstub_call_pre.h\"\n".
					"subl \$offset_$insn_array[$x+1][ORIG_POS], (%esp)\n".
					"#include \"callstub_call_post.h\"\n".
					"jmp    $target_str\n".
					"CALLSTUB_NEXT_$insn_array[$x][ORIG_POS]:";


			#$insn_array[$x][INSN_STR] = $insn_array[$x][INSN_STR] . $stub_code;
			print $__FCALLSTUB $stub_code;

			}
	}
}
sub transform_plt_v2 {
	my $objname = $_[0];
	if($enforce_plt != 1){
		print "no enforcement of plt section\n";
		return;
	}
	#check if plt exists!
	if(get_section_info($objname,".interp","addr") eq ""){
		print "binary is statically linked, so there is no PLT0\n";
		#return;

	}
	#figure out the scope of plt section
	my $plt_base = get_section_info($objname,".plt","addr");
	my $plt_size = get_section_info($objname,".plt","size");
	print "plt_base:$plt_base\n";
	if($plt_base eq ""){
		print "there is no plt section,return\n";
		return;
	}
	$plt_base =~ s/^0+//g;
	my $plt_last = sprintf("%x",hex($plt_base)+hex($plt_size));
	my $index = 0;
	my $last = 0;	
	print "first insn in .plt:$plt_base;\n";
	print "last  insn in .plt:$plt_last;\n";
	#find the 1st insn after .plt section
	while(not defined $pos_mapping{$plt_last}){
		$plt_last = sprintf("%x",hex($plt_last)+1);
	}
	my $index = $pos_mapping{$plt_base};
	my $last = $pos_mapping{$plt_last};

	my $PLT;
	open($PLT, ">./plt_target_addr") or die("cannot open file plt_target_addr: $!");
	my $first_ijmp = 0;
	for my $x ($index+1 .. $last){
		if($insn_array[$x][INSN_STR] =~ m/^\s*(jmp|jmpl)\s*\*([^\n]+)\s*$/){
			my $icf = $1;
			my $itarget = $2;
			if($first_ijmp == 0){
				$first_ijmp = 1;
				next;
			}else{
			#instrument all ijmp except the 1st one
				$insn_array[$x][INSN_STR] = instrument_indirect_control($icf,$itarget,3, $x);
				$insn_array[$x][INSTRU_FLAG] = $I_NEVER_TOUCH;
			}
		}elsif($insn_array[$x][INSN_STR] =~ m/^\s*(push|pushl)/){
			print $PLT "$insn_array[$x][ORIG_POS]\n";
		}
	}
	print $PLT "exported addresses:\n";
	my $cmd = "readelf --dyn-syms $objname|grep FUNC|awk '{print \$2}'|sed '\/^0\\+\$\/d'|";
	#print $PLT "$cmd\n";
	#system($cmd);
	open(my $EXP, $cmd) or die("cannot read dynamic symbol addresses: $!\n");
	while(<$EXP>){
		if($_ =~ m/^\s*([0-9a-f]+)\s*$/){
			print $PLT "translate_$1\n";
		}
	}
	close($EXP);
	close($PLT);
}
sub transform_plt {
	if($translate_plt != 1){
		print "no translation of plt section\n";
		return;
	}
	#check if plt exists!
	if(get_section_info($objname,".interp","addr") eq ""){
		print "binary is statically linked, so there is no PLT0\n";
		#return;

	}

	my $plt_base = get_section_info($objname,".plt","addr");
	my $plt_size = get_section_info($objname,".plt","size");
	print "plt_base:$plt_base\n";
	if($plt_base eq ""){
		print "there is no plt section,return\n";
		return;
	}
	$plt_base =~ s/^0+//g;
	my $plt_last = sprintf("%x",hex($plt_base)+hex($plt_size));
	my $index = 0;
	my $last = 0;	
	print "first insn in .plt:$plt_base;\n";
	print "last  insn in .plt:$plt_last;\n";
	#find the 1st insn after .plt section
	while(not defined $pos_mapping{$plt_last}){
		$plt_last = sprintf("%x",hex($plt_last)+1);
	}
	if(defined $pos_mapping{$plt_base} ){
		$index = $pos_mapping{$plt_base};
		$last = $pos_mapping{$plt_last};
	}else{	
		print "cannot find the 1st instruction in plt section, abort\n";
		translation_abort();
	}
	my $GOTSLOT;
	my $filename = "got_slots";
	open($GOTSLOT,'>'.$filename) || die("can't open gotslot file: $!");

	print "first insn in .plt:$plt_base; index: $index\n";
	print "last  insn in .plt:$plt_last; index: $last\n";

	$index = $index + 1;
	$last = $last -1;
	if(($insn_array[$index-1][INSN_STR]=~ m/^\s*(push|pushl)\s*0x([0-9a-f]+)\s*$/)
	and ($insn_array[$index][INSN_STR]=~ m/^\s*(jmp|jmpl)\s*\*([^\n]+)\s*$/)){
	#translating the 1st jmp * in plt
		print "index: $index\n";
		print "current insn: $insn_array[$index][INSN_STR]\n";

		my $cur_insn = instrument_indirect_control($1,$2,1,$index);
		$insn_array[$index][INSN_STR] = $cur_insn."\n".'.p2align 5'; 
		$insn_array[$index][INSTRU_FLAG] = $I_TRANSLATED; 
	}elsif(($insn_array[$index-1][INSN_STR]=~ m/^\s*(jmp|jmpl)\s*\*([^\n]+)\s*$/)
	and($insn_array[$index][INSN_STR]=~ m/^\s*(push|pushl)\s*\$0x([0-9a-f]+)\s*$/)){
		#the first stub in static binary
		#there is no PLT0 in static binary in fact. Therefore, each PLT stub is the same
		#print "index: $index\n";
		#print "current insn: $insn_array[$index][INSN_STR]\n";
		#print "cannot find the 1st indirect jmp in plt section, abort\n";
		#translation_abort();
		$index = $index - 2;
	}
	for $x ($index+1 .. $last){
		
		if($insn_array[$x][INSN_STR]=~ m/^\s*(jmp|jmpl)\s*\*([^\n]+)\s*$/){
			my $t = $2;
			my $o = $1;
			my $t1 = "";
			print $GOTSLOT "$t\n";
			my $cur_insn = "";
			my $trans = instrument_indirect_control($o,$t,0,$x);
			if($t =~ m/^0x[0-9a-fA-F]+$/){
				$t1 = $t;
				$cur_insn = 'cmpl $value_in_'.$t1.", $t\n";

			}elsif($t =~ m/^0x([0-9a-f]+)\(%ebx\)$/){
				#this is PIC code pattern in PLT section
				$t1 = "gotplus_$1";
				#in PIC, we only need to compare the lowest 8 bits
				$cur_insn = 'cmpb $value_in_'.$t1.", $t\n";
			}else{
				print "unknown indirect jmp: $insn_array[$x][INSN_STR]\n";
				translation_abort();
			}
			$cur_insn = $cur_insn . 
				"je   _$insn_array[$x+1][ORIG_POS]\n".
				$trans."\n";
			$insn_array[$x][INSN_STR] = $cur_insn;
			$insn_array[$x][INSTRU_FLAG] = $I_TRANSLATED;
			#To align the plt stub
			$insn_array[$x+2][INSN_STR]=$insn_array[$x+2][INSN_STR]."\n".'.p2align 4';
		}
	}
}
sub add_label_aftercall {
	my $size = @insn_array;
	print "adding label for next insn of call\n";
	for $x (0 .. $size-1) {
		if(defined $insn_array[$x][CALL_FLAG] and (($insn_array[$x][CALL_FLAG]==$C_CALL) or ($insn_array[$x][CALL_FLAG]==$C_ICALL))){
			#insert _callnext_xxx label just after call instruction, must be robust!
			my $orig_str = $insn_array[$x][INSN_STR];
			$insn_array[$x][INSN_STR] =~ s/call[l]*([^\n]+)[\n]*/call  $1\n_callnext_$insn_array[$x+1][ORIG_POS]:\n/g;
			if($orig_str eq $insn_array[$x][INSN_STR]){
				print "fail to add label after call on location: $insn_array[$x][ORIG_POS]\n";
				translation_abort();
			}
			#a$insn_array[$x][INSN_STR] =$insn_array[$x][INSN_STR]."\n_callnext_$insn_array[$x+1][ORIG_POS]:";
			#try the align the call target
			if($insn_array[$x][CALL_FLAG] ==$C_CALL){
				if(defined $insn_array[$x][BRAN_TARGET]){
					my $i = $pos_mapping{$insn_array[$x][BRAN_TARGET]};
					#print "updating call target: $insn_array[$i][ORIG_POS] with p2align\n";
					#$insn_array[$i][INSN_STR] = ".p2align 3\n". $insn_array[$i][INSN_STR];
				}
			}
		}
	}
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
			if(($src_insn =~ m/^ret/) or ($src_insn =~ m/^0/)){
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

sub custom_instrumentation {
	if($client_routine ne ""){
		print "entering client routine\n";
		$client_routine->();
	}
}
sub custom_instrumentation1 {
	my $size = @insn_array;
	for $x (0 .. $size-1){
		if(defined $insn_array[$x][CALL_FLAG] and 
			(($insn_array[$x][CALL_FLAG] ==$C_CALL) or
			($insn_array[$x][CALL_FLAG] ==$C_ICALL) or
			($insn_array[$x][CALL_FLAG] == $C_INVALID))){

		#=~ m/call/){# or 
		#	$insn_array[$x+1][INSN_STR] =~ m/call/ or 
		#	$insn_array[$x-1][INSN_STR] =~ m/call/){
			next;
		}else{
			#$insn_array[$x][INSN_STR] =$insn_array[$x][INSN_STR]."\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop";
			$insn_array[$x][INSN_STR] =$insn_array[$x][INSN_STR]."\npush %eax\nlahf\nincl %gs:0x34\nsahf\npop %eax";
		}
	}
}

#=============================================================================
#  The following are APIs exported for user instrumentation
sub sbt_instrument_lookup {
	my $routine = shift;
	my $type = shift;
	my $pos = shift;
	my $code = shift;
	my $instru_file = "";
	my $FD;
	if($type eq "TRANSLATE"){
		if($pos eq "BEFORE"){
			$instru_file = $routine."_instrument_pre.h";
		}elsif($pos eq "AFTER"){
			$instru_file = $routine."_instrument_post.h";
		}elsif($pos eq "ENTRY"){
			$instru_file = $routine."_instrument_entry.h";
		}
	}
	open($FD, '>./'.$instru_file) or die("cannot open file $instru_file for writing: $!");
	print $FD $code;
}
sub sbt_instrument_direct_call {
	my $instru_file = "";
	my $pos = shift;
	my $code = shift;
	my $FD;
	if($pos eq "BEFORE"){
		$instru_file = "callstub_call_pre.h";
	}elsif($pos eq "AFTER"){
		$instru_file = "callstub_call_post.h";
	}
	open($FD, '>./'.$instru_file) or die("cannot open file $instru_file for writing: $!");
	print $FD $code;
}
sub sbt_instrument_indirect_call {
	my $instru_file = "";
	my $pos = shift;
	my $code = shift;
	my $FD;
	if($pos eq "BEFORE"){
		$instru_file = "callstub_icall_pre.h";
	}elsif($pos eq "AFTER"){
		$instru_file = "callstub_icall_post.h";
	}
	open($FD, '>./'.$instru_file) or die("cannot open file $instru_file for writing: $!");
	print $FD $code;
}

sub sbt_insert_before_insn {
	my $x = shift;
	my $user_code = shift;
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_ADDED){
		if(defined $insn_array[$x-1][INSTRU_FLAG] and $insn_array[$x-1][INSTRU_FLAG] == $I_ADDED){
			next;
		}
	}
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_NEVER_TOUCH){
		next;
	}
	
	$insn_array[$x][INSN_STR] =$user_code."\n".$insn_array[$x][INSN_STR];
}

sub _insert_insn {
	my $array = shift;
	my $code = shift;
	my $flag = shift;
	my $x = shift;
	my $loc = shift;
	my $idx = @$array;
	if(($flag == $C_ICALL) or ($flag == $C_CALL)){
		$code = $code."\n__INSTRUMENT_RET_${x}_${loc}_$idx:\n";
	}
	push @$array, $code;
}

sub print_insn_before {
	my $fd = shift;
	my $idx = shift;
	my $array = $insn_array_before{$idx};
	if(not defined $array){
		return;
	}
	my $size = @$array;
	for my $i (0 .. $size-1){
		print $fd $array->[$i]."\n";
	}
}

sub print_insn_after {
	my $fd = shift;
	my $idx = shift;
	my $array = $insn_array_after{$idx};
	if(not defined $array){
		return;
	}
	my $size = @$array;
	for my $i (0 .. $size-1){
		print $fd $array->[$i]."\n";
	}
}
sub _insert_insn_before {
	my $x = shift;
	my $user_code = shift;
	my $flag = shift;
	if(defined $insn_array_before{$x}){
		_insert_insn($insn_array_before{$x}, $user_code, $flag, $x, 0);
	}else{
		my @insn = ();
		_insert_insn(\@insn, $user_code, $flag, $x, 0);
		$insn_array_before{$x} = [@insn];
	}	


}
sub _insert_insn_after {
	my $x = shift;
	my $user_code = shift;
	my $flag = shift;
	if(defined $insn_array_after{$x}){
		_insert_insn($insn_array_after{$x}, $user_code, $flag, $x, 1);
	}else{
		my @insn = ();
		_insert_insn(\@insn, $user_code, $flag, $x, 1);
		$insn_array_after{$x} = [@insn];
	}	
}


sub sbt_insert_before_insn_v2 {
	my $x = shift;
	my $user_code = shift;
	my $flag = shift;
	if(defined $insn_array[$x-1][INSTRU_FLAG] and $insn_array[$x-1][INSTRU_FLAG] == $I_ADDED){
		
		if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_ORIGINAL){
			#sbt_insert_after_insn_v2($x, $user_code, $flag);
		}
		next;
	}
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_NEVER_TOUCH){
		next;
	}
	_insert_insn_before($x, $user_code, $flag)
}

sub sbt_insert_after_insn_v2 {
	my $x = shift;
	my $user_code = shift;
	my $flag = shift;
	if(defined $insn_array[$x][CALL_FLAG] and 
		(($insn_array[$x][CALL_FLAG] ==$C_CALL) or
		($insn_array[$x][CALL_FLAG] ==$C_ICALL) or
		($insn_array[$x][CALL_FLAG] == $C_INVALID))){
		print "there is no way to add an insn after a call\n";
		return;
	}
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_ADDED){
		return;
	}
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_NEVER_TOUCH){
		return;
	}
	_insert_insn_after($x, $user_code, $flag)
}

sub sbt_insert_after_insn {
	my $x = shift;
	my $user_code = shift;
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_ADDED){
		next;
	}
	if(defined $insn_array[$x][INSTRU_FLAG] and $insn_array[$x][INSTRU_FLAG] == $I_NEVER_TOUCH){
		next;
	}

	if(defined $insn_array[$x][CALL_FLAG] and 
		(($insn_array[$x][CALL_FLAG] ==$C_CALL) or
		($insn_array[$x][CALL_FLAG] ==$C_ICALL) or
		($insn_array[$x][CALL_FLAG] == $C_INVALID))){
		$insn_array[$x+1][INSN_STR] =$user_code."\n".$insn_array[$x+1][INSN_STR];
		next;
	}else{
		#$insn_array[$x][INSN_STR] =$insn_array[$x][INSN_STR]."\nnop\nnop\nnop\nnop\nnop\nnop\nnop\nnop";
		$insn_array[$x][INSN_STR] =$insn_array[$x][INSN_STR]."\n".$user_code;
	}

}
sub only_disasm {
	my $asmdump = shift;
	my $binname = shift;
	my $configfile = shift;
	$global_binname = $binname;
	load_config($configfile);
	#read_icf_check();
	#fix_disasm_issue($asmdump, $binname);
	#analyze_icf_target($global_binname);
	if($disasm_get_icf == 1){
		exit(0);
	}
	#=============================
	disasm_lift($asmdump);
	custom_instrumentation();
}

sub change_lookup_routine {
	if($client_change_lookup_routine ne ""){
		print "entering client: change lookup routine name\n";
		$client_change_lookup_routine->();
	}
}

sub transform {
	my $asmdump = shift;
	my $binname = shift;
	my $configfile = shift;
	$global_binname = $binname;
	load_config($configfile);
	read_icf_check();
	#fix_disasm_issue($asmdump, $binname);
	#analyze_icf_target($global_binname);
	if($disasm_get_icf == 1){
		exit(0);
	}
	#=============================
	disasm_lift($asmdump);
	change_lookup_routine();
	transform_plt();
	transform_plt_v2($global_binname);
	instrument_all_icf();
	analyze_pic_code();
	if($translate_ret_to_lookup == 0){
		transform_insn();
		bundle_instruction();
	}
	transform_jecxz();
	parse_clang_code();
	#print_pos_mapping();
	#print_direct_calls();
	#gen_random_p2align();
	#gen_random_p2align_v2();
	transform_direct_call_to_transparent();
	add_label_aftercall();
	transform_call_to_pushjmp();
	custom_instrumentation();
	check_invalid_branch_target();
	print_insn();
}

sub main {
	my $asmdump = $ARGV[0];
	my $binname = $ARGV[1];
	my $configfile = $ARGV[2];
	transform($asmdump, $binname, $configfile);
}
__PACKAGE__->main unless caller;
