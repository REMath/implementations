#!/usr/bin/perl -w
use Switch;
my $cur_pos = 0;
my $tapping = 0;
my $pre_pos = "";
my $objname = "";
my $cur_func = "";
my $cur_abi = "";
my $cur_section = "";

my $cur_bytes = "";
my $cur_index = 0;
my $cur_insn = "";

#the pos of the 1st insn in .text
my $entry_begin = 0;
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

#instruction array format:
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=0']
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=1', 'position'(optional)]
#	['orig_position','instruction string','raw bytes', 'instru_flag=0','branch_flag=1', 'position'(optional), callflag=1]
#	instru_flag = 0: an original instruction (not instrumented)
#	instru_flag = 1: an instrumented instruction (indicates, the raw_bytes field is meaningless except the length)
#	branch_flag = 0 or undefined: normal instructions
#	branch_flag = 1: direct control transfer using call; 'position' is the target
#	branch_flag = 1 & callflag=1: direct control transfer using call; 'position' is the target
my @insn_array;
my %pos_mapping = ();


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


sub instrument_indirect_control {	
	#handle indirect control transfer
	$icf = $1;
	$itarget = $2;
	$cur_insn = "";
	if($icf =~ m/^\s*(call|calll)\s*$/){
		#matching a indirect call using register
		#print "indirect call:".$cur_insn."\n";
			$cur_insn = 
				'movl   $1,%gs:0x3c'."\n".	
				'movl	%eax,%gs:0x44'."\n".#save caller save register
				'movl	%edx,%gs:0x4c'."\n".
				"movl   ".$itarget.',%eax'."\n".
				'.p2align '.BUNDLE_ALIGN."\n".
				'.byte 0x8d,0xbc,0x27,0x00,0x00,0x00,0x00'."\n".
				'.byte 0x8d,0xb4,0x26,0x00,0x00,0x00,0x00'."\n".
				'.byte 0x8d,0xbc,0x27,0x00,0x00,0x00,0x00'."\n".
				'movl   %eax,%gs:0x40'."\n".
				'calll  binsearch';
			#print "unhandled indirect call:".$cur_insn."\n";
		
	}elsif($icf =~ m/^\s*(jmp|jmpl)\s*$/){
		#matching a indirect jump using register
		#print "indirect jmp:".$cur_insn."\n";	
		$cur_insn = 'movl   $1,%gs:0x3c'."\n".
				'movl	%eax,%gs:0x44'."\n".#save caller save register
				'movl	%edx,%gs:0x4c'."\n".				
				'movl   '.$itarget.',%eax'."\n".
				'.p2align '.BUNDLE_ALIGN."\n".
				'movl   %eax,%gs:0x40'."\n".
				'jmp   binsearch';
			#print "unhandled indirect jump:".$cur_insn."\n";
	}
	return $cur_insn;
}

sub main {
	my $insn_addr = '[0-9a-fA-F]{1,8}';
	my $insn_bin = '([0-9a-fA-F]{2}\s)+';
	#this following is a full list of (un)conditional jump/call insn opcodes
	#href: http://ref.x86asm.net/coder32-abc.html#J
	my $addr = '0x[0-9a-fA-F]{1,8}|[0-9a-fA-F]{1,8}';
	my $no_0x_addr = '[0-9a-fA-F]{1,8}';

	my $filename = shift(@ARGV);
	#my $output = shift(@ARGV);	
	my $testfile = 'test.s';
	my $outputfile = 'generated_asm.s';

	my $objfile = '[\w\d\.\_\-\+\/\@]+';
	my $abi = '[\w\d\-]+';
	my $secname = '[\w\d\.\_\-\@]+';

	my $func_entry = '[0-9a-fA-F]{8}';
	my $target = '[\$\%\w\d\_\@\-\.\+]+';
	#open(OUTPUT,'>'.$output) or error("can't open output file");



	open(TEST, '>'.$testfile) or error("can't open file for testing");
	open(OUTPUT, '>'.$outputfile) or error("can't open file for err");
	open(ASM, '<'.$filename) or error("can't open input file");
	while(<ASM>){
		if( $_ =~ m/^\s*([^\:]+)\:\t([^\t]+)\t([^\n]+)$/){
		#processing valid instructions
			$cur_pos = $1;
			$cur_bytes = $2;
			$cur_insn = $3;
			if($cur_bytes eq ""){
				print "raw bytes is empty, exit";
				exit(1);
			}
			#$cur_bytes = "0x".$cur_bytes;
			#$cur_bytes =~ s/ /,0x/g;
			#print "raw bytes is ".$cur_bytes."\n";
			#print "insn is ".$cur_insn."\n";
			#print a label
			print TEST "_".$cur_pos.":\n";

			if($cur_insn =~ m/^\s*($cf_opcode)\s+($insn_addr)\s+\<($target)\>\s*$/){
				#handle direct control transfer
				print TEST $1.' _'.$2."\n";
				$cur_opcode = $1;
				$cur_target = $2;
				if($cur_insn =~ m/^\s*($opcode_icf)\s+($no_0x_addr)\s+\<($target)\>\s*$/){
					#matching a direct call (to capture PIC call)
					$_opcode = $1;
					$_target = $2;
					if( $_opcode =~ m/^call|calll\s*$/){
						@insn = ($cur_pos, $_opcode.' _'.$_target, trim($cur_bytes), 0 ,"1", $_target, 1);
					}else{
						@insn = ($cur_pos, $_opcode.' _'.$_target, trim($cur_bytes), 0, "1", $_target);
					}
					push @insn_array, [@insn];
	
				}else{
					@insn = ($cur_pos, $cur_opcode.' _'.$cur_target, trim($cur_bytes), 0, "1", $cur_target);
					push @insn_array, [@insn];
					#print $cur_insn."\n";
				}
			}elsif($cur_insn =~ m/^\s*($opcode_icf)\s*\*([^\n]+)$/){
				#handle indirect control transfer
				if($cur_section eq '.plt'){
					#do not instrument the icf in .plt section
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),0);
				}else{
					$_insn = instrument_indirect_control($icf,$itarget);
					@insn = ($cur_pos, $_insn, "", 1);
				}
				push @insn_array, [@insn];

			}elsif($cur_insn ne ""){
			#handl all the other instructions
				if($cur_insn =~ m/^\s*lea\s+0x0\(\%esi\,\%eiz\,1\)\,\%esi$/){
					print TEST "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n";
					@insn = ($cur_pos, "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop", trim($cur_bytes), 0);
					push @insn_array, [@insn];				
				}
				elsif($cur_insn =~ m/^\s*lea\s+0x0\(\%edi\,\%eiz\,1\)\,\%edi$/){
					print TEST "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop\n";	
					@insn = ($cur_pos, "nop\nnop\nnop\nnop\nnop\nnop\nnop\nnop",trim($cur_bytes), 0);
					push @insn_array, [@insn];
				}elsif($cur_insn =~ m/^\s*repz\s+(ret|retl)\s*$/){
					#handling repz ret
					#print "handling illegal instruction:".$cur_insn."\n";
					$cur_opcode = "ret";
					$cur_insn = '.byte 0xf3'."\n".$cur_opcode;
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes), 0, "2");
					push @insn_array, [@insn];
				
				}elsif($cur_insn =~ m/^\s*(ret|retl)\s*$/){
					#handling ret
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),0, "2");
					push @insn_array, [@insn];
				}else{
					print TEST $cur_insn."\n";
					#push insn into array
					if($cur_bytes eq ""){
						print "raw bytes is empty\n";
						print "insn: ".$cur_insn."\n";
					}
					@insn = ($cur_pos, $cur_insn, trim($cur_bytes),0);
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
			print TEST "\t.text\n";	
			$entry_begin = get_entry_addr($objname);
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
sub transform_insn_to_rawbytes {

}

sub print_direct_calls() {
	$size = @insn_array;
	print "array size is ". $size."\n";
	for $x (0 .. $size-1) {
		if(defined($insn_array[$x][BRAN_TARGET]) and $insn_array[$x][BRAN_TARGET] eq "1"){
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
	print OUTPUT "\t.text\n";

	for $x (0 .. $size-1) {
		print OUTPUT "_".$insn_array[$x][ORIG_POS].":\n";
		print OUTPUT "\t".$insn_array[$x][INSN_STR]."\n";
		#print OUTPUT $insn_array[$x][RAW_BYTES]."\n";
	}

}
sub check_get_pc_thunk {
	$target = $_[0];
	$index = $pos_mapping{$target};
	$insn = $insn_array[$index][INSN_STR];
	$bytes = $insn_array[$index][RAW_BYTES];
	if(($bytes =~ m/^\s*8b\s1c\s24\s*$/) or
		#mov    (%esp),%ebx 8b 1c 24
		($bytes =~ m/^\s*8b\s0c\s24\s*$/)){
		#mov    (%esp,%ecx
		$next_insn = $insn_array[$index+1][INSN_STR];
		$next_bytes = $insn_array[$index+1][RAW_BYTES];
		if( $next_bytes =~ m/^\s*c3\s*$/){
			#ret     c3
			print "call target:".$insn." ".$bytes."\t".$next_insn." ".$next_bytes."\n";
			return 1;
		}else{
			return 0;
		}
	}else{
		#print "call target:".$insn." ".$bytes."\n";
		return 0;
	}
}

sub get_entry_addr {
	$binname = $_[0];
	$cmd = "readelf -h ".$binname." |";
	open(BIN, $cmd) or die("cannot open file".$binname);
	while(<BIN>){
		if($_ =~ m/^\s*Entry point address:\s*0x([^\n]+)$/){
			$_entry_begin = $1;
			return $_entry_begin; 
		}	
	}
}

sub get_section_info {
	$binname = $_[0];
	$secname = $_[1];
	$info = $_[2];
	$cmd = "readelf -S ".$binname." |";
	open(BIN, $cmd) or die("cannot open file".$binname);
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
		}
		else{
			;#print $_;
		}
	}

}

sub check_call_pop_trampoline {
	$cur_index = $_[0];
	$target = $_[1];
	if($pos_mapping{$target} == ($cur_index + 1)){
	#probably a call-pop trampoline
		print $target.":\tprobably a call-pop tram\n";
		$target_index = $cur_index + 1;
		print "instruction: ".$insn_array[$target_index][INSN_STR]."\n";
		if($insn_array[$target_index][INSN_STR] =~ m/^\s*(pop|popl)\s*\%(ebx|ecx)$/){
			#now, for sure it is
			#print $target.":\tfor sure,it is a call-pop tram\n";
	
			return 1;
		}
	}
	return 0;
}
#parameter1: target address
sub analyze_pic_code() {
	$size = @insn_array;
	for $x (0 .. $size-1) {
		if(defined($insn_array[$x][BRANCH]) and $insn_array[$x][BRANCH] eq "1"){
			$target = $insn_array[$x][BRAN_TARGET];
			if( check_get_pc_thunk($target) == 1){
				$got_addr = get_section_info($objname, ".got.plt","addr");
				print "got.plt address:".$got_addr."\n";
				$next_insn = $insn_array[$x+1][INSN_STR];
				if($next_insn =~ m/^\s*add\s+([^,]+)\,($gpr)\s*$/){
					print "next instruction:".$next_insn."\n";
					$new_insn = 'mov   $0x'.$got_addr.",".$2;
					print "new instruction: ".$new_insn."\n";
					$insn_array[$x+1][INSN_STR] = $new_insn;
					$insn_array[$x+1][RAW_BYTES] = "00 00 00 00 00";
					$insn_array[$x+1][INSTRU_FLAG] = 1;
				}
			}elsif( check_call_pop_trampoline($x,$target) == 1){
				$got_addr = get_section_info($objname, ".got.plt","addr");
				print "got.plt address:".$got_addr."\n";
				$next_insn = $insn_array[$x+2][INSN_STR];
				print "next instruction:".$next_insn."\n";
				if($next_insn =~ m/^\s*(add|addl)\s+([^,]+)\,\s*($gpr)\s*$/){
					print "next instruction:".$next_insn."\n";
					$new_insn = "\tmov\t".'$0x'.$got_addr.",".$3;
					print "new instruction: ".$new_insn."\n";
					$insn_array[$x+2][INSN_STR] = $new_insn;

					#5 zeros indicates the length is 5 bytes, as expected in gcc-4.6
					#in the future, it subjects to changes in gcc
					$insn_array[$x+2][RAW_BYTES] = "00 00 00 00 00";#
					$insn_array[$x+2][INSTRU_FLAG] = 1;
				}			#print OUTPUT $insn_array[$x][INSN_STR]."\n";
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

sub transform_direct_branch {
	$x = $_[0];
	$insn_str = $insn_array[$x][INSN_STR];
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
				exit(1);
			}

		}
	}else{
		print "error recognizing a direct branch insn!! \n";
		exit(1);
	}
}


sub transform_insn {
	print "This routine will rewrite instructions" ."\n";
	$size = @insn_array;
	for $x (0 .. $size-1) {
		if($insn_array[$x][INSTRU_FLAG] == 0 and (not defined $insn_array[$x][BRANCH])){
		#check if it is a normal instruction
			#print "this is a normal instruction\n";
			$insn_str = $insn_array[$x][RAW_BYTES];
			$insn_str =~ s/ /,0x/g;
			$insn_str = '.byte 0x'.$insn_str;
			$insn_array[$x][INSN_STR] = $insn_str;	
		}elsif($insn_array[$x][INSTRU_FLAG] == 0 and ($insn_array[$x][BRANCH] == "1")){
		#handling a direct call instruction
			transform_direct_branch($x);
		
		}elsif($insn_array[$x][INSTRU_FLAG] == 0 and ($insn_array[$x][BRANCH] == "1")){
		#handing a ret instruction
			$insn_array[$x][INSN_STR] = 'andl $0x07ffffe0,(esp)'."\n".$insn_array[$x][INSN_STR];
			$insn_array[$x][RAW_BYTES] = '81 24 24 00 00 00 00 '.$insn_array[$x][RAW_BYTES];
		}
	}
}

#This routine (pass) will bundle instructions into 32-byte blocks
#Note: this routine will make the position mapping useless, so any passes
#that will use this mapping should be done before this routine.
sub bundle_instruction(){
	$size = @insn_array;
	$cur_bsize = 0;
	print "This routine will bundle the instructions" ."\n";
	print "bundle size is: ".BUNDLE_SIZE."\n";
	print "entry begin is".$entry_begin."\n";
	for $x (0 .. $size-1) {
		$len = insn_len($insn_array[$x][RAW_BYTES]);
		#print "length:".$len."\t";
		if($len != int($len)){
			print "error in instruction length, not an integer\n";
			print "original bytes: ".$insn_array[$x][RAW_BYTES]."\n";
			exit(1);
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
		elsif(defined $insn_array[$x][CALL_FLAG] and $insn_array[$x][CALL_FLAG] == 1){
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

#		if($insn_array[$x][BRANCH] == 2){
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
	$size = @insn_array;
	$threshold =  1;
	$entry_index = $pos_mapping{$entry_begin};
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
	$size = @insn_array;
	$threshold =  1;
	$entry_index = $pos_mapping{$entry_begin};
	print "This routine will randomly generate p2align pesudo instruction" ."\n";
	print "bundle size is: ".BUNDLE_SIZE."\n";
	print "text begin is".$entry_begin."\n";
	for $x (0 .. $size-1) {
		$rand_num = rand();

		if($x >= $entry_index and $x < $entry_index + 30){
			next;
		}
		if($rand_num < $threshold){
			$insn_array[$x][INSN_STR] .="\n".'.p2align '.BUNDLE_ALIGN;
		}
	}
}

main();
#print get_section_info("./ls",".got.plt", "addr")."\n";
analyze_pic_code();
transform_insn();
bundle_instruction();
#print_pos_mapping();
#print_direct_calls();
#gen_random_p2align();
#gen_random_p2align_v2();
print_insn();
