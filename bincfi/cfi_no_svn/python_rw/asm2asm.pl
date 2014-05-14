#!/usr/bin/perl -w


my @insn_array;
my %pos_mapping = ();

my $gpr ='\%eax|'.
	'\%ebx|'.
	'\%ecx|'.
	'\%edx|'.
	'\%esi|'.
	'\%edi|'.
	'\%esp|'.
	'\%ebp';


my $opcode_icf = 'call\s|calll\s|jmp\s|jmpl\s';
my $cf_opcode = 'jmp\s|ljmp\s|jmpl\s|call\s|calll\s|je\s|jne\s|jg\s|jge\s|jae\s|jb\s|ja\s|jle\s|jbe\s|jl\s|js\s|jns\s|jp\s|jnp\s';
#instruction array format:
#	['orig_postion','instruction string','raw bytes', 'flag', 'position'(optional)]
#	flag = 0: nothing
#	flag = 1: direct control transfer using call; 'position' is the target

my $asm_filename;
my $bin_filename;
my $cur_section;	
my @cur_insn='';
my $cur_index=0;
my $cur_pos='';
sub add_insn {
	$size = @_;
	#print "size of array is ".$size."\n";
	if( $size == 1){
		$insn_string = $_[0];
		@insn = ($cur_pos, $insn_string, '', 0);
	}elsif( $size == 3){
		$insn_string = $_[0];
		@insn = ($cur_pos, $insn_string,'', $_[1], $_[2]);
	}else{

	}
	return @insn
}
sub main {
	my $insn_addr = '[0-9a-fA-F]{1,8}';
	


	my $filename = shift(@ARGV);
	$bin_filename = shift(@ARGV);
	my $outputfile = 'generated_asm.s';


	open(OUTPUT, '>'.$outputfile) or error("can't open file for err");
	open(ASM, '<'.$filename) or error("can't open input file");
	while(<ASM>){
		chomp;
		if($_ =~ m/^\s*\.file\s\"([^\n]+)\"$/){
			$asm_filename = $1;
			#print $_;
		}elsif( $_ =~ m/^\s*\.([^\n]+)$/){
			$cur_section = $1;
			#print $_;
		}elsif( $_ =~ m/^\_($insn_addr)\:$/){
			$cur_pos=$1;
			#print $_;

		}elsif($_ ne ""){
		#handling instructions
			if($_ =~ m/^\s*($opcode_icf)\s*\*([^\n]+)$/){
				#indirect control flow
				$icf = $1;
				$itarget = $2;
				$insn_str='';
			
				if($icf =~ m/^\s*(call|calll)\s*$/){
					$insn_str = 
					'movl   $1,-0x0c(%esp)'."\n".
					"\tmovl"."\t".'%eax,-0x1c(%esp)'."\n".
					#save clobbered registers
					"\tmovl"."\t".'%ecx,-0x20(%esp)'."\n".
					"\tmovl"."\t".'%edx,-0x24(%esp)'."\n".
					"\tmovl"."\t".$itarget.',%eax'."\n".
					"\tmovl"."\t".'%eax,-0x08(%esp)'."\n".
					"\tcalll\tbinsearch";

				}elsif($icf =~ m/^\s*(jmp|jmpl)\s*$/){
					$insn_str = "\tmovl\t".'$1,-0x08(%esp)'."\n".
					#save clobbered registers
					"\tmovl\t".'%eax,-0x18(%esp)'."\n".
					"\tmovl\t".'%ecx,-0x1c(%esp)'."\n".
					"\tmovl\t".'%edx,-0x20(%esp)'."\n".
					"\tmovl\t".$itarget.',%eax'."\n".
					"\tmovl\t".'%eax,-0x04(%esp)'."\n".
					"\tjmp\tbinsearch";
				}
				#print $_;
				@cur_insn = add_insn($insn_str);
			}elsif($_ =~ m/^\s*($cf_opcode)\s*\_($insn_addr)$/){
				@cur_insn = add_insn($_,1,$2);
				#print $_;
			}else{
				@cur_insn = add_insn($_);
				#all the other instructions
			}
			push @insn_array, [@cur_insn];
			if( $cur_pos ne ''){
				$pos_mapping{$cur_pos} = $cur_index;
				$cur_pos = '';
			}
				
			$cur_index = $cur_index+1;
		}else{
		#unrecognized pattern
			print $_;
		}

		
	}

}
sub print_insn() {
	$size = @insn_array;
	print "array size is ". $size."\n";
	print OUTPUT "\t.file\t".'"'.$asm_filename.'"'."\n";
	print OUTPUT "\t.text\n";

	for $x (0 .. $size-1) {
		if($insn_array[$x][0] ne ''){
			print OUTPUT "_".$insn_array[$x][0].":\n";
		}
		print OUTPUT $insn_array[$x][1]."\n";
		#print OUTPUT $insn_array[$x][2]."\n";
	}


}

sub print_pos_mapping() {
	while (($key, $value) = each %pos_mapping){
		print $key. " ==> ".$value."\n";
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

sub check_get_pc_thunk {
	$target = $_[0];
	$index = $pos_mapping{$target};
	$insn = $insn_array[$index][1];
	$bytes = $insn_array[$index][2];
	if($bytes =~ m/^\s*8b\s1c\s24\s*$/){
		#mov    (%esp),%ebx 8b 1c 24
		$next_insn = $insn_array[$index+1][1];
		$next_bytes = $insn_array[$index+1][2];
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
sub check_call_pop_trampoline {
	$cur_index = $_[0];
	$target = $_[1];
	if($pos_mapping{$target} == ($cur_index + 1)){
	#probably a call-pop trampoline
		print $target.":\tprobably a call-pop tram\n";
		$target_index = $cur_index + 1;
		print "instruction: ".$insn_array[$target_index][1]."\n";
		if($insn_array[$target_index][1] =~ m/^\s*(pop|popl)\s*\%(ebx|ecx)$/){
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
		if(defined($insn_array[$x][3]) and $insn_array[$x][3] eq "1"){
			$target = $insn_array[$x][4];
			if( check_get_pc_thunk($target) == 1){
				$got_addr = get_section_info($bin_filename, ".got.plt","addr");
				print "got.plt address:".$got_addr."\n";
				$next_insn = $insn_array[$x+1][1];
				if($next_insn =~ m/^\s*add\s+([^,]+)\,\s*($gpr)\s*$/){
					print "next instruction:".$next_insn."\n";
					$new_insn = "\tmov\t".'$0x'.$got_addr.",".$2;
					print "new instruction: ".$new_insn."\n";
					$insn_array[$x+1][1] = $new_insn;
					$insn_array[$x+1][2] = "";
				}
			}elsif( check_call_pop_trampoline($x,$target) == 1){
				$got_addr = get_section_info($bin_filename, ".got.plt","addr");
				print "got.plt address:".$got_addr."\n";
				$next_insn = $insn_array[$x+2][1];
				print "next instruction:".$next_insn."\n";
				if($next_insn =~ m/^\s*(add|addl)\s+([^,]+)\,\s*($gpr)\s*$/){
					print "next instruction:".$next_insn."\n";
					$new_insn = "\tmov\t".'$0x'.$got_addr.",".$3;
					print "new instruction: ".$new_insn."\n";
					$insn_array[$x+2][1] = $new_insn;
					$insn_array[$x+2][2] = "";
				}



			}
			#print OUTPUT $insn_array[$x][1]."\n";
		}
	}

}
main();
#print_pos_mapping();
analyze_pic_code();
print_insn();
