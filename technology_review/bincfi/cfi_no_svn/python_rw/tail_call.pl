#!/usr/bin/perl -w
use Switch;
use Fcntl;
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

#conditional control flow
my $ccf_opcode = 'jb\s|jnae\s|jc\s|jbe\s|jna\s|jcxz\s|jecxz\s|jl\s|jnge\s|jle\s|jng\s|jnb\s|jae\s|jnc\s|jnbe\s|ja\s|jnl\s|jge\s|jnle\s|jg\s|jno\s|jnp\s|jpo\s|jns\s|jnz\s|jne\s|jo\s|jp\s|jpe\s|js\s|jz\s|je\s';

my $ujmp_opcode = 'jmp\s|jmpl\s';
my $ucall_opcode = 'call\s|calll\s';

my $insn_addr = '[0-9a-fA-F]{1,8}';
my $target = '[\$\%\w\d\_\@\-\.\+]+';

my %pos_mapping = ();
my @insn_array;
my %ccf_source = (); #source address is the key; dest address is the value; ccf: conditional control flow
my %ucf_source = (); #source address is the key; source address is the value; ucf: unconditional control flow (excluding call)
my %cf_dest = ();   #destination address of direct control flow is the key;
my %ijmp_source = (); 
my %ret_source = ();

my %icf_target = ();
my %touched = (); #indicate whether the insn is touched

sub parse_disasm_insn {
	my $filename = $_[0];
	my $INSN;
	my $index = 1;
	my @insn;
	#1st element is empty
	push @insn_array ,[];
	open $INSN, $filename or print "cannot open file:$filename\n" and die $!;
	while(<$INSN>){
		if($_ =~ m/^\s*([0-9a-f]+):\s+([^\t]+)\t([^\n]+)$/){
			#print $_;
			my $cur_pos = $1;
			my $raw_bytes = $2;
			my $insn_str = $3;
			$touched{$cur_pos} = 0;
			if($insn_str =~ m/^\s*lock/){
				@insn = ($cur_pos, "f0", "lock");
				push @insn_array, [@insn];
				$pos_mapping{hex($cur_pos)} = $index;
				#print "$cur_pos\t".hex($cur_pos)."\n";
				$index = $index +1;
				$cur_pos = sprintf("%x",hex($cur_pos)+1);
				$raw_bytes =~ s/^\s*f0\s*//;
				$insn_str =~ s/lock[l]*\s*//; 
				$touched{$cur_pos} = 0;
			}

			if($insn_str =~ m/^\s*($ccf_opcode)\s+($insn_addr)\s+\<($target)\>\s*$/){
				$dest = $2;
				$ccf_source{$cur_pos} = $dest;
				$cf_dest{$dest} = $cur_pos;
				#print $_;	
			}elsif($insn_str =~ m/^\s*($ujmp_opcode)\s+($insn_addr)\s+\<($target)\>\s*$/){
				$dest = $2;
				$ucf_source{$cur_pos} = $dest;
				$cf_dest{$dest} = $cur_pos;
				#print $_;
			}elsif($insn_str =~ m/^\s*jmp[l]*\s+\*/){
				$ijmp_source{$cur_pos} = 0;
			}elsif($insn_str =~ m/^\s*repz\s+(ret|retl)\s*$/){
				$ret_source{$cur_pos} = 0;
			}elsif($insn_str =~ m/^\s*(ret|retl)\s*$/){
				$ret_source{$cur_pos} = 0;
			}
			@insn = ($cur_pos, $raw_bytes, $insn_str);
			push @insn_array, [@insn];
			$pos_mapping{hex($cur_pos)} = $index;
			#print "$cur_pos\t".hex($cur_pos)."\n";
			$index = $index +1;
		}
	}
}

sub parse_icf_target {
	my $filename = $_[0];
	open $TGT, $filename or print "cannot open file:$filename\n" and die $!;
	while(<$TGT>){
		if($_ =~ m/^([0-9a-f]+)$/){
			$icf_target{$1} = 1;
		}
	}
}

sub touch_insn {
	$cur = $_[0];
	if(not defined $touched{$cur}){
		print "pos: $cur is not defined in \%touched\n";
		exit(0);
	}
	if($touched{$cur} == 1){
		return;
	}else{
		$touched{$cur} = 1;
	}
	my $insn_str = $insn_array[$pos_mapping{hex($cur)}][2];
	my $cur_pos = $insn_array[$pos_mapping{hex($cur)}][0];
	#print "cur insn is :$cur\t$insn_str\n";
	if(defined $ucf_source{$cur}){
		touch_insn($ucf_source{$cur});
		return;
	}elsif(defined $ccf_source{$cur}){
		touch_insn($ccf_source{$cur});

	}elsif(defined $ijmp_source{$cur}){
		return;		
	}elsif(defined $ret_source{$cur}){
		$ret_source{$cur} = 1;
		return;
	}
	
	$idx = $pos_mapping{hex($cur_pos)};
	#print "idx:$idx\n";
	touch_insn($insn_array[$idx+1][0]);
	return;
}
my $bin = shift @ARGV;
my $disam_file = "$bin/log";
my $icf_file = "$bin/icf_target_addr";
parse_disasm_insn($disam_file);

system("../gadget_checking/get_icf_info.pl $icf_file noret_noexported >/tmp/icf_noret");
parse_icf_target("/tmp/icf_noret");
#foreach $x  ( keys(%icf_target)){print "$x\n";}

foreach $icf (keys (%icf_target)){
	touch_insn($icf);
}

#checking results
$ret_counted  =0;
$ret_total = keys(%ret_source);
foreach $r (keys (%ret_source)){
	if($ret_source{$r} == 0){
		$ret_counted += 1;
	}
}
print "$ret_counted,$ret_total\n";
