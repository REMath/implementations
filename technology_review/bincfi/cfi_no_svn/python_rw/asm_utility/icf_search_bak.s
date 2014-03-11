	#.comm	array,8000,32
	#.comm	insn_begin,4,4
	#.comm	insn_end,4,4
	#old_addr:	%gs:0x40,4,4
	#.comm	insn_mask,4,4
	#.comm	size,4,4
	#idx	%gs:0x50,4,4
	#i	%gs:0x54,4,4
binsearch:
movl	%gs:0x40, %edx
	movl	$insn_begin, %eax
	cmpl	%eax, %edx
	jl	.L8
	movl	%gs:0x40, %edx
	movl	$insn_end, %eax
	cmpl	%eax, %edx
	jg	.L8
	movl	%gs:0x40, %edx
	movl	$insn_begin, %eax
	subl	%eax, %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %gs:0x50
	movl	$0x0, %gs:0x54
	jmp	.L4
.L7:
	movl	%gs:0x50, %eax
	movl	array(,%eax,8), %edx
	movl	%gs:0x40, %eax
	cmpl	%eax, %edx
	je	.L5
	movl	%gs:0x54, %eax
	addl	$1, %eax
	movl	%eax,%gs:0x54
	movl	%gs:0x50, %eax
	leal	1(%eax), %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %gs:0x50
	jmp	.L4
.L5:
	movl	%gs:0x50, %eax
	movl	array+4(,%eax,8), %eax
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	jmp 	*%gs:0x40
.L4:
	movl	%gs:0x54, %edx
	movl	$size, %eax
	cmpl	%eax, %edx
	jl	.L7
.L8:
	nop
.L2:
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	jmp 	*%gs:0x40
