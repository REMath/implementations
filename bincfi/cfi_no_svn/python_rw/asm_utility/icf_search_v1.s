	#.comm	array,8000,32
	#.comm	insn_begin,4,4
	#.comm	insn_end,4,4
	#old_addr:	%gs:0x40,4,4
	#.comm	insn_mask,4,4
	#.comm	size,4,4
	#idx	%esi,4,4
	#i	%edi,4,4
binsearch:
movl	%gs:0x40, %edx
	movl	$insn_begin, %eax
	cmpl	%eax, %edx
	jb	binsearch_L8
	movl	%gs:0x40, %edx
	movl	$insn_end, %eax
	cmpl	%eax, %edx
	ja	binsearch_L8
	movl	%gs:0x40, %edx
	movl	$insn_begin, %eax
	subl	%eax, %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %esi
	movl	$0x0, %edi
	jmp	binsearch_L4
binsearch_L7:
	movl	%esi, %eax
	movl	array(,%eax,8), %edx
	movl	%gs:0x40, %eax
	cmpl	%eax, %edx
	je	binsearch_L5
	movl	%edi, %eax
	addl	$1, %eax
	movl	%eax,%edi
	movl	%esi, %eax
	leal	1(%eax), %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %esi
	jmp	binsearch_L4
binsearch_L5:
	movl	%esi, %eax
	movl	$array,%ecx
	add	$0x4,%ecx
	movl	(%ecx,%eax,8), %eax
	#dec	%eax
	movl	%eax,%gs:0x40
	#pushl	%eax
	#popl	%eax
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	jmp 	*%gs:0x40
binsearch_L4:
	movl	%edi, %edx
	movl	$size, %eax
	cmpl	%eax, %edx
	jl	binsearch_L7	
	xor %eax,%eax
	inc %eax
	xor %ebx,%ebx
	mov $0x40, %ebx
	int $0x80
binsearch_L8:
	nop
binsearch_L2:
	movl $local_insn_begin, %eax
	cmpl %eax, %edx
	jb binsearch_L9
	movl $local_insn_end, %eax
	cmpl %eax, %edx
	ja binsearch_L9
	jmp local_search
binsearch_L9:
	.ifdef only_local_lookup
	#pushl	%eax
	#popl	%eax
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	#we don't care about inter-module jmp/call
	jmp 	*%gs:0x40
	.endif
	#here, we go to the global lookup
	.ifdef use_far_jmp
	ljmp	$0x006f,$global_lookup
	.else
	movl  $0x03000000, %eax
	jmp *%eax
	.endif
.p2align 5
