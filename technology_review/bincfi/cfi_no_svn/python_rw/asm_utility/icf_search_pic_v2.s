	#.comm	array,8000,32
	#.comm	insn_begin,4,4
	#.comm	insn_end,4,4
	#old_addr:	%gs:0x40,4,4
	#.comm	insn_mask,4,4
	#.comm	size,4,4
	#idx	%esi,4,4
	#i	%edi,4,4
	#code base: %gs:0x3c
binsearch_save:
	movl	%ecx,%gs:0x48
	movl	%edx,%gs:0x4c
	movl	%esi,%gs:0x50
	movl	%edi,%gs:0x54

binsearch:
	movl	%gs:0x40, %esi

	.ifdef pic_change_stack
	movl	%esp, %edx
	movl	%gs:0x5c, %esp
	call	__binsearch_next
__binsearch_next:
	pop	%ecx
	subl	$__binsearch_next, %ecx
	movl	%edx, %esp
	.else
	call	__binsearch_next
__binsearch_next:
	pop	%ecx
	subl	$__binsearch_next, %ecx
	.endif

	subl	%ecx, %esi
	cmpl	$insn_begin, %esi
	jb	binsearch_L9
	cmpl	$insn_end, %esi
	ja	binsearch_L8
	movl	%esi, %gs:0x40
	subl	$insn_begin, %esi
	andl	$insn_mask, %esi
	xor	%edi, %edi
	#jmp	binsearch_L4
binsearch_L7:
	movl	array(%ecx,%esi,8), %edx
	cmpl	%gs:0x40, %edx
	je	binsearch_L5
	inc	%edi
	addl	%edi, %esi
	andl	$insn_mask, %esi
	#jmp	binsearch_L4	
	cmpl	$size, %edi
	jl	binsearch_L7
	jmp	binsearch_invalid_target
binsearch_L5:
	restore_eflags
	movl	array_4(%ecx,%esi,8), %edx
	addl	%ecx,%edx
	movl	%gs:0x50, %esi
	movl	%edx,%gs:0x40
	movl	%gs:0x48, %ecx
	movl	%gs:0x54, %edi
	movl	%gs:0x44, %eax
	movl	%gs:0x4c, %edx
	jmp 	*%gs:0x40
#binsearch_L4:
binsearch_invalid_target:
	call print_log
	xor %eax,%eax
	inc %eax
	xor %ebx,%ebx
	mov $0x40, %ebx
	int $0x80
binsearch_L8:
	#nop
binsearch_L2:
	#xor %eax,%eax
	#inc %eax
	#movl %gs:0x40,%ebx
	
	#int $0x80
	#hlt
	#check if jmp to translated code
	#movl	$local_insn_begin, %eax
	cmpl	$local_insn_begin, %esi
	jb	binsearch_invalid_target
	#movl	$local_insn_end, %eax
	cmpl	$local_insn_end, %esi
	ja	binsearch_L9
	jmp	local_search

binsearch_L9:
	addl	%ecx,%esi
	movl	%esi,%gs:0x40
	.ifdef only_local_lookup
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	#here, we go to the global lookup
	jmp 	*%gs:0x40
	.endif
	.ifdef use_far_jmp
	ljmp	$0x006f,$global_lookup
	.else
	movl	$0x03000000, %edx
	jmp	*%edx
	.endif
.p2align 5
