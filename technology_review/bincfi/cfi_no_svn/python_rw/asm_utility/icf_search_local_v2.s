.p2align 6
.macro restore_and_jmp
.ifdef fake_use_ret
	subl	$4, %esp
	movl	%edx, (%esp)
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi

	ret
.else
	movl	%edx,%gs:0x40
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx		
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	jmp 	*%gs:0x40
.endif
.endm
local_search_save:
movl %eax,%gs:0x44
	movl %ecx,%gs:0x48
	movl %edx,%gs:0x4c
	movl %esi,%gs:0x50
	movl %edi,%gs:0x54
	movl (%esp),%edx
	movl %edx, %gs:0x40
	addl $4, %esp

local_search:
movl	%gs:0x40, %esi
	cmpl	$local_insn_end, %esi
	ja	local_search_L9
	cmpl	$local_insn_begin, %esi
	jb	local_search_L8

	subl	$local_insn_begin, %esi
	andl	$insn_mask, %esi
	xor	%edi, %edi
	#jmp	local_search_L4
local_search_L7:
	movl	local_array(,%esi,4), %edx
	cmpl	%gs:0x40, %edx
	je	local_search_L5
	inc	%edi
	addl	%edi, %esi
	andl	$insn_mask, %esi
	cmpl	$size, %edi
	jl	local_search_L7	
	jmp	local_search_invalid_target
	#jmp	local_search_L4
local_search_L5:
	restore_and_jmp
#local_search_L4:
	#calling the log function
local_search_invalid_target:
	call print_log
	xor %eax,%eax
	inc %eax
	movl $0x41,%ebx
	int $0x80

local_search_L8:
	#nop
local_search_L2:
	#xor %eax,%eax
	#inc %eax
	#movl %gs:0x40,%ebx
	#int $0x80
	#hlt
	
	.ifdef ret_to_orig	
	#movl	$insn_end, %edx
	cmpl	$insn_end, %esi
	ja	local_search_invalid_target
	#movl	$insn_begin, %edx
	cmpl	$insn_begin, %esi
	jb	local_search_L9
	#movl	%eax,%gs:0x40
	jmp	binsearch
local_search_L9:
	.endif

	movl	%esi,%gs:0x40
	.ifdef only_local_lookup
	pushl	%eax
	popl	%eax
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx		
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi

	jmp 	*%gs:0x40
	.endif
	.ifdef use_far_jmp
	ljmp	$0x006f,$0x200
	.else
	movl	$0x03000200, %edx
	jmp	*%edx
	.endif
.p2align 5
