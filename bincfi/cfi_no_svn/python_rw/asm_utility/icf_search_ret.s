	#.comm	array,8000,32
	#.comm	insn_begin,4,4
	#.comm	insn_end,4,4
	#old_addr:	%gs:0x40,4,4
	#.comm	insn_mask,4,4
	#.comm	size,4,4
	#idx	%esi,4,4
	#i	%edi,4,4
.macro my_restore_and_jmp
.ifdef use_ret
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

binsearch_save:
	movl %eax,%gs:0x44
	movl %ecx,%gs:0x48
	movl %edx,%gs:0x4c
	movl %esi,%gs:0x50
	movl %edi,%gs:0x54
	movl (%esp),%edx
	movl %edx, %gs:0x40
	addl $4, %esp
binsearch_entry:
#include "binsearch_instrument_entry.h"

binsearch:
movl	%gs:0x40, %esi
	cmpl	$insn_begin, %esi
	jb	binsearch_L9
	cmpl	$insn_end, %esi
	ja	binsearch_L8
#include "binsearch_instrument_pre.h"
	subl	$insn_begin, %esi
	andl	$insn_mask, %esi
	xor	%edi, %edi
	#jmp	binsearch_L4
binsearch_L7:
	movl	array(,%esi,8), %edx
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
	movl	array_4(,%esi,8), %edx
#include "binsearch_instrument_post.h"
	my_restore_and_jmp
#binsearch_L4:
binsearch_invalid_target:
	call print_log
	xor %eax,%eax
	inc %eax
	xor %ebx,%ebx
	mov $0x41, %ebx
	int $0x80

	#xor %eax,%eax
	#inc %eax
	#xor %ebx,%ebx
	#mov $0x40, %ebx
	#int $0x80
binsearch_L8:
	#nop
binsearch_L2:
	cmpl $local_insn_begin, %esi
	jb binsearch_invalid_target
	cmpl $local_insn_end, %esi
	ja binsearch_L9
	jmp local_search
binsearch_L9:
	.ifdef only_local_lookup
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
	movl  $0x03000000, %edx
	jmp *%edx
	.endif
.p2align 4
