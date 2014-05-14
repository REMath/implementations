.p2align 5
tram_enter:
#lookup and translate original callee address AND
#change caller to tram_exit
	#movl	(%esp),%ecx
	#movl	%ecx,%gs:0x58

	#saving context
	movl	%eax,%gs:0x44
	movl	%ecx,%gs:0x48
	movl	%edx,%gs:0x4c

	#establishing
	movl	%gs:0x58, %eax
	test	%eax,%eax
	jnz	tram_enter_go
	call	alloc_stack_pages
	movl	%eax,%gs:0x58
	movl	%eax,(%eax)
tram_enter_go:
	movl	%eax,%edx
	movl	(%eax), %eax
	addl	$4,%eax
	#push (esp) onto stack
	movl	(%esp),%ecx
	movl	%ecx,(%eax)
	#update stack pointer
	movl	%eax,(%edx)
	#replace ret address
	movl	$tram_exit,(%esp)
	
	jmp	binsearch

.p2align 5
tram_exit:	
	movl	%eax,%gs:0x44
	movl	%ecx,%gs:0x48
	movl	%edx,%gs:0x4c

	subl	$4,%esp
	movl	%gs:0x58,%eax
	movl	%eax,%edx
	movl	(%eax),%eax
	movl	(%eax),%ecx
	movl	%ecx,(%esp)
	subl	$4,%eax
	movl	%eax,(%edx)
	movl	%gs:0x44,%eax
	movl	%gs:0x48,%ecx
	movl	%gs:0x4c,%edx
	ret
	hlt
.p2align 5

#a stack for callback function return addresses
alloc_stack_pages:
	subl	$48,%esp
	movl	$0, 20(%esp)
	movl	$-1, 16(%esp)
	movl	$34, 12(%esp)
	movl	$3, 8(%esp)
	movl	$8192, 4(%esp)
	movl	$0, (%esp)
	call	my_mmap
	addl	$48,%esp
	ret
.p2align 5
my_mmap:
	push   %ebp
	push   %ebx
	push   %esi
	push   %edi
	mov    0x14(%esp),%ebx
	mov    0x18(%esp),%ecx
	mov    0x1c(%esp),%edx
	mov    0x20(%esp),%esi
	mov    0x24(%esp),%edi
	mov    0x28(%esp),%ebp
	mov    $0xc0,%eax
	int    $0x80
	pop    %edi
	pop    %esi
	pop    %ebx
	pop    %ebp
	ret
#redirect control to tram_enter and save original callee address into gs:0x48
signal_handler:
.p2align 5
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp
	movl	16(%ebp), %eax
	movl	76(%eax),%ecx
	dec	%ecx
	movl	%ecx,%gs:0x40	
	movl	%eax, -4(%ebp)
	movl	$tram_enter, %edx
	movl	-4(%ebp), %eax
	movl	%edx, 76(%eax)
	leave
	ret

.p2align 5

