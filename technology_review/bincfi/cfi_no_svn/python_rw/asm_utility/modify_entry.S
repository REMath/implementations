#define AT_NULL         0               
#define AT_SYSINFO      32
#define AT_ENTRY	9

/* This program tries to modify the entry point of the loader or executable to
 * the corresponding original address. the entry point value in located in
 * the auxiliary vector in the stack */

	/* assumption of stack layout */

	/*	....		*/
	/*	0x00000000	*/
	/*	aux[n].val	*/ 
	/*	aux[n].type	*/
	/*	....		*/
	/*	....		*/
	/*	aux[0].val	*/
	/*	aux[0].type	*/
	/*	0x00000000	*/
	/*	env[n]  	*/
	/*	....		*/
	/*	env[0]  	*/
	/*	0x00000000	*/
	/*	argv[n] 	*/
	/*	....		*/
	/*	argv[0] 	*/
	/*	argc		*/
	/*  	8regs   	*/  /*<== added by our program */
	/*esp-->ret addr    	*/  /*<== added by our program */

	/*bypassing argv[] */
	lea 40(%esp),%edi /*pointing to argv[0]*/
	mov 36(%esp),%eax /*pointing to argc   */
	lea 4(,%eax,4),%eax
	add %eax,%edi
stage1:
	/*bypassing env[] */
	mov (%edi),%eax
	test %eax,%eax
        jz stage2
	add $4,%edi
        jmp stage1
	
stage2:
	/*search auxv[] */
	add $4,%edi
	mov (%edi),%eax
	cmp $AT_ENTRY,%eax
	je ENTRY_FOUND
	add $4,%edi
	test %eax,%eax
	jnz stage2
	
	mov $1,%eax
	xor %ebx,%ebx
	int $0x80  
	
ENTRY_FOUND:
	mov 4(%edi),%eax /*get value into eax */
	mov %eax, %edx
	call ___get_next
___get_next:
	pop %ecx
	sub $___get_next, %ecx
	sub %ecx, %eax
	cmp $local_insn_begin, %eax
	jb donot_touch
	cmp $local_insn_end, %eax
	ja donot_touch
	
	mov $orig_entrypoint, %eax
	add %ecx, %eax
	mov %eax, 4(%edi) /*put the value back */
	jmp ___modify_entry_done
	/*debugging code */
	mov $1,%eax
	xor %ebx,%ebx
	inc %ebx
	inc %ebx
	int $0x80  

donot_touch:
	#push %eax
	#call *(%esp)
	#mov $1,%eax
	#xor %ebx,%ebx
	#inc %ebx
	#int $0x80  

___modify_entry_done:
