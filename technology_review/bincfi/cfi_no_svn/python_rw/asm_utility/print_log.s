print_log:
.ifdef is_pic
	call get_pic_base_ecx
	#movl %gs:0x40, %edx
	#addl %ecx, %edx
	movl %ecx, %edx
	addl $module_name, %edx
	addl $log_func_addr, %ecx
	movl (%ecx), %ecx
	#movl %edx, (%esp)
	movl %gs:0x40, %eax
	call *%ecx
	ret
.else
	#movl %gs:0x40, %edx
	#movl %edx, (%esp)
	movl  $module_name, %edx
	movl  $log_func_addr, %ebx
	movl  (%ebx), %ebx
	movl %gs:0x40, %eax #ABI assume eax containing 1st parameter
	call *%ebx
	#hlt
	ret
.endif
