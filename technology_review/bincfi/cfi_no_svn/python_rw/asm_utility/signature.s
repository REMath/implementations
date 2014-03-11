.text
mytext_beginning:
	.byte 0x7f
	.byte 'e'
	.byte 'l'
	.byte 'f'
	.byte elf_type
	.byte abi_version
	.byte reserved2
	.byte reserved3
	.long	binsearch -mytext_beginning
	.long	local_search -mytext_beginning
	.long	plt_search -mytext_beginning
	.long	__my_trap_redirector
	.long   ret_search -mytext_beginning
	.long   ret_local_search -mytext_beginning
log_func_addr:
	#log_func will be patched at runtime
	.long   log_func
	#.long   plt_search
module_name:
	.long module_name_begin
	.skip 0x3c
bip_options:
	.long bip_options_begin
	.skip 0xc
