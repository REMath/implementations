#define _GNU_SOURCE         /* See feature_test_macros(7) */
#include <stdio.h>
#include <stdlib.h>
#include <dlfcn.h>
#include <link.h>
#include <asm/ldt.h>
#include <sys/mman.h>
#include <elf.h>
#define set_cs( cs ) asm volatile ( "ljmp %0, $0 \n\t" :: "i"(cs) )
#define set_cs1( cs ) asm volatile ( "ljmp %0, $fake_label1 \n\t fake_label1: \n\t" :: "i"(cs) )
#define set_cs2( cs ) asm volatile ( "ljmp %0, $fake_label2 \n\t fake_label2: \n\t" :: "i"(cs) )
#define set_cs1_call( cs ) asm volatile ( "lcall %0, $fake_label1 \n\t fake_label1: \n\t" :: "i"(cs) )
struct  entity{
	void *old_code;
	int old_size;
	void *new_code;
	int new_size;
};
struct runtime_entity{
	int num;
	int reserved1;
	int reserved2;
	int reserved3;
	struct entity ent_array[255];
};
struct ent_page{
	unsigned int base_addr;
	unsigned short  off_search;
	unsigned short  off_local_search;
};
struct signature {
	char sig[4];
	char elf_type;
	char reserved1;
	char reserved2;
	char reserved3;
	unsigned int off_search;
	unsigned int off_local_search;
};
//struct ent_page mapping[1024*1024] __attribute__((aligned(0x1000))) __attribute__((visibility("hidden")));
struct ent_page *mapping;
//void construct_ldt() __attribute__ ((constructor));

//struct runtime_entity runtime  __attribute__((aligned(0x1000))) __attribute__((visibility("hidden")));

struct user_desc ud;



/* This function helps redirecting the control flow to the
 * target code entity. It's a naked function, so it should
 * not use any local data, but thread local variables are
 * allowed 
 * ATTN: DO NOT CHANGE THE FUNCTION NAME */
 __attribute__((naked)) void _G_lookup(){
	#ifdef _CFI_USE_FAR_JMP
	set_cs1(0x0073);
	#endif
	//address:0x03000000
	//use %edx instead of %eax, because %eax contains eflag info
	asm("movl %gs:0x40, %edx");//<== originally, this was %eax
	asm("shrl $12, %edx");
	asm("lea 0x04000000(,%edx,8),%edx");
	asm("movl (%edx), %ecx");
	asm("test %ecx, %ecx");
	asm("jz _invalid_jmp");

	asm("xor %esi, %esi");
	asm("movw 0x4(%edx), %si");
	asm("test %si, %si");

	asm("jz _normal_jmp");
	asm("addl %esi, %ecx");
	asm("jmp *%ecx");

	asm("_normal_jmp:\n");
	asm("movl %gs:0x44, %eax");
	asm("movl %gs:0x48, %ecx");
	asm("movl %gs:0x4c, %edx");
	asm("movl %gs:0x50, %esi");
	asm("movl %gs:0x54, %edi");
	asm("jmp *%gs:0x40");
	asm("_invalid_jmp:");
	asm("xor %eax, %eax");
	asm("movl $0x42, %ebx");
	asm("inc %eax");
	asm("int $0x80");
}

 __attribute__((naked)) void _G_lookup_local(){
	asm(".p2align 9");
	#ifdef _CFI_USE_FAR_JMP
	set_cs2(0x0073);
	#endif
	//address:0x03000200
	//use %edx instead of %eax, because %eax contains eflag info
	asm("movl %gs:0x40, %edx");//<== originally, this was %eax
	asm("shrl $12, %edx");
	asm("lea 0x04000000(,%edx,8),%edx");
	asm("movl (%edx), %ecx");
	asm("test %ecx, %ecx");
	asm("jz _invalid_jmp2");

	asm("xor %esi, %esi");
	asm("movw 0x6(%edx), %si");
	asm("test %si, %si");

	asm("jz _normal_jmp2");
	asm("addl %esi, %ecx");
	asm("jmp *%ecx");

	asm("_normal_jmp2:\n");
	//asm("addl $4, %esp");
	asm("movl %gs:0x44, %eax");
	asm("movl %gs:0x48, %ecx");
	asm("movl %gs:0x4c, %edx");	
	asm("movl %gs:0x50, %esi");
	asm("movl %gs:0x54, %edi");
	asm("jmp *%gs:0x40");
	asm("_invalid_jmp2:");
	asm("xor %eax, %eax");
	asm("movl $0x42, %ebx");
	asm("inc %eax");
	asm("int $0x80");
}
 __attribute__((naked)) void _G_lookup_ret(){
	asm(".p2align 9");
	#ifdef _CFI_USE_FAR_JMP
	set_cs1(0x0073);
	#endif
	//address:0x03000400
	asm("movl %gs:0x40, %eax");
	asm("shrl $12, %eax");
	asm("lea 0x04000000(,%eax,8),%eax");
	asm("movl (%eax), %ecx");
	asm("test %ecx, %ecx");
	asm("jz _invalid_jmp");
	asm("movw 0x4(%eax), %dx");
	asm("test %dx, %dx");
	asm("jz _normal_jmp");
	//searching ret_search trampoline
	asm("movl 0x18(%ecx), %eax");
	asm("test %eax, %eax");	
	asm("jz _G_lookup_local");//target code does not support ret enforce
	//asm("cmpl $0x90909090, %eax");
	//asm("je _G_lookup_local");//target code does not support ret enforce
	//asm("cmpw $0x9090, %ax");
	//asm("je _G_lookup_local");//target code does not support ret enforce
	//asm("cmp $0x90, %al");
	//asm("je _G_lookup_local");//target code does not support ret enforce
	//asm("xor %edx,%edx");
	//asm("rol $8,%eax");
	//asm("mov %al, %dl");
	//asm("rol $8,%eax");
	//a/sm("mov %al, %dh");
	asm("addl %eax, %ecx");
	asm("jmp *%ecx");
}
 __attribute__((naked)) void _G_lookup_ret_local(){
	asm(".p2align 9");
	#ifdef _CFI_USE_FAR_JMP
	set_cs1(0x0073);
	#endif
	//address:0x03000600
	asm("movl %gs:0x40, %eax");
	asm("shrl $12, %eax");
	//asm("andl $0x000fffff,%eax");
	asm("lea 0x04000000(,%eax,8),%eax");
	asm("movl (%eax), %ecx");
	asm("test %ecx, %ecx");
	asm("jz _invalid_jmp");
	asm("movw 0x6(%eax), %dx");
	asm("test %dx, %dx");
	asm("jz _normal_jmp2");
	//searching ret_search trampoline
	asm("movl 0x1c(%ecx), %eax");
	asm("test %eax, %eax");	
	asm("jz _G_lookup_local");//target code does not support ret enforce
	asm("cmpl $0x90909090, %eax");
	asm("je _G_lookup_local");//target code does not support ret enforce
	asm("cmpw $0x9090, %ax");
	asm("je _G_lookup_local");//target code does not support ret enforce
	//asm("cmp $0x90, %al");
	//asm("je _G_lookup_local");//target code does not support ret enforce
	//asm("xor %edx,%edx");
	//asm("rol $8,%eax");
	//asm("mov %al, %dl");
	//asm("rol $8,%eax");
	//a/sm("mov %al, %dh");
	asm("addl %eax, %ecx");
	asm("jmp *%ecx");
	//assuming that offset is always two bytes
	//asm("xor %edx,%edx");
	//asm("rol $8,%eax");
	//asm("mov %al, %dl");
	//asm("rol $8,%eax");
	//asm("mov %al, %dh");
	//asm("shl $16,%edx");
	//asm("add %edx, %ecx");
}
 __attribute__((naked)) void _G_lookup_plt(){
	asm(".p2align 9");
	#ifdef _CFI_USE_FAR_JMP
	set_cs1(0x0073);
	#endif
	//address:0x03000800
	asm("movl %gs:0x40, %edx");
	asm("shrl $12, %edx");
	asm("lea 0x04000000(,%edx,8),%edx");
	asm("movl (%edx), %ecx");
	asm("test %ecx, %ecx");
	asm("jz _invalid_jmp");
	asm("movw 0x4(%edx), %dx");
	asm("test %dx, %dx");
	asm("jz _normal_jmp");
	//searching ret_search trampoline
	asm("movl 0x10(%ecx), %edx");
	//asm("test %edx, %edx");	
	asm("cmpl $0x10, %edx");//hacking, if plt_search is not defined, it is 0x10
	asm("jz _G_lookup");//target code does not support plt enforce
	asm("addl %edx, %ecx");
	asm("jmp *%ecx");
}
int main()
{
	return 0;
}
