#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <beaengine/BeaEngine.h>

int main(int argc, char* argv[])
{
	/* ============================= Init datas */
	DISASM MyDisasm;
	int len;
	int Error = 0;
	UInt64 EndCodeSection = 0x401020;

	BEA_UNUSED_ARG (argc);
	BEA_UNUSED_ARG (argv);	
	/* ============================= Init the Disasm structure (important !)*/
	(void) memset (&MyDisasm, 0, sizeof(DISASM));

	/* ============================= Init EIP */
	MyDisasm.EIP = 0x401000;

	/* ============================= Loop for Disasm */
	while (!Error){
		/* ============================= Fix SecurityBlock */
		MyDisasm.SecurityBlock = (UIntPtr)EndCodeSection - (UIntPtr)MyDisasm.EIP;

		len = Disasm(&MyDisasm);
		if (len == OUT_OF_BLOCK) {
			(void) printf("disasm engine is not allowed to read more memory \n");
			Error = 1;
		}
		else if (len == UNKNOWN_OPCODE) {
			(void) printf("unknown opcode");
			Error = 1;
		}
		else {
			(void) puts(MyDisasm.CompleteInstr);
			MyDisasm.EIP = MyDisasm.EIP + (UIntPtr)len;
			if (MyDisasm.EIP >= EndCodeSection) {
				(void) printf("End of buffer reached ! \n");
				Error = 1;
			}
		}
	};
	return 0;
}
