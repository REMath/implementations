#include <stdio.h>
#include <string.h>

#include <beaengine/BeaEngine.h>

int main(int argc, char* argv [])
{
	
	/* ============================= Init datas */
	DISASM MyDisasm;
	int len, i = 0;
	int Error = 0;

	BEA_UNUSED_ARG (argc);
	BEA_UNUSED_ARG (argv);
	/* ============================= Init the Disasm structure (important !)*/
	(void) memset (&MyDisasm, 0, sizeof(DISASM));

	/* ============================= Init EIP */
	MyDisasm.EIP = (UIntPtr) &main;

	/* ============================= Loop for Disasm */
	while ((!Error) && (i<20)){
		len = Disasm(&MyDisasm);
		if (len != UNKNOWN_OPCODE) {
			(void) puts(MyDisasm.CompleteInstr);
			MyDisasm.EIP = MyDisasm.EIP + (UIntPtr)len;
            i++;
		}
		else {
			Error = 1;
		}
	};
	return 0;
}
