#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <beaengine/BeaEngine.h>
/* ============================= Init datas */
DISASM MyDisasm;
int len;
int Error = 0;
void *pBuffer;

typedef int  (*MainPtr) (int, char*[]);
MainPtr pSourceCode;


/* ======================================================= 
 Disassemble code in the specified buffer using the 
 correct VA					
*/

/*========================================================*/

static void DisassembleCode(char *StartCodeSection, char *EndCodeSection, 
			    MainPtr Virtual_Address)
{

  Error = 0;

  /* ============================= Init EIP */
  MyDisasm.EIP = (UIntPtr) StartCodeSection;
  /* ============================= Init VirtualAddr */
  MyDisasm.VirtualAddr = (UIntPtr) Virtual_Address;

  /* ============================= set IA-32 architecture */
  MyDisasm.Archi = 0;
  /* ============================= Loop for Disasm */
  while ( !Error){
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
      /* ============================= Make a filter on Instruction */
      if (MyDisasm.Instruction.BranchType != 0) {
	(void) printf("Branch-Instruction : ");
	(void) printf("%.8X %s\n",(int) MyDisasm.VirtualAddr, (char*)&MyDisasm.CompleteInstr);
      }
      else if ((MyDisasm.Argument1.AccessMode == READ) && (MyDisasm.Argument2.AccessMode == READ)) {
	(void) printf("CompareInstruction : ");
	(void) printf("%.8X %s\n",(int) MyDisasm.VirtualAddr, (char*)&MyDisasm.CompleteInstr);
      }
      MyDisasm.EIP = MyDisasm.EIP + (UIntPtr)len;
      MyDisasm.VirtualAddr = MyDisasm.VirtualAddr + (UIntPtr)len;
      if (MyDisasm.EIP >= (UIntPtr) EndCodeSection) {
	(void) printf("End of buffer reached ! \n");
	Error = 1;
      }
    }
  };
  return;
}

/**
 * MAIN
 */
int main(int argc, char* argv[])
{
  BEA_UNUSED_ARG (argc);
  BEA_UNUSED_ARG (argv);
  /* ======== Init the Disasm structure (important !)*/
  (void) memset (&MyDisasm, 0, sizeof(DISASM));


  pSourceCode =  main;
  pBuffer = malloc(0x600);
  /* ============================ Let's NOP the buffer */
  (void) memset (pBuffer, 0x90, 0x600);
  /* ============================= Copy 100 bytes in it */
  (void) memcpy (pBuffer,(void*)(UIntPtr)pSourceCode, 0x600);

  (void) printf("******************************************************* \n");
  (void) printf("Display only BranchInstructions and ComparisonInstructions. \n");
  (void) printf("******************************************************* \n");

  /* ============================= Select Display Option */
  MyDisasm.Options = Tabulation + MasmSyntax;
  /* ============================= Disassemble code located in that buffer */
  DisassembleCode (pBuffer, (char*) pBuffer + 0x600, pSourceCode);

  return 0;
}
