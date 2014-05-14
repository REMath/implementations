
enum {
	O_UNK,

	O_MOV,

	O_MVN,
	O_AND,
	O_TST,
	O_BIC,
	O_ORR,
	O_EOR,
	O_LSL,
	O_LSR,
	O_ASR,
	O_ROR,
	O_NOP,

	O_ADD,
	O_ADC,
	O_SUB,
	O_SBC,
	O_NEG,
	O_CMP,
	O_CMN,
	O_MUL,

	O_B,
	O_BL,
	O_BX,

	O_BEQ,
	O_BNE,
	O_BCS,
	O_BCC,
	O_BMI,
	O_BPL,
	O_BVS,
	O_BVC,
	O_BHI,
	O_BLS,
	O_BGE,
	O_BLT,
	O_BGT,
	O_BLE,

	O_SWI,
	
	O_LDR,
	O_LDRB,
	O_LDRH,
	O_LDSB,
	O_LDSH,
	O_STR,
	O_STRB,
	O_STRH,
	O_PUSH,
	O_POP,

	O_STMIA,
	O_LDMIA,
};

enum {
	R_SP = 13,
};

enum {
	O_VOID = 0, // no operand
	O_IMM = 1,	// immediate value
	O_REG = 2,	// register
	O_CODE= 3,	// code pointer
	O_MEM = 4,	// memory access

	O_REGMASK = 5, // mask of registers, used for push/pop
};

struct ArmOp {
	byte type;
	byte reg;
	byte reg2; // second register in memory access.. or 0xff
	uint32 value;
};

struct ArmIns {
	byte mnem;		// mnemonic
	ArmOp op[3];	// operands

#define op1 op[0]
#define op2 op[1]
#define op3 op[2]
};

int DecodeThumb(ArmIns &i, ea_t pc);
void PrintThumb(ArmIns &i, char *s);
extern const char * const _regs[];
extern const char * const _mnems[];
