#include <ida.hpp>
#include <bytes.hpp>
#include "default.h"
#include "insn.h"


void MkReg2Imm(ArmIns &i, uint m, uint r1, uint r2, long imm)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
	i.op[1].type = O_REG;i.op[1].reg = r2;
	i.op[2].type = O_IMM;i.op[2].value = imm;
}

void MkReg3(ArmIns &i, uint m, uint r1, uint r2, uint r3)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
	i.op[1].type = O_REG;i.op[1].reg = r2;
	i.op[2].type = O_REG;i.op[2].reg = r3;
}

void MkReg2(ArmIns &i, uint m, uint r1, uint r2)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
	i.op[1].type = O_REG;i.op[1].reg = r2;
}

void MkReg(ArmIns &i, uint m, uint r1)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
}

void MkRegImm(ArmIns &i, uint m, uint r1, long imm)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
	i.op[1].type = O_IMM;i.op[1].value = imm;
}

void MkRegMem(ArmIns &i, uint m, uint r1, uint r2, uint r3, long imm)
{
	i.mnem = m;
	i.op[0].type = O_REG;i.op[0].reg = r1;
	i.op[1].type = O_MEM;
	i.op[1].reg = r2;
	i.op[1].reg2 = r3;
	i.op[1].value = imm;
}

void MkJump(ArmIns &i, uint m, ea_t ea)
{
	i.mnem = m;
	i.op[0].type = O_CODE;
	i.op[0].value = ea;	
}

#define MASK(n) ((1<<(n))-1)
#define F(x,y) ((op >> x) & MASK(y-x+1))
#define SEX(v,n) ((signed int)((v)<<(32-n))>>(32-n))
// decode a Thumb instruction.
// return the length
int DecodeThumb(ArmIns &i, ea_t pc)
{
	memset(&i, 0, sizeof(i));
	uint op = get_word(pc);

	switch(F(11,15)) {
	case 0x00: MkReg2Imm(i, O_LSL, F(0,2), F(3,5), F(6,10)); return 2;
	case 0x01: MkReg2Imm(i, O_LSR, F(0,2), F(3,5), F(6,10)); return 2;
	case 0x02: MkReg2Imm(i, O_ASR, F(0,2), F(3,5), F(6,10)); return 2;

	case 0x03: {
		uint f1 = F(0,2), f2=F(3,5), f3=F(6,8);
		switch(F(9,10)) {
		case 0: MkReg3(i, O_ADD, f1,f2,f3); return 2;
		case 1: MkReg3(i, O_SUB, f1,f2,f3); return 2;
		case 2: 
			if (f3 != 0)
				MkReg2Imm(i, O_ADD, f1,f2,f3);
			else
				MkReg2(i, O_MOV, f1, f2);
			return 2;
		case 3: MkReg2Imm(i, O_SUB, f1,f2,f3); return 2;
		}
		break;
	}
	
	case 0x4: MkRegImm(i, O_MOV, F(8,10), F(0,7)); return 2;
	case 0x5: MkRegImm(i, O_CMP, F(8,10), F(0,7)); return 2;
	case 0x6: MkRegImm(i, O_ADD, F(8,10), F(0,7)); return 2;
	case 0x7: MkRegImm(i, O_SUB, F(8,10), F(0,7)); return 2;

	case 0x8:
		if (!F(10,10)) {
			static const byte _aluops[] = {
				O_AND,O_EOR,O_LSL,O_LSR,
				O_ASR,O_ADC,O_SBC,O_ROR,
				O_TST,O_NEG,O_CMP,O_CMN,
				O_ORR,O_MUL,O_BIC,O_MVN
			};
			MkReg2(i, _aluops[F(6,9)], F(0,2), F(3,5)); return 2;
		} else {
			uint d = F(0,2) | (F(7,7)<<3);
			uint s = F(3,6);
			switch(F(8,9)) {
			case 0: MkReg2(i, O_ADD, d, s); return 2;
			case 1: MkReg2(i, O_CMP, d, s); return 2;
			case 2: MkReg2(i, O_MOV, d, s); return 2;
			case 3: MkReg(i, O_BX, s); return 2;
			}
		}
		break;

	case 0x9: { // PC relative constant load
		MkRegImm(i, O_MOV, F(8,10), get_long( ((pc + 4)&~2) + F(0,7) * 4 ));
		return 2;
	}

	case 0xA: case 0xB: { // Store/Load Rd, [Rn, Rm]
		static const byte _storeloadops[] = {
			O_STR, O_STRH, O_STRB,O_LDSB,
			O_LDR, O_LDRH, O_LDRB,O_LDSH,
		};
		i.mnem = _storeloadops[F(9,11)];
		i.op[0].type = O_REG; i.op[0].reg=F(0,2);
		i.op[1].type = O_MEM; i.op[1].reg=F(3,5); i.op[1].reg2=F(6,8);
		return 2;
	}

	case 0xC: case 0xD: case 0xE: case 0xF: case 0x10: case 0x11: {
		static const byte _ops[] = { O_STR, O_LDR, O_STRB, O_LDRB, O_STRH, O_LDRH };
		static const byte _mul[] = { 4, 4, 1, 1, 2, 2 };
		MkRegMem(i, _ops[F(11,15)-0xC], F(0,2),
			F(3,5), 0xff, F(6,10) * _mul[F(11,15)-0xC]);
		return 2;
	}

	case 0x12: MkRegMem(i, O_STR, F(8,10), R_SP, 0xff, F(0,7) * 4); return 2;
	case 0x13: MkRegMem(i, O_LDR, F(8,10), R_SP, 0xff, F(0,7) * 4); return 2;

	case 0x14: MkRegImm(i, O_MOV, F(8,10), ((pc+4)&~2) + F(0,7) * 4); return 2;
	case 0x15: MkReg2Imm(i, O_ADD, F(8,10), R_SP, F(0,7) * 4); return 2;
	
	case 0x16:
		if (F(9,10) == 2) {
			i.mnem = O_PUSH;
			i.op[0].type = O_REGMASK;
			i.op[0].value = F(0,7) + (F(8,8) ? (1<<14):0);
			return 2;
		} else if (F(7,10) == 1) {
			MkReg2Imm(i, O_SUB, R_SP, R_SP, F(0,6)*4);
			return 2;
		} else if (F(7,10) == 0) {
			MkReg2Imm(i, O_ADD, R_SP, R_SP, F(0,6)*4);
			return 2;
		}
		break;

	case 0x17:
		if (F(9,10) == 2) {
			i.mnem = O_POP;
			i.op[0].type = O_REGMASK;
			i.op[0].value = F(0,7) + (F(8,8) ? (1<<15):0);
			return 2;
		}
		break;

	case 0x18:
	case 0x19:
		i.mnem = F(11,11) ? O_LDMIA : O_STMIA;
		i.op[0].type = O_REG;
		i.op[0].reg = F(8,10);
		i.op[1].type = O_REGMASK;
		i.op[1].value = F(0,7);
		return 2;

	case 0x1A:
	case 0x1B: {
		uint m = F(8,11);
		if (m <= 0xD) {
			static const byte _ops[] = {
				O_BEQ,O_BNE,O_BCS,O_BCC,
				O_BMI,O_BPL,O_BVS,O_BVC,
				O_BHI,O_BLS,O_BGE,O_BLT,
				O_BGT,O_BLE,
			};
			MkJump(i, _ops[m], pc + 4 + SEX(F(0,7),8) * 2);
			return 2;
		} else if (m == 0xF) {
			i.mnem = O_SWI;
			i.op[0].type = O_IMM;
			i.op[0].value = F(0,7);
			return 2;
		}
		break;
	}

	case 0x1C:
		MkJump(i, O_B, pc + 4 + SEX(F(0,10),11) * 2);
		return 2;

	case 0x1E: {
		uint o2 = get_word(pc + 2);
		MkJump(i, O_BL, pc + 4 + SEX( ((op & 0x7FF)<<11) + (o2 & 0x7FF),22) * 2);
		return 4;
	}
	}

	return 0; // undefined instruction
}

const char * const _mnems[] = {
"UNK",

"MOV",

"MVN",
"AND",
"TST",
"BIC",
"ORR",
"EOR",
"LSL",
"LSR",
"ASR",
"ROR",
"NOP",

"ADD",
"ADC",
"SUB",
"SBC",
"NEG",
"CMP",
"CMN",
"MUL",

"B",
"BL",
"BX",

"BEQ",
"BNE",
"BCS",
"BCC",
"BMI",
"BPL",
"BVS",
"BVC",
"BHI",
"BLS",
"BGE",
"BLT",
"BGT",
"BLE",

"SWI",
	
"LDR",
"LDRB",
"LDRH",
"LDSB",
"LDSH",
"STR",
"STRB",
"STRH",
"PUSH",
"POP",

"STMIA",
"LDMIA",
};

const char * const _regs[] = {
	"R0",
	"R1",
	"R2",
	"R3",
	"R4",
	"R5",
	"R6",
	"R7",
	"R8",
	"R9",
	"R10",
	"R11",
	"R12",
	"SP",
	"LR",
	"PC",
};

static char *PrintOp(char *s, ArmOp &o)
{
	switch(o.type) {
	case O_IMM:
		// size is charbuf[80] in printexp()
		// not taking into account used space -> overflow
		s += qsnprintf(s, 80, "0x%X", o.value);
		break;
	case O_REG:
		s = strcpy_e(s, _regs[o.reg]);
		break;

	case O_CODE:
		s += qsnprintf(s, 80, "0x%X", o.value);
		break;
		
	case O_MEM:
		if (o.reg2 != 0xFF && o.value == 0) {
			s += qsnprintf(s, 80, "[%s, %s]", _regs[o.reg], _regs[o.reg2]);
		} else if (o.reg2 == 0xff && o.value != 0) {
			s += qsnprintf(s, 80, "[%s, %d]", _regs[o.reg], o.value);
		} else if (o.reg2 == 0xff && o.value == 0) {
			s += qsnprintf(s, 80, "[%s]", _regs[o.reg]);
		} else {
			s = strcpy_e(s, "<INVALID>");
		}
		break;

	case O_REGMASK: {
		*s++ = '{';
		bool first = true;
		for(int i=0; i!=16; i++) {
			if (o.value & (1 << i)) {
				if (!first) *s++ = ',';
				first = false;
				s = strcpy_e(s, _regs[i]);
			}
		}
		*s++ = '}';
		*s = 0;
		break;
	}

	default:
		s = strcpy_e(s, "<INVALID>");
	}

	return s;
}

void PrintThumb(ArmIns &i, char *s)
{
	// buffer size is charbuf[80] in printexp()
	// not taking into account used space -> overflow
	s += qsnprintf(s, 80, "%-8s", _mnems[i.mnem]);

	if (i.op[0].type != O_VOID) {
		s = PrintOp(s, i.op[0]);
		if (i.op[1].type != O_VOID) {
			*s++ = ',';
			*s++ = ' ';
			s = PrintOp(s, i.op[1]);
			if (i.op[2].type != O_VOID) {
				*s++ = ',';
				*s++ = ' ';
				s = PrintOp(s, i.op[2]);
			}
		}
	}
}

