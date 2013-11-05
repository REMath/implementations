#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <netnode.hpp>
#include <struct.hpp>

#include "arm.h"


static inline void mkreg(int n, int reg) {
	cmd.Operands[n].type = o_reg;
	cmd.Operands[n].reg = reg;
}

static inline void mkimm(int n, long imm, int reg = -1) {
	cmd.Operands[n].type = o_imm;
	cmd.Operands[n].value = imm;
	cmd.Operands[n].dtyp = dt_dword;
	cmd.Operands[n].specflag1 = reg;
}

static inline void mkphr(int n, int r1, int r2 = -1) {
	cmd.Operands[n].type = o_phrase;
	cmd.Operands[n].reg = r1;
	cmd.Operands[n].specflag1 = r2;
}

static inline void mkmemimm(int n, int r1, int r2, int r3, long imm)
{
	cmd.Operands[n].type = o_displ;
	cmd.Operands[n].value = imm;

	if (r1 == r3) {
		cmd.Operands[n].reg = r2;
		cmd.Operands[n].specflag1 = r1;
	} else {
		cmd.Operands[n].reg = r1;
		cmd.Operands[n].specflag1 = r2;
	}
}

static inline void mkdispl(int n, int r, long imm)
{
	cmd.Operands[n].type = o_displ;
	cmd.Operands[n].value = imm;
	cmd.Operands[n].reg = r;
	cmd.Operands[n].specflag1 = -1;	
}

static inline void mkjmp(int n, ea_t ea)
{
	cmd.Operands[n].type = o_near;
	cmd.Operands[n].addr = ea;
}

static bool instruction_writes_to(ea_t addr, int reg)
{
	int a = get_word(addr);
	
	// LDR
	if ((a & 0xF800) == 0x4800 && (a >> 8 & 7) == reg)
		return true;

	// MOVE
	if ((a & 0xF800) == 0x2000 && (a >> 8 & 7) == reg)
		return true; 

	return false;
}

//LDR R3,[R0=R0,R1]


int check_add_ldr(int a, int b, int reg, long imm)
{
	int t;

	// translate ADD Rx,R?,R?, LDR Rx,[Rx]
	if ((a & 0xFE00) == 0x1800 && // ADD
			(
			(t = ARM_ldr, (b & 0xFFC0) == 0x6800)  ||// LDR
			(t = ARM_ldrb, (b & 0xFFC0) == 0x7800) ||// LDRB
			(t = ARM_ldrh, (b & 0xFFC0) == 0x8800) // LDRH
			) && 
			(b >> 3 & 7) == (b & 7) && // LDR Rx,[Rx]
			(a & 7) == (b & 7)) {      // Add dest same as Rx?
		
		if (reg != -1) {
			if ((a >> 3 & 7) != reg && (a >> 6 & 7) != reg)
				return 0;

			mkmemimm(1, a >> 3 & 7, a >> 6 & 7, reg, imm);
		} else {
			mkphr(1, a >> 3 & 7, a >> 6 & 7);
		}
		
		cmd.itype = t;
		mkreg(0, b & 7);
		
		return 4;
	}

	return 0;
}

bool disallow_combine(ea_t ea)
{
	flags_t flags = getFlags(ea);
	return hasRef(flags) || has_name(flags);
}


int after_imm(ea_t ea, int reg, long imm)
{
	int a = get_word(ea);
	int t;

	if (disallow_combine(ea)) return 0;

	if ((a & 0xFFC0) == 0x4000 && (a & 7) == reg) {
		cmd.itype = ARM_and;
		
		mkreg(0, a & 7);
		mkreg(1, a >> 3 & 7);
		mkimm(2, imm);
		return 2;
	}

	if ((a & 0xFFC0) == 0x4240 && (a & 7) == reg && (a >> 3 & 7) == reg) {
		cmd.itype = ARM_movl;
		mkreg(0, reg);
		mkimm(1, -imm);
		return 2;
	}

	// ldrsh ry, [rx,rz]
	if ((
		(t=ARM_ldrsh, (a & 0xFE00) == 0x5E00) || 
		(t=ARM_ldrsb, (a & 0xFE00) == 0x5600)
		) && ((a >> 3 & 7) == reg || (a >> 6 & 7) == reg)
		) {
		cmd.itype = t;
		mkreg(0, a & 7);		
		mkmemimm(1, a >> 3 & 7, a >> 6 & 7, reg, imm);
		return 2;
	}

	t = check_add_ldr(a, get_word(ea + 2), reg, imm);
	if (t) return t;

	// check mov Rx,IMM   str Rx, ..
		if ( 
				 (t=ARM_str, (a & 0xF807) - reg == 0x6000) ||
				 (t=ARM_strb, (a & 0xF807) - reg == 0x7000) ||
				 (t=ARM_strh, (a & 0xF807) - reg == 0x8000)
		 ) {
			int disp = a >> 6 & 31;
			if (t == ARM_str) disp *= 4; else if (t == ARM_strh) disp *= 2;

			cmd.itype = t;
			mkimm(0, imm, a & 7);
			if (disp != 0)
				mkdispl(1, a >> 3 & 7, disp);
			else
				mkphr(1, a >> 3 & 7);
			return 2;
		}

	return 0;
}


int ana_simplify(void )
{
	int a, b, c, t;

	return 0;

	a = get_word(ea);
	b = get_word(ea + 2);

	// if it has references to it, don't simplify
	if (disallow_combine(ea + 2)) b = 0xFFFF;

	if ((a & 0xF800) == 0x2000) {
		// check if a is mov and b is lsl
		if ((b & 0xF83F) == ( ((a >> 8) & 7) + (((a >> 8) & 7) << 3))  )  {
			int imm = (a & 0xFF) << ((b >> 6) & 31);
			int reg = ((a >> 8) & 7);

			cmd.itype = ARM_movl;
			mkreg(0, reg);
			mkimm(1, imm);

			t = after_imm(ea + 4, reg, imm);
			if (t) return t + 4;
			return 4;
		}

		t = after_imm(ea + 2, (a >> 8 & 7), a & 0xFF);
		if (t) return 2 + t;
	}
	
	
	// check if it's ADD with a constant value, that's really a mov.
	if ( (a & 0xFFC0) == (0x1C00) ) {
		cmd.itype = ARM_move;
		mkreg(0, a & 7);
		mkreg(1, a >> 3 & 7);

		// check if an immediate add follows
		if ( (b & 0xF800) == 0x3000 && (a & 7) == (b >> 8 & 7) ) {
			cmd.itype = ARM_add;
			mkimm(2, b & 0xFF);

			// check if an LDR reg,[reg] follows
			c = get_word(ea + 4);
			if ( (c & 0xFFF8) == 0x6800 + (a & 7) + ((a & 7) << 3)) {
				cmd.itype = ARM_ldr;
				mkdispl(1, a >> 3 & 7, b & 0xFF);
				return 6;
			}
			return 4;
		}

		// check if an immediate subtract follows
		if ( (b & 0xF800) == 0x3800 && (a & 7) == (b >> 8 & 7) ) {
			cmd.itype = ARM_sub;
			mkimm(2, b & 0xFF);
			return 4;
		}

		return 2;
	}	

	// translate LDR into MOVE instruction
	if ( (a & 0xF800) == (0x4800)) {
		int reg = (a >> 8) & 7;
		int imm = a & 0xFF;

		cmd.itype = ARM_movl;
		mkreg(0, reg);
		mkimm(1, get_long((ea + 4 + imm * 4) &~2));

		// check if the instruction that follows is LDR or STR of the same reg
		if ( (t=ARM_ldr_data, (b & 0xFFF8) - (reg<<3) == 0x6800) ||
				 (t=ARM_str_data, (b & 0xFFF8) - (reg<<3) == 0x6000) ||
				 (t=ARM_ldrb_data, (b & 0xFFF8) - (reg<<3) == 0x7800) ||
				 (t=ARM_strb_data, (b & 0xFFF8) - (reg<<3) == 0x7000) ||
				 (t=ARM_ldrh_data, (b & 0xFFF8) - (reg<<3) == 0x8800) ||
				 (t=ARM_strh_data, (b & 0xFFF8) - (reg<<3) == 0x8000)
		 ) {
			cmd.itype = t;
			mkreg(0, b & 7),
			mkreg(2, instruction_writes_to(ea + 4, reg) ? (b & 7) : reg);
			return 4;
		}

		t = after_imm(ea + 2, cmd.Op1.reg, cmd.Op2.value);
		if (t) return 2 + t;

		return 2;
	}

	// translate
	// LSL R0,R0,#0x18
	// LSR Rx,R0,#0x18
	if (( 
		(t=ARM_movzb, (a & 0xFFC0) == 0x0600 && (b & 0xFFC0) == 0x0E00) ||
		(t=ARM_movsb, (a & 0xFFC0) == 0x0600 && (b & 0xFFC0) == 0x1600) ||
		(t=ARM_movzw, (a & 0xFFC0) == 0x0400 && (b & 0xFFC0) == 0x0C00) ||
		(t=ARM_movsw, (a & 0xFFC0) == 0x0400 && (b & 0xFFC0) == 0x1400)) && 
		 (a & 7) == (b >> 3 & 7) &&
		 ((a & 7) == (b & 7) || (a & 7) == (a >> 3 & 7))

		  ) {
		cmd.itype = t;

		mkreg(0, b & 7);
		mkreg(1, a >> 3 & 7);

		return 4;
	}

	t = check_add_ldr(a, b, -1, 0);
	if (t) return t;

	// check if it's a compare followed by a branch
	if ( ((t=0, (a & 0xF800) == 0x2800) || (t=1, (a & 0xFFC0) == 0x4280) || (t=2, (a & 0xFF00) == 0x4500)) &&
			 (b & 0xF000) == 0xD000 && (b & 0xF00) < 0xE00) {
		cmd.itype = ARM_ifgoto;
		cmd.segpref = b >> 8 & 0xF;

		if (t == 0) {
			mkreg(0, a >> 8 & 7);
			mkimm(1, a & 0xFF);
		} else if (t == 1) {
			mkreg(0, a & 7);
			mkreg(1, a >> 3 & 7);
		} else {
			mkreg(0, (a & 7) + ((a & 0x80) >> 4));
			mkreg(1, (a >> 3 & 7) + ((a & 0x40) >> 3));
		}
		mkjmp(2, ea + 6 + ((signed char)(b & 0xFF)) * 2);
		return 4;
	}
	
//	000 00 11000 xxx yyy
//	00000110 00xxxyyy

//sub_0_800D6E0+36   FF 21         MOV   R1, #0xFF
//sub_0_800D6E0+38   19 40         AND   R1, R3

//sub_0_800D6E0+3E   0E 48         LDR   R1, =oam_backup       ; (R0=?)
//sub_0_800D6E0+38   19 40         AND   R1, R3

//waitforstart_5+34   DE 21 49 00   MOVL  R1, 0x1BC
//waitforstart_5+38   50 18         ADD   R0, R2, R1
//waitforstart_5+3A   00 21         MOV   R1, #0
//waitforstart_5+3C   01 60         STR   R1, [R0]

//intro_calltable_5+BA   01 22         MOV   R2, #1
//intro_calltable_5+BC   52 42         NEG   R2, R2

//ROM:0800BC02 04 24         MOV   R4, #4
//ROM:0800BC04 1D 5F         LDRSH R5, [R3,R4]

	return 0;

}

//--------------------------------------------------------------------------
// Return the instruction mnemonics
const char *get_insn_mnem(void)
{
  switch(cmd.itype) {
	case ARM_movl: return "MOVL";
	case ARM_move: return "MOVE";
	case ARM_ldr_data: return "LDR";
	case ARM_str_data: return "STR";
	case ARM_ldrb_data: return "LDRB";
	case ARM_strb_data: return "STRB";
	case ARM_ldrh_data: return "LDRH";
	case ARM_strh_data: return "STRH";
	case ARM_movzb: return "MOVZB";
	case ARM_movsb: return "MOVSB";
	case ARM_movzw: return "MOVZW";
	case ARM_movsw: return "MOVSW";

	case ARM_ldr: return "LDR";
	case ARM_ldrb: return "LDRB";
	case ARM_ldrh: return "LDRH";

	case ARM_ldrsh: return "LDRSH";
	case ARM_ldrsb: return "LDRSB";

	case ARM_add: return "ADD";
	case ARM_and: return "AND";
	case ARM_sub: return "SUB";

	case ARM_str: return "STR";
	case ARM_strb:return "STRB";
	case ARM_strh:return "STRH";

	case ARM_ifgoto: return "IF";

	default:
		return "UNKNOWN";
	}
}



bool outop_simplify(op_t *op)
{
	if (op->type == o_phrase) {
		out_symbol('[');
		out_register(_registers[op->reg]);
		if (op->specflag1 != -1) {
			out_symbol(',');
			out_register(_registers[op->specflag1]);
		}
		out_symbol(']');
		OutChar(0);
		return true;
	}

	if (op->type == o_displ) {
		out_symbol('[');
		out_register(_registers[op->reg]);
		out_symbol(',');
		if (op->specflag1 != -1) {
			out_register(_registers[op->specflag1]);
			out_symbol('=');
		}
		out_symbol('#');
		OutValue(*op);
		out_symbol(']');
		OutChar(0);
		return true;
	}

	if (op->type == o_imm) {
		if (op->specflag1 != -1) {
			out_register(_registers[op->specflag1]);
			out_symbol('=');
		}
		OutValue(*op);
		return true;
	}
	return false;
}

static const char * const _compare_ops[] = {
	" == ",
	" != ",
	" >=u ",
	" <u ",
	" MI ",
	" PL ",
	" VS ",
	" VC ",
	" >u ",
	" <=u ",
	" >= ",
	" < ",
	" > ",
	" <= ",	
};

static void out_symbols(const char *s)
{
	for(;*s;s++) out_symbol(*s);
}

void out_simplify()
{
	char buf[1024];

	init_output_buffer(buf, sizeof(buf));

	int s = get_item_size(cmd.ea);

	if (s != cmd.size) {
		msg("size %d vs %d at %x\n", s, cmd.size, cmd.ea);
		do_unknown_range(cmd.ea, s > cmd.size ? s : cmd.size, 0);
		MakeLine("<patched>");
		return;
	}

	OutMnem();
	out_one_operand(0);

	if (cmd.itype == ARM_ifgoto) {
		out_symbols(_compare_ops[cmd.segpref]);
		out_one_operand(1);
		out_symbol(','); OutChar(' ');
		out_one_operand(2);
		goto done;
	}
	
	out_symbol(','); OutChar(' ');
	
	if (cmd.itype >= ARM_ldr_data && cmd.itype <= ARM_strh_data) {
		out_symbol('[');
		
		if (cmd.Op1.reg != cmd.Op3.reg) {
			out_one_operand(2);
			OutChar(' ');out_symbol('=');OutChar(' ');
		}
		
		out_one_operand(1);
		out_symbol(']');
	} else if (cmd.itype == ARM_add || cmd.itype == ARM_and || cmd.itype == ARM_sub) {
		out_one_operand(1);
		out_symbol(','); OutChar(' ');
		out_one_operand(2);
	} else {
		out_one_operand(1);
	}
	

done:
	term_output_buffer();
	MakeLine(buf);
}


void emu_simplify()
{
	ua_add_off_drefs(cmd.Op2, dr_O);
	ua_add_cref(0,cmd.ea+cmd.size,fl_F);

	if (cmd.itype == ARM_ifgoto) {
		ua_add_cref(0,cmd.Operands[2].addr,fl_JN);
	}
}
