// Copyright 2004-2005 Ludvig Strigeus <strigeus@gmail.com>
// GNU GPL LICENSE

#include <ida.hpp>
#include <idp.hpp>
#include <typeinf.hpp>
#include <struct.hpp>

#define WITH_CONSTRUCTORS
#include "default.h"
#include "insn.h"
#include "exp.h"

using namespace std;
#define cmd foo
void DumpRS(const RegState &rs);
bool IsBB(BasicBlock *list, BasicBlock *bb);



BasicBlock *Analyzer::NewBasicBlock()
{
	// otherwise allocate
	BasicBlock *bb = new BasicBlock;
	memset(bb, 0, sizeof(BasicBlock));

	bb->next = _list->next;
	_list->next = bb;

	bb->base = 0;

	return bb;
}


BasicBlock *Analyzer::GetBasblockAt(ea_t from)
{
	BasicBlock *bb, **bbp = &_list;

	// first see if it exists already? the list is sorted in address order
	while ( (bb = *bbp) != NULL) {
		if (from <= bb->base) {
			if (from == bb->base)
				return bb;
			break;
		}
		bbp = &bb->next;
	}

	// otherwise allocate
	bb = new BasicBlock;
	memset(bb, 0, sizeof(BasicBlock));

	bb->next = *bbp;
	*bbp = bb;

	bb->base = from;

	return bb;
}

void Analyzer::DestroyBB(BasicBlock *del)
{
//	msg("Destroying %x\n",del->base);
	BasicBlock *bb, **bbp = &_list;
	while ( (bb = *bbp) != del) { bbp = &bb->next; }
	*bbp = bb->next;
//	delete del;
}

struct JmpDst {
	ea_t ea; // address of jump instruction
	JmpDst *next; // next jmp instruction
};

static bool InstructionEndsFlow(ArmIns &ins)
{
	// unconditional jumps
	if (ins.mnem == O_BX || ins.mnem == O_B)
		return true;

	// assignment to PC
	if (ins.mnem == O_MOV && ins.op1.type == O_REG && ins.op1.reg == 15)
		return true;

	if (ins.mnem == O_POP && ins.op1.value & (1 << 15))
		return true;

	return false;
}

static bool InsertJmpDst(JmpDst *&first, addr_t dst, Pool &p)
{
	// insert into list of jump destinations if it's not there already. the list is sorted in address order.
	JmpDst *jd, **jdp = &first;
	// add it to the list, sorted in address order.
	for(;;) {
		if ((jd = *jdp) == NULL || dst < jd->ea) {
			jd = (JmpDst*)p.Alloc(sizeof(JmpDst));
			jd->ea = dst;
			jd->next = *jdp;
			*jdp = jd;
			return true;
		}
		if (dst == jd->ea)
			break;
		jdp = &jd->next;
	}
	return false;
}

struct SwitchStatement {
	SwitchStatement *next;
	uint num_edges;
	uint reg;
	addr_t ea_start; // address of ldr rx, =jmptbl
	addr_t ea; // address of mov pc,?? instr
	addr_t edges[1]; // edges
	int hasdefault;
	addr_t defaultadd;
};

static SwitchStatement *GetSwitchAt(SwitchStatement *s, addr_t ea)
{
	for(;s;s=s->next)
		if (s->ea == ea)
			return s;
	return NULL;
}
/*Severly old
int CheckSwitchR0(addr_t ea){
	//Using R0
	// verify that it matches the switch sequence.
	//ROM:080003A4 80 00   LSL   R0, R0, #2
	//ROM:080003A6 02 49   LDR   R1, =off_83C173C
	//ROM:080003A8 40 18   ADD   R0, R0, R1
	//ROM:080003AA 00 68   LDR   R0, [R0]
	//ROM:080003AC 87 46   MOV   PC, R0
	if (!(get_word(ea) == 0x4687 &&
		get_word(ea-2) == 0x6800 &&
		get_word(ea-4) == 0x1840 &&
		(get_word(ea-6) & 0xff00) == 0x4900 &&
		(get_word(ea-8)&~0x38) == 0x0080))
	{
		return 0;
	}


	return 1;
}

int CheckSwitchR1(addr_t ea){
	char err[1024]={0};
	//Using R0
	// verify that it matches the switch sequence.
	//ROM:0807D4A2  89 00          LSLS    R1, R1, #2
	//ROM:0807D4A4  01 4A          LDR     R2, =jpt_807D4AA
	//ROM:0807D4A6  89 18          ADDS    R1, R1, R2
	//ROM:0807D4A8  09 68          LDR     R1, [R1]
	//ROM:0807D4AA  8f 46          MOV     PC, R1        
	if (!(get_word(ea) == 0x468F &&
		get_word(ea-2) == 0x6809 &&
		get_word(ea-4) == 0x1889 &&
		(get_word(ea-6) & 0xff00) == 0x4A00 &&
		(get_word(ea-8)) == 0x0089))
	{
		return 0;
	}
	msg("R1 switch obtained!\n");
	return 1;
}
*/
int CheckMySwitch(addr_t ea)
{
	if ((get_word(ea-0) & 0xFF00) == 0x4600 && //MOV PC, Rx 
		(get_word(ea-2) & 0xF800) == 0x6800 && //LDR Rx, [Rx]
		(get_word(ea-4) & 0xFE00) == 0x1800 && //ADD Rx, Rx, Ry
		(get_word(ea-6) & 0xF800) == 0x4800 && //LDR Ry, =jpt
		(get_word(ea-8) & 0xFF80) == 0x0080)  //LSLS Rx, Rx, #2
	{
		//Make sure that the registers are correctly setup
		return 1;
	}

	if ((get_word(ea-0) & 0xFF00) == 0x4600 && //MOV PC, Rx 
		(get_word(ea-2) & 0xF800) == 0x5800 && //LDR Rx, [Ry, Rx]
		(get_word(ea-4) & 0xFF80) == 0x0080 && //LSLS Rx, Rx, #2
		(get_word(ea-6) & 0xF800) == 0x4800)  //LDR Ry, =jpt
	{
		//Make sure that the registers are correctly setup
		return 2;
	}

	return 0;
}
static SwitchStatement *TryCreateSwitchStatement(SwitchStatement *&ss, addr_t ea, Pool &pool, addr_t funcstart, addr_t funcend,long* addrs)
{
	int reg=0;
	int jmpSize=4;
	addr_t jmptab_addr=0;
	addr_t ea_start=0;
	ArmIns ins;
	uint switch_max=0;
	int limit=0;
	// first check if a switch statement has already been created, only allow a single one
	for(SwitchStatement *s = ss;s;s=s->next)
		if (s->ea == ea)
			return 0;

	// If switch information is present in the database, use it for defaults
	switch_info_ex_t si;
	if ( get_switch_info_ex(ea, &si, sizeof(si)) > 0 )
	{
		//msg("si.jumps  = %08X\n",si.jumps);
		//msg("si.ncases  = %08X\n",si.ncases);
		//msg("si.jcases  = %08X\n",si.jcases);
		//msg("si.startea  = %08X\n",si.startea);
		//msg("si.elbase  = %08X\n",si.elbase);
		//msg("si.get_jtable_element_size()  = %08X\n",si.get_jtable_element_size());
		//msg("si.get_shift()  = %08X\n",si.get_shift());
		//msg("si.flags  = %08X\n",si.flags);
		//msg("si.values  = %08X\n",si.values);
		//msg("si.get_vtable_element_size()  = %08X\n",si.get_vtable_element_size());
		//msg("si.regnum  = %08X\n",si.regnum);
		//msg("si.regdtyp  = %08X\n",si.regdtyp);
		//msg("si.defjump  = %08X\n",si.defjump);
		//msg("si.cb  = %08X\n",si.cb);
		//msg("si.flags2  = %08X\n",si.flags2);
		//msg("si.is_indirect()  = %08X\n",si.is_indirect());
		//msg("si.is_subtract()  = %08X\n",si.is_subtract());

		//msg("get_switch_parent(ea)  = %08X\n",get_switch_parent(ea));

	    switch_max = si.get_jtable_size();
	    jmptab_addr = si.jumps;
	    reg = si.regnum;
	    jmpSize = si.get_jtable_element_size();

		//msg("get_next_dref_from(jmptab_addr,ea)  = %08X\n",get_next_dref_from(jmptab_addr,ea));
		//msg("get_next_dref_to(jmptab_addr,ea)  = %08X\n",get_next_dref_to(jmptab_addr,ea));
		//msg("get_first_dref_to(jmptab_addr)  = %08X\n",get_first_dref_to(jmptab_addr));

		//msg("get_next_dref_from(jmptab_addr,funcstart)  = %08X\n",get_next_dref_from(jmptab_addr,funcstart));
		//msg("get_next_dref_to(jmptab_addr,funcstart)  = %08X\n",get_next_dref_to(jmptab_addr,funcstart));

		addr_t adr_of_ldr = get_next_dref_to(jmptab_addr,funcstart); //LDR Ry, =jpt

		if((get_word(adr_of_ldr-2) & 0xFF80) == 0x0080) //LSLS Rx, Rx, #2
		ea_start = adr_of_ldr - 2;
		else
		ea_start = adr_of_ldr;

	    //This will only work if only one method uses this jump table (Which should be most of the time)
	    //ea_start = get_first_dref_to(jmptab_addr);
	}
	else
	{
		//If IDA PRO doesn't detect the jump table then try to detect it manually

		/*
		ROM:0807D49C                 CMP     R1, #0x12
		ROM:0807D49E                 BLS     JumpTable
		ROM:0807D4A0                 B       loc_807DAD8     @ jumptable 0807D4AA default case
		*/
		/*
		check for tables with limits
		2YXX 16 CMP X, Y 
		d900 14 BLS blah
		e000 12 B blah


		//*/
		//addr_t defaddr=0;
		//int hasdefault=0;
		//if (get_word(ea-16) & 0x2000 &&
		//	get_word(ea-14) & 0xd900 &&
		//	get_word(ea-12) & 0xe000)
		//{
		//	switch_max=(get_word(ea-16)&0xFF);
		//	hasdefault=1;
		//	defaddr=(ea-8)+((signed)(get_word(ea-12)&0xFFF) );//0807D4A0 0xE31A  B       loc_807DAD8		
		//}
		msg("ea  = %08X\n",ea);

		int jumpTableType = CheckMySwitch(ea);
		msg("jumpTableType = %d\n",jumpTableType);
		if(jumpTableType == 0)
		{
			msg("No switches\n");
			return 0;
		}

		int offset1 = ea - 8; //LSLS Rx, Rx, #2
		int offset2 = ea - 6; //LDR Ry, =jpt
		int offset3 = ea - 10; //BHI Somewhere
		int offset4 = ea - 12; //CMP Rx, #xx
		ea_start = ea - 8; //Default start address

		if(jumpTableType == 2)
		{
			offset1 = ea - 4;
			ea_start = ea - 6;
		}

		reg = (get_word(offset1) >> 3) & 7; //LSLS Rx, Rx, #2

		// indeed it does..
		// determine the address of the switch's jumptable
		DecodeThumb(ins, offset2);
		assert(ins.mnem == O_MOV && ins.op[1].type == O_IMM);
		jmptab_addr = ins.op[1].value;

		// max number of items in switchtable
	

		// try to determine the number of items in the jumptable
		msg("jmptab=%x\nyAt offset %x\n", jmptab_addr,ea);
		if(switch_max==0)
		{
			bool found = false;
			//If we didn't have a BLS table earlier..
			for(int i=offset2; i>offset2-0x10; i-=2)
			{
				msg("searching at %08X\n",i);
				if ((get_word(i) & 0xFF00) == 0xD800 && //BHI Somewhere
					(get_word(i-2) & 0xF800) == 0x2800) //CMP Rx, #xx
				{
					msg("found switch_max at %08X\n",i-2);
					switch_max = get_byte(i-2) + 1;
					found = true;
					break;
				} 
				else if ((get_word(i) & 0xFF00) == 0xD900 && //BLS JumpTable
						(get_word(i-2) & 0xF800) == 0x2800) //CMP Rx, #xx
				{
					msg("found switch_max at %08X\n",i-2);
					switch_max = get_byte(i-2) - 1;
					found = true;
					break;
				} 
			}
			if(!found)
			{
				for(uint i=0; ; i++) {
					addr_t x = get_long(jmptab_addr + i * 4);
		
					if (0==(x & 0x8FFFFFF)||(x|0x8FFFFFF) > (funcend|0x80000000)) {
						switch_max = i-1;
						break;
					}
					msg("Address: %x\n", x);
				}
			}
		}
		msg("Max: %d\n", switch_max);
		// make sure the switch items are inside the function bounds
		/*for(uint i=0; i!=switch_max; i++) {
			addr_t x = get_long(jmptab_addr + i * 4);
			if (x < ea || x > funcend) return 0;
		}*/
	}

	SwitchStatement *s = (SwitchStatement*)pool.Alloc(sizeof(SwitchStatement) + switch_max * sizeof(addr_t));

	s->ea = ea;
	s->next = ss;
	ss = s;
	s->num_edges = switch_max;
	s->reg = reg;
	s->ea_start = ea_start;

	for(uint i=0; i!=switch_max; i++) {
		s->edges[i] = get_long(jmptab_addr + i * 4);
	}
	

	
	return s;
}

bool Analyzer::CreateSwitchConds(BasicBlock *bb, SwitchStatement *s)
{
	int num_jmptbl_lookup_instr = ((s->ea - s->ea_start)/2) + 1;
	msg("s->ea = %08X\n", s->ea);
	msg("s->ea_start = %08X\n", s->ea_start);
	msg("num_jmptbl_lookup_instr = %d\n", num_jmptbl_lookup_instr);
	if (bb->num_instr < num_jmptbl_lookup_instr)
		return false;

	// delete the last 5 instructions...
	bb->instr.SetCount(bb->num_instr - num_jmptbl_lookup_instr);

	if (s->num_edges == 1) {
		// special case.. only a single edge going out?!
		bb->flow = GetBasblockAt(s->edges[0]);
		bb->flow->ref++;
		return true;
	}

	// otherwise create compare instructions
	for(uint i=0; i != s->num_edges - 1; i++) {
		MkInstr(bb->instr.Append(), NewCondExp(NewBinExp(E_COMP_EQ, NewRegExp(s->reg), NewConstExp(i))));
		bb->cond = GetBasblockAt(s->edges[i]);
		bb->cond->ref++;
		bb->flow = (i == s->num_edges - 2) ? GetBasblockAt(s->edges[i+1]) : NewBasicBlock();
		bb->flow->ref++;
		bb = bb->flow;
	}

	return true;
}

bool Analyzer::AnalyzeOwn(ea_t start, ea_t end)
{
	addr_t ea;
	ArmIns ins;
	JmpDst *first_dst = NULL;
	SwitchStatement *switches = NULL;
	bool changes;
	Pool pool(1000);

	_function_base = start;

	do {
		ea = start;
		changes = false;
		for(;;) {
			if (ea >= end) {
				msg("%x: Flow continues beyond function boundary\n", ea);
				return false;
			}
			int len = DecodeThumb(ins, ea);
			if (len == 0) {
				msg("Unable to decode at %x\n", ea);
				return false;
			}

			// check if the instruction references code in this function?
			if (((ins.mnem == O_B || ins.mnem == O_BL) && ins.op[0].value != start || (ins.mnem >= O_BEQ && ins.mnem <= O_BLE)) && ins.op[0].value >= start && ins.op[0].value < end) {
				// insert a jump destination.
				if (InsertJmpDst(first_dst, ins.op[0].value, pool) && ins.op[0].value <= ea)
					changes = true;
			}
			ea += len;
			if (InstructionEndsFlow(ins) || ins.mnem == O_BL && ins.op[0].value > start && ins.op[0].value < end) {
				// need to determine if it's a switch statement.
				// if it is a switch statement, then jump destinations for the switch statement need to be determined
				if (ins.mnem == O_MOV && ins.op[0].reg == 15) {
					long addrs;
					SwitchStatement *s = TryCreateSwitchStatement(switches, ea - 2, pool, start, end,&addrs);
					if (s) {
						// it's a switch statement, insert the switch edges into the jmpdst list
						for(uint i=0; i!=s->num_edges; i++)
							InsertJmpDst(first_dst, s->edges[i], pool);
					}
				
				}

				// locate the first entrypoint that's >= than "ea" and continue there.
				JmpDst *jd = first_dst;
				for(;;) {
					if (!jd) goto getout; // finished with everything?
					if (jd->ea >= ea) { ea = jd->ea; break; }
					jd = jd->next;
				}
			}
		}
getout:;
	} while (changes);

	_list = NULL;

	// now we have determined the start address for each basic block.
	// do another pass that actually creates the basic blocks and fills them with instructions.

	BasicBlock *bb = GetBasblockAt(ea = start);
	
	bool flow;

	for(;;) {
		assert(ea < end);

		int len = DecodeThumb(ins, ea);
		if (len == 0) {
			msg("Unable to decode at %x\n", ea);
			return false;
		}

		if (((ins.mnem == O_B || ins.mnem == O_BL) && ins.op[0].value != start) && ins.op[0].value >= start && ins.op[0].value < end) {
			bb->flow = GetBasblockAt(ins.op[0].value);
			bb->flow->ref++;
			flow = false;
		} else {
			CreateInstruction(ins, ea, bb);
			ea += len;

			// check if to terminate the basblock?
			if (ins.mnem >= O_BEQ && ins.mnem <= O_BLE && ins.op[0].value >= start && ins.op[0].value < end && bb->instr[bb->num_instr-1].e->type == E_COND) {
				// add a cond to the basblock
				bb->cond = GetBasblockAt(ins.op[0].value);
				bb->cond->ref++;
				flow = true;
			} else if (InstructionEndsFlow(ins)) {
				flow = false;
			} else {
				if (!first_dst || ea < first_dst->ea)
					continue;
				flow = true;
			}
		}

		if (flow) {
			if (first_dst) {
				if (ea > first_dst->ea) {
					msg("AnalyzeOwn: internal error: %x > %x\n", ea, first_dst->ea);
					return false;
				}
				if (ea == first_dst->ea) first_dst = first_dst->next;
			}
			bb = bb->flow = GetBasblockAt(ea);
			bb->ref++;
		} else {

			// switch statement handling?
			if (ins.mnem == O_MOV && ins.op[0].reg == 15) {
				// switch statement.
				SwitchStatement *s = GetSwitchAt(switches,ea - 2);
				if (s && !CreateSwitchConds(bb, s)) {
					msg("CreateSwitchConds failure\n");
					return false;
				}
			}


			if (!first_dst)
				break;

			assert(first_dst->ea >= ea);

			ea = first_dst->ea;
			first_dst = first_dst->next;
			bb = GetBasblockAt(ea);
		}
	}
//	return false;
	return true;
}


Exp *Analyzer::CreateOpExp(const ArmOp &o)
{
	switch(o.type) {
	case O_REG: return NewRegExp(o.reg);
	case O_IMM: return NewConstExp(o.value);
	default:
		msg("CreateOpExp: unknown type\n");
		return NULL;
	}
}

Exp *Analyzer::CreateEffAddrExp(const ArmOp &o)
{
	if (o.type == O_MEM) {
		Exp *e = NewRegExp(o.reg);
		if (o.reg2 != 0xff) { e = NewBinExp(E_ADD, e, NewRegExp(o.reg2)); }
		if (o.value != 0) { e = NewBinExp(E_ADD, e, NewConstExp(o.value)); }
		return e;
	}
	msg("CreateEffAddrExp: unknown type\n");
	return NULL;
}

void Analyzer::CalcInstrFlags(Instr &i)
{
	_uses = _changes = 0;
	VisitUC(i.e);
	i.uses = (uint16)_uses;
	i.changes = (uint16)_changes;
}

// try to determine the calling convention for the call.
static uint32 GetCallingConventionFor(ea_t addr)
{
//	if (addr == 0x0809E458) return 0xF + (1<<7);
	if (addr == 0x83C0200) return 1<<4;
	if (addr == 0x83C01F8) return 1<<2;

	char buf[MAXSTR];


	if (print_type(addr, buf, sizeof(buf), true)) {
		uint32 ret = 0;

		if (!memcmp(buf, "int ", 4)) {
			ret |= CC_RET;
		}

		int args = 0;

		// parse the number of arguments
		int len = strlen(buf);
		if(len > 0)
		{
			if (buf[len-1] == ')' && buf[len-2] == '(') {
				args = 0;
			} else {
				args++;
				for(int i=0; buf[i]; i++)
					if (buf[i] == ',')
						args++;
			}
		}

		// remember # args
		ret |= ((1<<args)-1);

		return ret | CC_USER;
	}


#if 0
	type_t ti[MAXSTR];
	p_list pl[MAXSTR];

	if (!get_ti(addr, ti,pl)) {

//		msg("Type for %x is unknown\n", addr);
		return 0; // unknown
	}
#endif
//	msg("Type for %x is known %d\n", addr, strlen((char*)ti))	;

	return 0;
}

static Exp *SetupCallConv(Exp *e)
{
	assert(e->type == E_CALL);
	e->call.conv = GetCallingConventionFor(e->call.addr);

	if (e->call.conv) {
		uint n = 0;
		for(uint i=0; i!=16; i++) {
			if (HASBIT(e->call.conv, i) && n < 4) {
				e->call.arg[n++] = NewRegExp(i);
			}
		}
	}

	if (e->call.conv & CC_RET)
		e = NewMovExp(0, e);
	return e;
}

#define BINOP(ooo,xxx) case ooo: t = xxx; goto binop_handler;
#define UNOP(ooo,xxx)  case ooo: t = xxx; goto unop_handler;
#define LOADOP(ooo,xxx)  case ooo: t = xxx; goto load_handler;
#define STOREOP(ooo,xxx)  case ooo: t = xxx; goto store_handler;
#define CONDOP(ooo,xxx)  case ooo: t = xxx; goto cond_handler;


void Analyzer::MkInstr(Instr &i, Exp *e, addr_t ea)
{
	i.e = e;
	i.addr = ea;
	CalcInstrFlags(i);
}

void Analyzer::CreateInstruction(const ArmIns &ai, addr_t ea, BasicBlock *bb)
{
	int t;
	Exp *e;

	switch(ai.mnem) {
	case O_MOV:
		e = NewMovExp(ai.op1.reg, CreateOpExp(ai.op2));
		break;

	BINOP(O_AND, E_AND)
	BINOP(O_EOR, E_EOR)
	BINOP(O_LSL, E_LSL)
	BINOP(O_LSR, E_LSR)

	BINOP(O_ASR, E_ASR)
//	BINOP(O_ADC, E_ADC)
//	BINOP(O_SBC, E_SBC)
	BINOP(O_ROR, E_ROR)

	BINOP(O_ORR, E_ORR)
	BINOP(O_MUL, E_MUL)
	BINOP(O_BIC, E_BIC)

	BINOP(O_ADD, E_ADD)
	BINOP(O_SUB, E_SUB)
binop_handler:
	if (ai.op3.type) {
		e = NewMovExp(ai.op1.reg, NewBinExp(t, CreateOpExp(ai.op2), CreateOpExp(ai.op3)));
	} else {
		e = NewMovExp(ai.op1.reg, NewBinExp(t, CreateOpExp(ai.op1), CreateOpExp(ai.op2)));
	}
	break;

	UNOP(O_NEG, E_NEG)
	UNOP(O_MVN, E_MVN)
unop_handler:
	e = NewMovExp(ai.op1.reg, NewUnExp(t, CreateOpExp(ai.op2)));
	break;

	LOADOP(O_LDR, T_I32)
	LOADOP(O_LDRB, T_U8)
	LOADOP(O_LDRH, T_U16)
	LOADOP(O_LDSB, T_I8)
	LOADOP(O_LDSH, T_I16)
load_handler:
	e = NewMovExp(ai.op1.reg, NewLoadExp(t, CreateEffAddrExp(ai.op2)));
	break;

	STOREOP(O_STR, T_I32)
	STOREOP(O_STRB, T_U8)
	STOREOP(O_STRH, T_U16)
store_handler:
	e = NewStoreExp(t, CreateEffAddrExp(ai.op2), CreateOpExp(ai.op1));
	break;

	case O_BL: {
		e = SetupCallConv(NewCallExp(ai.op1.value));
		break;
	}

	// handle the LDMIA   R0, {R1} case
	case O_LDMIA: {
		// check that a single bit is set
		uint r;

		for(r=0; r!=8; r++) {
			if (ai.op2.value == (uint)(1 << r))
				break;
		}

		if (r == 8) goto unhandled_handler;

		// translate this into..
		// LOAD R1,[R0]
		// R0 = R0 + 4

		MkInstr(bb->instr.Append(), NewMovExp(r, NewLoadExp(T_I32, NewRegExp(ai.op1.reg))), ea);
		e = NewMovExp(ai.op1.reg, NewBinExp(E_ADD, NewRegExp(ai.op1.reg), NewConstExp(4)));
		break;
	}

	// handle the STMIA   R5, {R4} case

	case O_STMIA:
{
		// check that a single bit is set
		uint r;

		for(r=0; r!=8; r++) {
			if (ai.op2.value == (uint)(1 << r))
				break;
		}

		if ( r == 8) goto unhandled_handler;

		// translate this into..
		// STORE R1,[R0]
		// R0 = R0 + 4

		MkInstr(bb->instr.Append(), NewStoreExp(T_I32,NewRegExp(r), NewRegExp(ai.op1.reg)), ea);
		e = NewMovExp(ai.op1.reg, NewBinExp(E_ADD, NewRegExp(ai.op1.reg), NewConstExp(4)));
		break;
	}

	case O_PUSH:
	case O_POP:
	case O_SWI:
	case O_TST:
	case O_CMP:
	case O_CMN:
	case O_ADC:
	case O_SBC:
	case O_BX:
	case O_B:
unhandled_handler:
	  e = NewOtherExp(ai);
		break;

	CONDOP(O_BEQ, E_COMP_EQ)
	CONDOP(O_BNE, E_COMP_NE)
	CONDOP(O_BCS, E_COMP_CS)
	CONDOP(O_BCC, E_COMP_CC)
	CONDOP(O_BMI, E_COMP_MI)
	CONDOP(O_BPL, E_COMP_PL)
	CONDOP(O_BVS, E_COMP_VS)
	CONDOP(O_BVC, E_COMP_VC)
	CONDOP(O_BHI, E_COMP_HI)
	CONDOP(O_BLS, E_COMP_LS)
	CONDOP(O_BGE, E_COMP_GE)
	CONDOP(O_BLT, E_COMP_LT)
	CONDOP(O_BGT, E_COMP_GT)
	CONDOP(O_BLE, E_COMP_LE)
cond_handler: {
		Exp *b = bb->instr.GetCount() == 0 ? NULL : bb->instr[bb->instr.GetCount()-1].e;
		// This is a tricky one.
		// Check if the instruction before was a compare instruction.
		// if it was, generate an appropriate cond expression.
		if (!b || b->type != E_OTHER) goto unhandled_handler;

		if (b->other.ins.mnem == O_CMP) {
			e = NewCondExp(NewBinExp(t, CreateOpExp(b->other.ins.op1), CreateOpExp(b->other.ins.op2)));
		} else if (b->other.ins.mnem == O_CMN) {
			e = NewCondExp(NewBinExp(t, CreateOpExp(b->other.ins.op1), NewUnExp(E_NEG, CreateOpExp(b->other.ins.op2))));
		} else
			goto unhandled_handler;

		// delete the old otherexp from the array...
		bb->instr.SetCount(bb->instr.GetCount() - 1);
		break;
	}

	default:
		{
			msg("CreateInstruction: not found %s\n", _mnems[ai.mnem]);
			return;
		}
	}
	MkInstr(bb->instr.Append(), e, ea);
}

struct SwiInfo {
	uint16 uses;
	uint16 changes;
	const char *name;
};

static const SwiInfo _swi_info[] = {
	{0,0,"SoftReset"}, // 00h
	{0,0,"RegisterRamReset"}, // 01h
	{0,0,"Halt"}, // 02h
	{0,0,"Stop"}, // 03h
	{0,0,"IntrWait"}, // 04h
	{0,0,"VBlankIntrWait"}, // 05h
	{0,0,"Div"}, // 06h
	{0,0,"DivArm"}, // 07h
	{0,0,"Sqrt"}, // 08h
	{0,0,"ArcTan"}, // 09h
	{0,0,"ArcTan2"}, // 0Ah
	{0,0,"CpuSet"}, // 0Bh
	{0,0,"CpuFastSet"}, // 0Ch
	{0,0,"GetBiosChecksum"}, // 0Dh
	{0,0,"BgAffineSet"}, // 0Eh
	{0,0,"ObjAffineSet"}, // 0Fh
	{0,0,"BitUnPack"}, // 10h
	{0,0,"LZ77UnCompWram"}, // 11h
	{0,0,"LZ77UnCompVram"}, // 12h
	{0,0,"HuffUnComp"}, // 13h
	{0,0,"RLUnCompWram"}, // 14h
	{0,0,"RLUnCompVram"}, // 15h
	{0,0,"Diff8bitUnFilterWram"}, // 16h
	{0,0,"Diff8bitUnFilterVram"}, // 17h
	{0,0,"Diff16bitUnFilter"}, // 18h
	{1,0,"SoundBias"}, // 19h
	{0,0,"SoundDriverInit"}, // 1Ah
	{0,0,"SoundDriverMode"}, // 1Bh
	{0,0,"SoundDriverMain"}, // 1Ch
	{0,0,"SoundDriverVSync"}, // 1Dh
	{0,0,"SoundChannelClear"}, // 1Eh
	{0,0,"MidiKey2Freq"}, // 1Fh
};

void Analyzer::VisitUC(Exp *e)
{
	switch(e->type) {
	case E_CONST: return;
	case E_REG:  _uses |= 1 << e->reg; return;
	case E_MOV: _changes |= 1 << e->mov.reg; VisitUC(e->mov.e); return;
	case E_BIN:
		VisitUC(e->bin.left);
		VisitUC(e->bin.right);
		return;
	case E_UN:
		VisitUC(e->un.left);
		return;
	case E_STOR:
		VisitUC(e->store.ea);
		VisitUC(e->store.value);
		return;
	case E_LOAD:
		VisitUC(e->load.ea);
		return;
	case E_CALL:
		_uses |= e->call.conv & 0xFFFF;
		_changes |= 0xF;
		return;

	case E_OTHER: {
		switch(e->other.ins.mnem) {
		case O_PUSH: _uses |= e->other.ins.op1.value; break;
		case O_POP:  _changes |= e->other.ins.op1.value; break;
		case O_LDMIA:
		case O_STMIA:
			_uses |= 1<<e->other.ins.op1.reg;
			_changes |= 1<<e->other.ins.op1.reg;
			break;
		case O_SWI:
			if ((uint)e->other.ins.op1.value < lengthof(_swi_info)) {
				_uses |= _swi_info[e->other.ins.op1.value].uses;
				_changes |= _swi_info[e->other.ins.op1.value].changes;
			}
			break;

		}
		return;
	}
	case E_COND:
		VisitUC(e->cond.e);
		return;
	case E_CHOOSE:
		VisitUC(e->choose.e);
		VisitUC(e->choose.left);
		VisitUC(e->choose.right);
		break;
	case E_RETURN:
		assert(0);
		break;
	default:
		assert(0);
	}
}

Exp *DuplicateExp(Exp *e)
{
	switch(e->type) {
	case E_CONST: return NewConstExp(e->num);
	case E_REG:		return NewRegExp(e->reg);
	case E_MOV:		return NewMovExp(e->mov.reg, DuplicateExp(e->mov.e));
	case E_BIN:		return NewBinExp(e->bin.subtype, DuplicateExp(e->bin.left), DuplicateExp(e->bin.right));
	case E_UN:		return NewUnExp(e->un.subtype, DuplicateExp(e->un.left));
	case E_OTHER:	return NewOtherExp(e->other.ins);
	case E_LOAD:  return NewLoadExp(e->load.subtype, DuplicateExp(e->load.ea));
	case E_STOR:  {
		Exp *t = NewStoreExp(e->store.subtype, DuplicateExp(e->store.ea), DuplicateExp(e->store.value));
		t->store.oper = e->store.oper;
		return t;
	}
	case E_CHOOSE: return NewChooseExp(DuplicateExp(e->choose.e),DuplicateExp(e->choose.left),DuplicateExp(e->choose.right));
	case E_RETURN: return NewReturnExp(e->ret.e ? DuplicateExp(e->ret.e) : NULL);
	default:
		msg("Unk type %d\n", e->type);
		assert(0);
	}
	return NULL;
}

bool _errr;

void Analyzer::ForEachNode(Exp **ep, ForEachCallback *func, uint mask, void *param)
{
	Exp *e = *ep;

	if (mask & (1<<e->type)) {
		Exp *f = func(e, param);
		if (f) {
			*ep = f;
			return;
		}
	}

	switch(e->type) {
	case E_MOV:
		ForEachNode(&e->mov.e, func, mask, param);
		return;
	case E_BIN:
		ForEachNode(&e->bin.left, func, mask, param);
		ForEachNode(&e->bin.right, func, mask, param);
		return;
	case E_UN:
		ForEachNode(&e->un.left, func, mask, param);
		return;
	case E_STOR:
		ForEachNode(&e->store.ea, func, mask, param);
		ForEachNode(&e->store.value, func, mask, param);
		return;
	case E_LOAD:
		ForEachNode(&e->load.ea, func, mask, param);
		return;
	case E_COND:
		ForEachNode(&e->cond.e, func, mask, param);
		return;
	case E_CONST:
	case E_OTHER:
	case E_REG:
		return;
	case E_CALL: {
		for(int i=0; i!=4; i++)
			if (e->call.arg[i])
				ForEachNode(&e->call.arg[i], func, mask, param);
		return;
	case E_CHOOSE:
		ForEachNode(&e->choose.e, func, mask, param);
		ForEachNode(&e->choose.left, func, mask, param);
		ForEachNode(&e->choose.right, func, mask, param);
		return;

	case E_RETURN:
		if (e->ret.e)
			ForEachNode(&e->ret.e, func, mask, param);
		return;

	}
	default:
		msg("Unknown Exp %x\n", e->type);
		_errr = true;
//		assert(0);
	}
}

bool Analyzer::IsConstantValue(Exp *e, uint32 &num)
{
	uint32 tmp1,tmp2;

	switch(e->type) {
	case E_CONST:
		num = e->num;
		return true;
	case E_BIN: {
		assert(e->bin.left != e && e->bin.right != e);
		if ( !IsConstantValue(e->bin.left,tmp1) || !IsConstantValue(e->bin.right,tmp2))
			return false;

		uint32 r=tmp1,s=tmp2;
		switch(e->bin.subtype) {
		case E_AND: r &= s; break;
		case E_EOR: r ^= s; break;
		case E_LSL: r <<= s; break;
		case E_LSR: r >>= s; break;
		case E_ASR: r >>= s; break;
		case E_ROR: return false;
		case E_ORR: r |= s; break;
		case E_MUL: r *= s; break;
		case E_BIC: r &= ~s; break;
		case E_ADD: r += s; break;
		case E_SUB: r -= s; break;
		default:
			return false;
		}
		num = r;
		return true;
	}
	case E_UN:
		if (!IsConstantValue(e->un.left,tmp1))
			return false;
		switch(e->un.subtype) {
		case E_MVN: num = ~tmp1; break;
		case E_NEG: num = -(long)tmp1; break;
		default:
			return false;
		}
		return true;
	default:
		return false;
	}
}

static Exp *IsBinOpWithConstant(Exp *e, byte op, uint32 &num)
{
	if (e->type != E_BIN || e->bin.subtype != op)
		return NULL;

	if (e->bin.right->type != E_CONST)
		return NULL;

	num = e->bin.right->num;
	return e->bin.left;
}

static Exp *IsAnyBinOpWithConstant(Exp *e, byte &subtype, uint32 &num)
{
	if (e->type != E_BIN)
		return NULL;

	if (e->bin.right->type != E_CONST)
		return NULL;

	subtype = e->bin.subtype;
	num = e->bin.right->num;
	return e->bin.left;
}

static Exp *MkAddMul(Exp *e, uint32 add, uint32 mul)
{
	if (mul != 1) e = NewBinExp(E_MUL, e, NewConstExp(mul));
	if (add != 0) {

		if ( (signed long)add >= -65535 && (signed long) add < 0)
			e = NewBinExp(E_SUB, e, NewConstExp(-(long)add));
		else
			e = NewBinExp(E_ADD, e, NewConstExp(add));
	}
	return e;
}

Exp *IsAddMul(Exp *e, AddMulStruct &ams)
{
	Exp *next;
	ams.add = 0;
	ams.mul = 1;
	int step = 0;

	while (e->type == E_BIN) {
		uint32 constant;

		if (e->bin.left->type == E_CONST) {
			constant = e->bin.left->num;
			next = e->bin.right;
		} else if (e->bin.right->type == E_CONST) {
			constant = e->bin.right->num;
			next = e->bin.left;
		} else
			break;

		if (e->bin.subtype == E_ADD) {
			if ((signed long)constant >= -65535 && (signed long) constant < 0) step = 10;
			ams.add += constant * ams.mul;
		} else if (e->bin.subtype == E_MUL) {
			ams.mul *= constant;
		} else if (e->bin.subtype == E_LSL && next == e->bin.left) {
			ams.mul *= (1 << constant);
		} else if (e->bin.subtype == E_SUB && next == e->bin.left) {
			ams.add += (-(long)constant) * ams.mul;
		} else
			break;

		step++;
		if (next != e->bin.left) step = 10; // not good

		e = next;
	}

	ams.normal = step == (ams.add != 0) + (ams.mul != 1);
	return e;
}


// try to express it on the form
// ((E >> SHIFT) & AND | OR) << LSHIFT

struct AndOrShiftStruct {
	uint32 and;
	uint32 or;
	int shift;
	bool normal;
};

static inline uint32 Shift(uint32 v, int n)
{
	return n >= 0 ? v << n : v >> (-n);
}



//((X&C)>>S)&A|O --> (X>>S)&((C>>S)&A)|O
//((X|C)>>S)&A|O --> ( (X>>S) | (C>>S) ) & A|O  --> (X>>S) & A | ((C>>S) & A | O)

//(A & 2)	<< 24 >> 25
// shift = -25, and = 0xfe000000, or = 0
// shift = -1, and = 0x000000fe, or = 0
// shift = -1, and =

//(X>>C) -> (X

Exp *IsAndOrShift(Exp *e, AndOrShiftStruct &aos)
{
	aos.and = 0xffffffff;
	aos.or = 0;
	aos.shift = 0;
	int step = 0;

	while (e->type == E_BIN) {
		uint32 constant;
		Exp *next;

		if (e->bin.left->type == E_CONST) {
			constant = e->bin.left->num;
			next = e->bin.right;
		} else if (e->bin.right->type == E_CONST) {
			constant = e->bin.right->num;
			next = e->bin.left;
		} else
			break;

		if (e->bin.subtype == E_AND) {
			aos.and &= Shift(constant, aos.shift);
			step |= step & ~3 ? -1 : 4;
		} else if (e->bin.subtype == E_ORR) {
			aos.or |= Shift(constant,aos.shift) & aos.and;
			step |= step & ~1 ? -1 : 2;
		} else if (e->bin.subtype == E_LSL && next == e->bin.left) {
			aos.shift += constant;
			step |= step ? -1 : 1;
			aos.and &= Shift(0xFFFFFFFF, aos.shift);
		} else if (e->bin.subtype == E_LSR && next == e->bin.left) {
			aos.shift -= constant;
			step |= step & ~6 ? -1 : 8;
			aos.and &= Shift(0xFFFFFFFF, aos.shift);
		} else
			break;

		if (next != e->bin.left) step = -1;

		e = next;
	}

	aos.normal = (step != -1);
	return e;
}

Exp *MkAndOrShift(Exp *e, uint32 and, uint32 or, int shift)
{
	if (shift<0) {
		e = NewBinExp(E_LSR, e, NewConstExp(-shift));
	} else {
		and >>= shift;
		or >>= shift;
	}
	if (or |= 0) e = NewBinExp(E_ORR, e, NewConstExp(or));
	if (and != Shift(0xffffffff,-shift)) e = NewBinExp(E_AND, e, NewConstExp(and));
	if (shift>0) { e = NewBinExp(E_LSL, e, NewConstExp(shift));  }
	return e;
}


static uint32 ResolveMemContents(uint32 v)
{

#if 0
	// SMW
	if (v == 0x3007A48) return 0x300302C; // N/A
	if (v == 0x3007A38) return 0x30040E8; // 0x1DC bytes big. Allocated on heap.
	if (v == 0x3002360) return 0x30042C8; // 0x154 bytes big.
	if (v == 0x3003F98) return 0x3004420; // 0x11F0 bytes big.
	if (v == 0x3003F9C) return 0x3005614; // 0x18C bytes big
#elif 1
	// PINBALL
	if (v == 0x02000898) return 0x03008000;
	if (v == 0x20019B4) return 0x2000E90; // replace object_struct_ptr with object_struct
	if (v == 0x2000F4C) return 0x3008000 + 0x64; // points into the gamedesc struct
#else
#endif
	return 0;
}

Exp *Analyzer::SimplifyConstantsCallback(Exp *e, void *p)
{
	uint32 num, num2;
	byte subtype;

	if (e->type == E_LOAD) {
		if (e->load.subtype == T_I32 && e->load.ea->type == E_CONST) {
			uint32 x = ResolveMemContents(e->load.ea->num);
			if (x) return NewConstExp(x);
		}
		return NULL;
	}

	Exp *et;
	if (IsConstantValue(e, num))
		return NewConstExp(num);


	// try to simplify things on the form
	// X << 0x18 >> 0x18

#define MATCH(a,b,c) ((et=IsBinOpWithConstant(a, b, c)) != NULL)
#define MATCH2(a,b,c)  ((et=IsAnyBinOpWithConstant(a, b, c)) != NULL)
	if (MATCH(e,E_ASR,num)) {
		if (MATCH(et,E_LSL,num2)) {
			if ((num2 == 0x18 || num2 == 0x10) && num <= num2) {
				// found arithmetic sign extend. check if the operand is a unsigned load operation of the right size.
				if (et->type == E_LOAD) {
					if (num2 == 0x10 && et->load.subtype == T_U16) { et->load.subtype = T_I16; goto fixup_const; }
					if (num2 == 0x18 && et->load.subtype == T_U8) { 	et->load.subtype = T_I8; 	goto fixup_const; }
				}
				et = NewUnExp((num2 == 0x18) ? E_FROM_I8 : E_FROM_I16, et);
fixup_const:
				if (num2 != num) et = NewBinExp(E_LSL, et, NewConstExp(num2 - num));
				return et;
			}
		}
	}

#define MASK(n) ( (1<<(32 - (n)))-1)
	uint32 addval;
	if (MATCH(e,E_LSR,num) && MATCH(et,E_ADD,addval) && addval != 0 && (addval & MASK(num)) == 0 && MATCH(et,E_LSL,num2) && (num2 == 0x18 || num2 == 0x10) && num2 == num) {
		et = MkAddMul(et, (long)addval >> num, 1);
		et = NewBinExp(E_AND, et, NewConstExp(MASK(num)));
		return et;
	}

	if ( MATCH2(e,subtype,num) && subtype >= E_COMP_EQ && subtype <= E_COMP_LE && num == 0) {
		Exp *tmp = et;

		if (MATCH(et,E_LSL,num2)) {
			// EXP << 5  < 0    ==>  EXP & 0x80000
			// EXP << 5  >= 0   ==>  !(EXP & 0x80000)
			if (subtype == E_COMP_CS || subtype == E_COMP_CC) {
				et = NewBinExp(E_AND, et, NewConstExp( (1<<(31 - num2))));
				if (subtype == E_COMP_CC) et = MakeLNot(et);
				return et;
			}
			if (num2 == 0x10 || num2 == 0x18) {
				assert(e->bin.left == tmp);
				e->bin.left = NewUnExp( num2 == 0x18 ? E_FROM_I8 : E_FROM_I16, et);
				return e;
			}
		}
	}


	AddMulStruct ams;
	et = IsAddMul(e, ams);

	if (et->type == E_BIN && et->bin.subtype == E_ADD) {
		AddMulStruct ams1,ams2;
		Exp *a = IsAddMul(et->bin.left, ams1);
		Exp *b = IsAddMul(et->bin.right,ams2);

		// check if both of them reference a register
		if (a->type == E_REG && b->type == E_REG && a->reg == b->reg)
			return MkAddMul(a, (ams1.add + ams2.add) * ams.mul + ams.add, (ams1.mul + ams2.mul) * ams.mul);

		if (ams1.add != 0 && ams2.add != 0) {
			et->bin.left = MkAddMul(a, 0, ams1.mul);
			et->bin.right = MkAddMul(b, 0, ams2.mul);
			return MkAddMul(et, (ams1.add + ams2.add) * ams.mul + ams.add, ams.mul);
		}
	}
	// check if the addmul can be simplified?
	if (!ams.normal) {
		return MkAddMul(et, ams.add, ams.mul);
	}

#if 1
	AndOrShiftStruct aos;
	et = IsAndOrShift(e, aos);
	if (!aos.normal) {
//		printexp(e);
//		msg("\nMkAndOrShift(0x%x,0x%x,%d)\n", aos.and, aos.or, aos.shift);
		e=MkAndOrShift(et, aos.and, aos.or, aos.shift);
//		printexp(e);
//		msg("\n*\n");
		return e;
	}
#else
	{
		uint32 and=0xFFFFFFFF, or=0;

		// combine multiple and into a single and
		if (MATCH(e, E_AND, and) || MATCH(e,E_ORR,or)) {
			Exp *last = et;
			uint ch = 1;

			for(;;) {
				if (MATCH(last, E_AND, num)) {
					and &= num;
				} else if (MATCH(last, E_ORR, num)) {
					or |= (num & and);
				} else
					break;
				ch++;
				last = et;
			}

			ch -= (and != 0xffffffff) + (or != 0);
			if (ch) {
				if (and != 0xffffffff) last = NewBinExp(E_AND, last, NewConstExp(and));
				if (or != 0) last = NewBinExp(E_ORR, last, NewConstExp(or));
				return last;
			}
		}
	}
#endif

	return NULL;
}

void Analyzer::SimplifyConstants(Exp **e)
{
	ForEachNode(e, SimplifyConstantsCallback, 1<<E_BIN | 1<<E_UN | 1<<E_LOAD, NULL);
}

void Analyzer::ComputeUsesWrites(BasicBlock *bb)
{
	uint32 writes = 0;
	uint32 uses = 0;

	// compute uses/changes field for each instruction
	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];
		uses |=  i.uses & ~writes;
		writes |= i.changes;
	}

	bb->uses2 = bb->uses = uses;
	bb->writes = writes;
}

void Analyzer::ComputeUsesWrites()
{
	BasicBlock *bb;
	bool changed;
	int iterations = 0;

	// fix point iteration
	// propagate the uses fields of the children onto the parent, unless the parent writes to this register as well.
	// iterate until nothing chnages.
	do {
		changed = false;
		for(bb = _list; bb; bb = bb->next) {
			uint32 uses = 0;
			if (bb->flow) uses |= bb->flow->uses;
			if (bb->cond) uses |= bb->cond->uses;
			bb->liveout = uses;

			// for each variable that the parent doesn't write to, and the child needs, propagate to parent.
			uses = (uses &~ bb->writes) | bb->uses;

			if (bb->uses != uses) {
				bb->uses = uses;
				changed = true;
			}
		}
		iterations++;
	} while (changed);

//	msg("ComputeUsesWrites: %d iterations\n", iterations);
}

// determine the values of the registers after executing the basic block
// rs_cond contains the register state if the conditional jump is taken.
// rs_flow contains the register state for normal flow
void Analyzer::ComputeRegisterState(BasicBlock *bb, RegState *rs_flow, RegState *rs_cond)
{
	RegState rs = bb->rs;
	uint32 cmp_const = 0;
	RegState *cmp_rs = NULL;
	uint cmp_reg = 0;

	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];

		// we only handle loading simple constants into registers.
		// also handle move from one register to another.
		if (i.e->type == E_MOV) {
			uint r = i.e->mov.reg;
			if (r <= 12) {
				if (IsConstantValue(i.e->mov.e, rs.values[r])) {
					// constant value!!
					rs.changed |= 1<<r;
					rs.known |= 1<<r;
					continue;
				} else if (i.e->mov.e->type == E_REG) {
					uint r2 = i.e->mov.e->reg;
					if (rs.known & (1 << r2)) {
						rs.changed |= 1<<r;
						rs.known |= 1<<r;
						rs.values[r] = rs.values[r2];
						continue;
					}
				}
			}
		} else if (i.e->type == E_COND && i.e->cond.e->type == E_BIN) {
			Exp *e = i.e->cond.e;
			// if a register is compared to a known value, then for the EQUAL branch,
			// we know the value of the register. Only works for == or !=
			// also check if one side of the compare is a register, and the other side is a constant.
			if ((e->bin.subtype == E_COMP_EQ || e->bin.subtype == E_COMP_NE) && e->bin.left->type == E_REG) {
				bool good = false;

				cmp_reg = e->bin.left->reg;

				if (e->bin.right->type == E_CONST) {
					cmp_const = e->bin.right->num;
					good = true;
				} else if (e->bin.right->type == E_REG) {
					if (rs.known & (1 << e->bin.right->reg)) {
						cmp_const = rs.values[e->bin.right->reg];
						good = true;
					}
				}
				if (good) {
					cmp_rs = (e->bin.subtype == E_COMP_EQ) ? rs_cond : rs_flow;
				}
			}
		}
		// if the instruction overwrites a register, update the regstate.
		rs.changed |= i.changes;
		rs.known &= ~i.changes;
	}

	if (rs_flow) memcpy(rs_flow, &rs, sizeof(rs));
	if (rs_cond) memcpy(rs_cond, &rs, sizeof(rs));

	if (cmp_rs) {
		cmp_rs->changed |= (1 << cmp_reg);
		cmp_rs->known |= (1 << cmp_reg);
		cmp_rs->values[cmp_reg] = cmp_const;
	}
}

static Exp *ReplaceReg(Exp *e, void *p)
{
	if (e->reg == ((uint32*)p)[0]) {
		return NewConstExp(((uint32*)p)[1]);
	}
	return NULL;
}

void dbgme(BasicBlock *bb, const char *x)
{
	for(;bb;bb=bb->next) {
	if (bb->base == 0x806D2B6)
		for(size_t j=0; j!=bb->num_instr; j++) {
			Instr &i = bb->instr[j];
			 if (i.changes == 8) { msg("%s: ", x); printexp(i.e); msg("\n"); return; }
		}
	}
}

// in basic block, starting at instruction start, search forward to see if reg
// can be replaced with value.
bool Analyzer::TryReplaceWithConst(BasicBlock *bb, uint start, uint reg, uint32 value)
{
	bool do_call_analysis = (start != 0 && reg < 4);
	bool can_remove = true;

	for(size_t j=start; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];

		if (do_call_analysis && i.e->type == E_CALL && i.e->call.arg[reg] == NULL && !(i.uses & (1 << reg))) {
			// a call instruction that uses the value in 'reg' that was never used before.
			i.e->call.arg[reg] = NewConstExp(value);
			return can_remove;
		}

		if (i.uses & (1<<reg)) {
			if (i.e->type == E_OTHER) {
				can_remove = false;
			} else {
				uint32 f[2] = {reg,value};
				ForEachNode(&i.e, ReplaceReg, 1<<E_REG, f);
				i.uses &= ~(1<<reg); // register is not used by the instruction anymore
			}
			do_call_analysis = false; // only do this for unused constants
		}

		// instruction overwrites register. stop here.
		if (i.changes & (1 << reg)) {
			return can_remove;
		}
	}

	if (bb->liveout & (1<<reg))
		can_remove = false;

	return can_remove;
}

static Exp *CallbCountReg(Exp *e, void *p)
{
	if (e->reg == ((uint32*)p)[0]) ((uint32*)p)[1]++;
	return NULL;
}

struct Ctx0 {
	byte reg;
	bool flag;
	Exp *e;
};

static Exp *ReplaceReg2(Exp *e, void *p)
{
	Ctx0 *c = (Ctx0*)p;
	if (e->reg == c->reg) {
		if (c->flag) {
			c->flag = false;
			return c->e;
		}
		return DuplicateExp(c->e);
	}
	return NULL;
}

static bool IsSimpleExpression(Exp *e, uint reg, bool liveout)
{
	if (e->type == E_REG) {
		return !liveout;
	}

	if (e->type == E_BIN && e->bin.left->type == E_REG && e->bin.right->type == E_CONST) {
		if (e->bin.left->reg == R_SP ||
				e->bin.left->reg == reg)
			return true;

		return !liveout;
	}

	if (e->type == E_BIN && e->bin.right->type == E_REG && e->bin.left->type == E_CONST) {
		return !liveout;
	}

	if (e->type == E_BIN && e->bin.right->type == E_CONST && e->bin.subtype == E_ADD) {
		return IsSimpleExpression(e->bin.left, reg, liveout);
	}

	return false;
}

LList<Exp*> items;
bool dupl;

static Exp *ValidateExp(Exp *e, void *p)
{
	if (items.LookupElement(e) == (size_t) -1) {
		items.Append(e);
	} else {
		dupl = true;
	}
	return NULL;
}

void Analyzer::Validate(const char *x)
{
	dupl = false;
	items.Init();

	for(BasicBlock *bb=_list; bb; bb=bb->next) {
		for(size_t j=0; j!=bb->num_instr; j++) {
			Instr &i = bb->instr[j];
			ForEachNode(&i.e, ValidateExp, 0xffffff, NULL);
		}
	}
	items.Free();

	msg("Validate %-10s %s\n", x, dupl ? "FAIL" : "ok");

}


bool Analyzer::TryReplaceWithExpr(BasicBlock *bb, uint start, uint reg, Exp *e, uint uses)
{
	// first we need to check if the register is a candidate for replacement.
	// conditions:
	//  * the written result is only used once, OR
	//  * the value is constant, OR

	int flags = 0;
	int num_refs = 0;

	for(size_t j=start; ; j++) {
		if (j==bb->num_instr) {
			// reached the end of the basic block. check if the register needs to be live on exit from the basic block.
			if (bb->liveout & (1 << reg))
				flags |= 4;
			break;
		}

		Instr &i = bb->instr[j];

		if (i.e->type == E_CALL && num_refs == 0 && flags == 0 && reg < 4 && i.e->call.arg[reg] == NULL && !(i.uses & (1 << reg))) {
			if (uses & 0xF) {
				i.e->call.arg[reg] = NewRegExp(reg);
				i.uses |= (1 << reg);
			} else {
				// a call instruction that uses the value in 'reg' that was never used before.
//				msg("%X: Found func arg %d. call uses %x, uses = %x\n", bb->base, reg, i.uses, uses);
				i.e->call.arg[reg] = e;
				i.uses |= uses;
				return true;
			}
		}

		if (i.uses & (1 << reg)) {
			if (flags) {
				flags |= 2; // this means that the register is used AFTER one of the dependent ones are modified.
			} else if (i.e->type == E_OTHER) {
				flags |= 2; // used for SWI and stuff..
			} else {
				// count number of places the register is used at....
				uint32 f[2] = {reg,0};
				ForEachNode(&i.e, CallbCountReg, 1<<E_REG, f);
				num_refs += f[1];
				if (f[1] == 0) {
					msg("f[1] error. R%d isn't found but uses is %x/%x at %d\n", reg, i.uses, i.changes, j);
					printbb(bb);
				}
//				assert(f[1] != 0);
			}
		}

		// instruction overwrites register. stop here.
		if (i.changes & (1 << reg))
			break;

		if (i.changes & uses) {
			// the instruction changes a register that exists in the replaced exp.
			flags |= 1;
		}
	}

	// never referenced?
	if (num_refs == 0)
		return false;


	// if the instruction can't be deleted because it's still needed,
	// and if the instruction modifies a register that it depends on,
	// then we can't do anything
	if ( (flags & 6) != 0 && (uses & (1 << reg)))
		return false;

	//SimpleThres st = {2,1,1<<reg|1<<R_SP};

	if (IsSimpleExpression(e,reg,(flags & 6) != 0)) {

	} else {
		if (num_refs != 1 || (flags & 6) != 0)
			return false;
	}

	Ctx0 ctx = { reg, (flags & 6) == 0, e };

	// do the actual replacement
	for(size_t j=start; j != bb->num_instr; j++) {
		Instr &i = bb->instr[j];

		if (i.uses & (1 << reg)) {
			ForEachNode(&i.e, ReplaceReg2, 1<<E_REG, &ctx);
			i.uses = (i.uses&~(1<<reg)) | uses;
		}
		if (i.changes & (uses | (1 << reg)))
			break;
	}

	// return TRUE if it should be deleted.
	return (flags & 6) == 0;
}


void Analyzer::PropagateInitialConsts(BasicBlock *bb)
{
	uint t = bb->uses2 & bb->rs.known;
	for(uint i=0; t; t>>=1, i++)
		if (t&1)
			TryReplaceWithConst(bb, 0, i, bb->rs.values[i]);
}

void Analyzer::KillInstr(BasicBlock *bb, uint j)
{
	assert(j < bb->num_instr);
	bb->instr.RemoveElement(j);
}


static Exp *ShouldMoveCallb(Exp *e, void *p)
{
	*(bool*)p = false;
	return NULL;
}

bool Analyzer::ShouldBeMoved(Exp *e)
{
	bool ok = true;
	ForEachNode(&e, ShouldMoveCallb, 1<<E_CALL | 1<<E_CHOOSE, &ok);
	return ok;
}

void ValidateRefs(BasicBlock *list, BasicBlock *bb, const char *m = "")
{
	size_t count = 0;
	for(;list;list=list->next) {
		if (list->flow == bb) count++;
		if (list->cond == bb) count++;
	}
	if (count != bb->ref) {
		msg("%x: Ref mismatch %s! %d vs %d\n", bb->base, m, count, bb->ref);
		*(byte*)0=0;
	}
}

static inline bool IsMov(Exp *e)
{
	return e->type == E_MOV;
}

static inline bool IsMov(Exp *e, byte reg)
{
	return e->type == E_MOV && e->mov.reg == reg;
}

static inline bool IsReg(Exp *e, byte reg)
{
	return e->type == E_REG && e->reg == reg;
}

static inline bool IsBin(Exp *e, byte subtype)
{
	return e->type == E_BIN && e->bin.subtype == subtype;
}

static inline bool IsConst(Exp *e, uint32 c)
{
	return e->type == E_CONST && e->num == c;
}

static inline bool IsBinConst(Exp *e, byte subtype, uint32 &c)
{
	if (e->type == E_BIN && e->bin.subtype == subtype && e->bin.right->type == E_CONST) {
		c = e->bin.right->num;
		return true;
	}
	return false;
}

static inline bool IsBinConst2(Exp *e, byte subtype, uint32 c)
{
	return e->type == E_BIN && e->bin.subtype == subtype && e->bin.right->type == E_CONST && e->bin.right->num == c;
}

struct Ctx1 {
	byte reg;
	byte reg2;
	uint32 shift;
};

static Exp *CheckSignExpOptimCallb(Exp *e, void *p)
{
	Ctx1 *c = (Ctx1*)p;

	if (e->type == E_BIN && IsReg(e->bin.left, c->reg)) {
		if (e->bin.subtype == E_ASR && IsConst(e->bin.right, c->shift)) {
			return e;
		} else if ((e->bin.subtype == E_COMP_EQ ||
								e->bin.subtype == E_COMP_NE ||
								e->bin.subtype == E_COMP_GE ||
								e->bin.subtype == E_COMP_LT ||
								e->bin.subtype == E_COMP_GT ||
								e->bin.subtype == E_COMP_LE) && IsConst(e->bin.right, 0)) {
			return e;
		}
	} else if (e->type == E_REG && e->reg == c->reg) {
		c->reg2 = 0;
	}

	return NULL;
}

static Exp *CheckSignExpOptimCallb2(Exp *e, void *p)
{
	Ctx1 *c = (Ctx1*)p;
	if (IsReg(e->bin.left,(byte)c->reg)) {
		Exp *xx = NewUnExp(c->shift == 0x10 ? E_FROM_I16 : E_FROM_I8, NewRegExp(c->reg2));
		if (e->bin.subtype == E_ASR) {
			return xx;
		} else {
			e->bin.left = xx;
			return e;
		}
	}
	return NULL;
}

static bool CheckSignExpOptim(Exp *e, byte reg, uint32 shift)
{
	Ctx1 ctx = { reg, true, shift };
	Analyzer::ForEachNode(&e, CheckSignExpOptimCallb, 1<<E_BIN | 1<<E_REG, &ctx);
	return *(bool*)&ctx.reg2;
}

static bool IsLiveOnEntry(BasicBlock *bb, uint j, byte reg)
{
	return false;
}

void Analyzer::SimplifyBB(BasicBlock *bb)
{
	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];

		SimplifyConstants(&i.e);

	// for each store instruction, see if it's on the form
	// byte<EXP> = byte<EXP> ???
	// if it is, it can be simplified
		if (i.e->type == E_STOR && i.e->store.oper == 0)
			TrySimplifyStore(i.e->store.value, i.e->store.ea, i.e->store.subtype, i.e->store.oper);


		// Check if it's on the form
		//ROM:08022C02 82                R0 = (R6 << 0x18) + 0xFF000000
		//ROM:08022C03 46                R6 = R0 >> 0x18
		//ROM:08022C04 47              } while (R0 >= 0)

		uint32 addv,lslv;
		if (j <= bb->num_instr - 3 && IsMov(i.e) && IsBinConst(i.e->mov.e, E_ADD,addv) && IsBinConst(i.e->mov.e->bin.left, E_LSL, lslv) && (lslv == 0x10 || lslv == 0x18)) {
			Instr &n = bb->instr[j + 1];
			Instr &m = bb->instr[j + 2];
			if (IsMov(n.e) && IsBinConst2(n.e->mov.e, E_LSR, lslv) && IsReg(n.e->mov.e->bin.left, i.e->mov.reg) && CheckSignExpOptim(m.e,i.e->mov.reg, lslv) && !IsLiveOnEntry(bb, j+3, i.e->mov.reg)) {
				Ctx1 ctx = {i.e->mov.reg, n.e->mov.reg, lslv};
				int r = i.e->mov.e->bin.left->bin.left->reg;
				n.e->mov.e = NewUnExp(
					lslv == 0x18 ? E_FROM_U8 : E_FROM_U16,
					MkAddMul(
						NewRegExp(r),
						(long)addv >> lslv, 1));
				ForEachNode(&m.e, CheckSignExpOptimCallb2, 1<<E_BIN, &ctx);

				// Update uses/changes
				n.uses = MKBIT(r);
				n.changes = MKBIT(ctx.reg2);
				CLRBIT(m.uses, ctx.reg);
				SETBIT(m.uses, ctx.reg2);

				KillInstr(bb, j);
				j--;
			}
		}


	}

	// for each assignment instruction in the basic block, see if the assigned expression
	// can be propagated and if the register can be eliminated.
	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];

		// first try and simplify the expression
		SimplifyConstants(&i.e);

		if (i.e->type != E_MOV)
			continue;

		int r = i.e->mov.reg;

		if (i.e->mov.e->type == E_CONST) {
			if (!TryReplaceWithConst(bb, j+1, i.e->mov.reg, i.e->mov.e->num))
				continue;
		} else {
			if (!TryReplaceWithExpr(bb, j+1, i.e->mov.reg, i.e->mov.e, i.uses))
				continue;
		}

		// instruction is not needed anymore. delete it.
		KillInstr(bb, j);
		j--;

		if ((int)j >= 0 && HASBIT(bb->instr[j].uses, r)) { j--; }
	}

	// check if the next basic block is a very simple one, and if it's a good idea to propagate
	// that instruction up to here.
	if (bb->flow && !bb->cond && !bb->flow->cond && bb->num_instr != 0 && bb->flow->num_instr == 1 && bb != bb->flow->flow) {
		Instr &i = bb->instr[bb->num_instr - 1];
		Instr &j = bb->flow->instr[0];
		if ((j.e->type == E_STOR||j.e->type == E_MOV) && i.e->type == E_MOV && (j.uses & i.changes) != 0 && ShouldBeMoved(j.e)) {
			// yes.. copy it up
			Instr &tmp = bb->instr.Append();
			tmp = j;
			tmp.e = DuplicateExp(tmp.e);

			assert(bb != bb->flow);

			BasicBlock *f = bb->flow;
			bb->flow = f->flow;
			if (!--f->ref)
				DestroyBB(f);
			else if (f->flow)
				f->flow->ref++;

		}
	}

}

static bool MergeRegisterState(RegState *d, const RegState *s)
{
	bool changes = false;

	uint dk = d->known;
	uint dc = d->changed;

	for(uint i=0; i!=13; i++) {
		uint m = 1<<i;

		if (s->changed & m) {
			if (dk & m) {
				if (!(s->known & m) || s->values[i] != d->values[i]) {
					dk ^= m;
					changes = true;
				}
			} else if (!(dc & m)) {
				dc |= m;
				dk |= s->known & m;
				d->values[i] = s->values[i];
				changes = true;
			}
		}
	}

	d->known = dk;
	d->changed = dc;

	return changes;
}

void Analyzer::ComputeRegisterState()
{
	BasicBlock *bb;
	bool changed;
	int iterations = 0;

	RegState rs_flow, rs_cond;

	// initialize all register states to zero
	for(bb = _list; bb; bb = bb->next) {
		memset(&bb->rs, 0, sizeof(bb->rs));
	}

	// fix point iteration until nothing changes
	do {
		changed = false;
		for(bb = _list; bb; bb = bb->next) {
			ComputeRegisterState(bb, &rs_flow, &rs_cond);
			if (bb->flow) changed |= MergeRegisterState(&bb->flow->rs, &rs_flow);
			if (bb->cond) changed |= MergeRegisterState(&bb->cond->rs, &rs_cond);
		}
		iterations++;
		if (iterations > 1000)
			break;
	} while (changed);

//	msg("ComputeRegisterState: %d iterations\n", iterations);
}

Exp *GetIfExp(BasicBlock *bb)
{
	Exp *e = bb->instr[bb->num_instr-1].e;
	assert(e->type == E_COND);
	return e->cond.e;
}


bool IsReturn(BasicBlock *bb)
{
	return bb->flow == NULL &&
		(bb->num_instr == 0 || (bb->num_instr == 1 && bb->instr[bb->num_instr-1].e->type == E_RETURN));
}

static Exp *GetReturnExp(BasicBlock *bb)
{
	assert(bb->flow == NULL);
	if (bb->num_instr == 0) return NULL;
	assert(bb->num_instr == 1);
	assert(bb->instr[bb->num_instr-1].e->type == E_RETURN);
	return bb->instr[bb->num_instr-1].e->ret.e;
}

EmittedEnt *NewEmitGoto(BasicBlock *bas)
{
	while (bas && bas->num_instr == 0 && bas->flow != bas)
		bas = bas->flow;

	if (bas == NULL) {
		return NewEmitReturn(NULL);
	}
	if (IsReturn(bas))
		return NewEmitBas(bas);//Return(GetReturnExp(bas));

	EmittedEnt *ee = new EmittedEnt(EE_GOTO);

	ee->bas.bas = bas;
	bas->need_label = true;
	return ee;
}


static bool MakeGotoFromIf(BasicBlock *bb, BasicBlock *cond, BasicBlock *els, BasicBlock *stopper)
{
	if (els->cond == NULL && els->flow == cond)
		return false;


//	msg("%d: %d\n", bb->order, IsReturn(cond));
	// make sure we use "return" as often as possible.
	if (IsReturn(cond))
		return true;

	if (cond == stopper)
		return false;

	if (cond->written)
		return true;

	if (cond->ref - cond->back_ref <= 1)
		return false;

	if (bb->loop_head == cond->loop_head)
		return false;

	return stopper && cond->order > stopper->order;
}

bool Analyzer::EeReachesEnd(EmittedEnt *ee)
{
	if (ee == NULL)
		return true;

	// jump to the last item
	while (ee->next) ee = ee->next;

	switch(ee->type) {
	case EE_BAS: {
		BasicBlock *b = ee->bas.bas;
		if (b->num_instr > 0 &&
				b->instr[b->num_instr-1].e->type == E_RETURN)
			return false;
		break;
	}
	case EE_RETURN:
	case EE_GOTO:
		return false;

	case EE_IF:
		if (ee->cond.left && ee->cond.right) {
			if (!EeReachesEnd(ee->cond.left) && !EeReachesEnd(ee->cond.right))
				return false;
		}
		break;

	case EE_ENDLESS:
		// check if it's an endless loop
		if (ee->loop.body == NULL)
			return false;
		break;
	}
	return true;
}

int Analyzer::EeDepth(EmittedEnt *ee)
{
	int d = 0;
	for(;ee;ee=ee->next) {
		switch(ee->type) {
		case EE_WHILE:
		case EE_REPEAT:
		case EE_ENDLESS:
			d = max(d, 1 + EeDepth(ee->loop.body));
			break;
		case EE_IF:
			d = max(d, 1 + max(EeDepth(ee->cond.left), EeDepth(ee->cond.right)));
			break;
		}
	}
	return d;
}

bool CompareDepth(int dp, BasicBlock *bb)
{
	if (dp != 0) return dp > 0;

	Exp *e = GetIfExp(bb);
	if (e->type == E_BIN && e->bin.subtype == E_COMP_EQ)
		return true;
	return false;
}

EmittedEnt *Analyzer::EmitCode2(BasicBlock *bb, BasicBlock *stopper)
{
	EmittedEnt *fst;
	BasicBlock *cont;

	fst = NewEmitBas(bb);

	if (IsTwoWay(bb)) {
		EmittedEnt *r = NewEmitIf(GetIfExp(bb), bb);
		fst = NewEmitSeq(fst, r);

		if (MakeGotoFromIf(bb, bb->cond, bb->flow, stopper)) {
			r->cond.left = NewEmitGoto(bb->cond);
			cont = bb->flow;
		} else if (MakeGotoFromIf(bb, bb->flow, bb->cond, stopper)) {
			r->cond.negate = true;
			r->cond.left = NewEmitGoto(bb->flow);
			cont = bb->cond;
		} else if (bb->if_follow) {
			cont = bb->if_follow;

			if (stopper && stopper->order < cont->order && stopper->order > bb->order) {
				cont = stopper;
//				msg("%d: overriding cont from %d to %d\n", bb->order, bb->if_follow->order, stopper->order);
			}
			bb->if_follow = cont;

			EmittedEnt *flw = EmitCode(cont, stopper);

			BasicBlock *flow = bb->flow;
			BasicBlock *cond = bb->cond;

			// check if to swap the order of the if/else branches...
//			msg("%d: IF: flow=%d cond=%d ret=%d\n", bb->ord(), flow->ord(), cond->ord(), bb->if_follow->flow->ord());

			if (IsReturn(cont) && flow->order > cond->order && (flow == cont || cond == cont) )
				swap(flow,cond);

			if (flow != cont) {
				r->cond.negate = (flow == bb->flow);
				r->cond.left = EmitCode(flow, cont);
				if (cond != cont) {
					r->cond.right = EmitCode(cond, cont);

					if (CompareDepth(EeDepth(r->cond.left) - EeDepth(r->cond.right), bb)) {
						swap(r->cond.left, r->cond.right);
						r->cond.negate ^= true;
					}

					// can the if branch be optimized into a tail return?
					if (IsReturn(cont)) {
						r->cond.left = NewEmitSeq(r->cond.left, NewEmitBas(cont));
						fst = NewEmitSeq(fst, r->cond.right);
						r->cond.right = NULL;
					} else if (!EeReachesEnd(r->cond.left)) {
						fst = NewEmitSeq(fst, r->cond.right);
						r->cond.right = NULL;
					}
				}
			} else {
				r->cond.negate = (flow != bb->flow);
				r->cond.left = EmitCode(cond, cont);
			}

			return NewEmitSeq(fst, flw);
		} else {
//		msg("%d: Default if case\n", bb->ord());

			r->cond.negate = true;
			r->cond.left = EmitCode(bb->flow, stopper);
			if (EeReachesEnd(r->cond.left)) {
				r->cond.right = EmitCode(bb->cond, stopper);
				if (!EeReachesEnd(r->cond.right)) {
					fst = NewEmitSeq(fst, r->cond.left);
					r->cond.left = r->cond.right;
					r->cond.right = NULL;
					r->cond.negate = false;
				}
				cont = NULL;
			} else {
				cont = bb->cond;
			}
		}
	} else {
//		if(IsReturn(bb)) return NewEmitSeq(fst, NewEmitBas(bb));
		cont = bb->flow;
	}

	if (cont)
		fst = NewEmitSeq(fst, EmitCode(cont, stopper));

	return fst;
}

EmittedEnt *Analyzer::EmitCode(BasicBlock *bb, BasicBlock *stopper)
{
	assert(bb != NULL);

	if (bb == stopper) {
		return NULL;
	}

	if (bb->written) {
		return NewEmitGoto(bb);
	}
	bb->written = true;

	if (bb->loop_type) {
		if (bb->loop_type != LT_PRE_TESTED) {
			EmittedEnt *r = NewEmitLoop(bb);
			assert(bb->loop_follow != bb->loop_latch);

			EmittedEnt *flw = NULL;

			if (bb->loop_type == LT_POST_TESTED) {
				// if jumping to itself, the loop latch has already been written
				if (bb->loop_latch != bb) {
					if (bb->loop_latch->written) msg("Im %d, Loop latch %d already written\n",bb->ord(), bb->loop_latch->ord());
					bb->loop_latch->written = true;
					if (bb->loop_follow) flw = EmitCode(bb->loop_follow, stopper);
					r->loop.body = EmitCode2(bb, bb->loop_latch);
				} else {
					if (bb->loop_follow) flw = EmitCode(bb->loop_follow, stopper);
				}
				r->loop.body = NewEmitSeq(r->loop.body, NewEmitBas(bb->loop_latch)); // output the loop latch
				r->loop.exp = GetIfExp(bb->loop_latch);
				r->loop.negate = (bb->loop_latch->flow == bb);
			} else {
				if (bb->loop_follow) flw = EmitCode(bb->loop_follow, stopper);
				r->loop.body = EmitCode2(bb, bb);
			}

			// append follow, if any
			if (flw) r = NewEmitSeq(r, flw);

			return r;
		} else {
			EmittedEnt *r = NewEmitLoop(bb);

			assert(bb->loop_latch != bb);
			assert(bb->num_instr == 1);
			assert(bb->cond);
			assert(bb->cond == bb->loop_follow || bb->flow == bb->loop_follow);
			assert(bb->loop_follow != bb);

			// determine the branch of the IF that is NOT follow
			BasicBlock *bl = bb->cond != bb->loop_follow ? bb->cond : bb->flow;

			EmittedEnt *flw = EmitCode(bb->loop_follow, stopper);

			r->loop.body = EmitCode(bl, bb);

			r->loop.exp = GetIfExp(bb);
			r->loop.negate = (bb->cond == bb->loop_follow);

			return NewEmitSeq(NewEmitSeq(NewEmitBas(bb),r), flw);
		}
	}

	return EmitCode2(bb, stopper);
}


void Analyzer::Init()
{
	memset(this, 0, sizeof(*this));
	_exp_pool.Init();

	for(int i=0; i!=16; i++)
		_inittypes[i] = TI_UNK;
}

void Analyzer::Free()
{
	BasicBlock *bb;
	for(bb = _list; bb; ) {
		BasicBlock *next = bb->next;
		delete bb;
		bb = next;
	}
	_exp_pool.Free();
}

void Analyzer::RemoveFunctionPrologueCode(BasicBlock *first, BasicBlock *last)
{
	uint sp_mod = 0;
	uint pushed = 0;

	// delete the instructions that correspond to prologue code.
	{
		uint j;
		uint movtemp = 0;
		int n = -1;
		for(j=0; j!=first->num_instr; j++) {
			Exp *e = first->instr[j].e;

			if (e->type == E_OTHER && e->other.ins.mnem == O_PUSH) {
				// push
				pushed |= e->other.ins.op1.value &~movtemp;
				movtemp = 0;
				n = j;
			} else if (e->type == E_MOV && e->mov.e->type == O_REG && e->mov.e->reg >= 8 && e->mov.reg < 8) {
				// move large register
				pushed |= 1<<e->mov.e->reg;
				movtemp |= 1<<e->mov.reg;
			} else if (e->type == E_MOV && e->mov.e->type == E_BIN && e->mov.reg == R_SP && e->mov.e->bin.subtype == E_SUB &&
				e->mov.e->bin.left->type == E_REG && e->mov.e->bin.left->reg == R_SP &&
				e->mov.e->bin.right->type == E_CONST) {
				// sub sp,sp,XX
				sp_mod = e->mov.e->bin.right->num;
				n = j;
				break;
			} else
				break;
		}

		while (n>=0) { KillInstr(first, 0); n--; }
	}

	// delete the instructions that correspond to epilogue code
	uint n = last->num_instr;
	uint popped = 0;

	for(uint j=last->num_instr; (int)--j>=0;) {
		Exp *e = last->instr[j].e;

		if (e->type == E_OTHER) {
			if (e->other.ins.mnem == O_POP) {
				popped |= e->other.ins.op1.value;
				n = j;
			} else if (e->other.ins.mnem == O_BX && j == last->num_instr - 1) {
				if (e->other.ins.op1.reg == 1)
					_returns = true;
				n = j;
			} else
				break;
		} else if (e->type == E_MOV && e->mov.e->type == O_REG && e->mov.e->reg < 8 && e->mov.reg >= 8) {
		} else if (e->type == E_MOV && e->mov.e->type == E_BIN && e->mov.reg == R_SP && e->mov.e->bin.subtype == E_ADD &&
			e->mov.e->bin.left->type == E_REG && e->mov.e->bin.left->reg == R_SP &&
			e->mov.e->bin.right->type == E_CONST && e->mov.e->bin.right->num == sp_mod) {
			// sub sp,sp,XX
			n = j;
			break;
		} else
			break;
	}

	while (n != last->num_instr) KillInstr(last, n);
//	msg("Prologue: Saved 0x%X: Stack 0x%X\n", pushed, sp_mod);

	_framesize = sp_mod;
}

// remove a basic block and fixup the xrefs
void Analyzer::DeleteEmptyBB(BasicBlock *bd)
{
	BasicBlock *flow = bd->flow;
	assert(bd->flow && !bd->cond);
	assert(bd->num_instr == 0);
	assert(bd->flow != bd);
	int refs = flow->ref - 1;
	for(BasicBlock *bb = _list; bb; bb=bb->next) {
		if (bb->flow == bd) { bb->flow = flow; refs++; }
		if (bb->cond == bd) { bb->cond = flow; refs++; }
	}
	flow->ref = refs;
	DestroyBB(bd);
}

Pool _cached_type_pool(4000);
struct CachedTypeItem {
	TypeId str;
	TypeId result;
	uint32 offs;
	CachedTypeItem *next;
};

TailQueue(CachedTypeItem, next) _cached_type_list;
LList<tid_t> _struct_map;

void NewCachedType(TypeId str, uint32 offs, TypeId type)
{
	// initialize the list if it's empty
	if (_cached_type_list.empty())
		_cached_type_list.init();

	CachedTypeItem *cyi = (CachedTypeItem *)_cached_type_pool.Alloc(sizeof(CachedTypeItem));
	_cached_type_list.enqueue(cyi);
	cyi->offs = offs;
	cyi->result = type;
	cyi->str = str;

	assert(type);
}

TypeId CheckCachedType(TypeId str, uint32 offs)
{
	for(CachedTypeItem *cyi = _cached_type_list.first(); cyi; cyi = cyi->next) {
		if (cyi->str == str &&
				cyi->offs == offs) {
			return cyi->result;
		}
	}
	return 0;
}

TypeId GetTypeFromCmtString(const char *cmt, int indirect)
{
	while (*cmt == '*') { indirect++; cmt++; }
	while (*cmt == '&') { indirect--; cmt++; }

	if ((uint)indirect > 3) return TI_UNK;

	// for now, the type is simply a struct name.. simple.. but it doesn't work
	// if we rename structures.

	// scan until the end or the last :
	char *last = my_strchr(cmt, ':');
	char bak = *last;
	*(char*)last = 0;
	tid_t id = get_struc_id(cmt);
	*(char*)last = bak;

	if (id == BADADDR) return TI_UNK; // no struct with this name...

	// check if the structure type already exists, if not, add it.
	size_t t = _struct_map.LookupElement(id);
	if (t == (size_t) -1)
		t = _struct_map.Append(id);

	// and convert to TypeId and return
	return TI_STRUCT + t + (indirect * TI_INDIRECT);
}

tid_t GetTidForType(TypeId id)
{
	return _struct_map[id - TI_STRUCT];
}

size_t GetSizeOfStruct(TypeId id)
{
	return get_struc_size(get_struc(_struct_map[id - TI_STRUCT]));
}

inline static TypeId ParseCmtString(const char *s, int indirect)
{
//	if (s) msg("Parsing %s\n", s);
	return (s && s[0] == ':') ? GetTypeFromCmtString(s + 1, indirect) : TI_UNK;
}

static TypeId GetTypeOfAddress2(uint32 ea)
{
	char membercmt[1024];

	// check if the address has a comment...
	flags_t f = getFlags(ea);
	if (f == 0)
		return TI_UNK;

	addr_t head = ea;

	// check if it's a struct...
	if (isTail(f)) {
		head = get_item_head(ea);
		f = getFlags(head);
		if (!isData(f) || !isStruct(f)) return TI_UNK;
	} else {
		if (!isData(f)) return TI_UNK;
		if (!isStruct(f)) {
			char cmt[1024];
			// data item
			if (!has_cmt(f)) return TI_UNK;
			get_cmt(ea, false,cmt,sizeof(cmt));
			return ParseCmtString(cmt, 1);
		}
	}

	// reach here if it's a struct
	typeinfo_t ti;
	if (!get_typeinfo(head, 0, f, &ti)) return TI_UNK;

	// pointer to the struct?
	if (ea == head) {
		size_t t = _struct_map.LookupElement(ti.tid);
		if (t == (size_t) -1) t = _struct_map.Append(ti.tid);
		assert(t + TI_STRUCT);
		return t + TI_STRUCT;
	}

	struc_t *sptr = get_struc(ti.tid);
	if (!sptr) return TI_UNK;

	member_t *mptr = get_member(sptr, ea - head);
	if (!mptr || mptr->soff != ea - head) return TI_UNK;

	get_member_cmt(mptr->id, false,membercmt,sizeof(membercmt));
	return ParseCmtString(membercmt, 1);
}

TypeId GetTypeOfAddress(uint32 ea)
{
	// those are definately not an address, so they can't have a type
	if (ea < 0x01000000 || ea >= 0x0F000000)
		return TI_UNK;

	// check if the item is in the type cache..
	TypeId id = CheckCachedType(TI_NONE, ea);
	if (id) return id;

	id = GetTypeOfAddress2(ea);

	// insert cache item to speed up future lookups
	NewCachedType(TI_NONE, ea, id);
	return id;
}

TypeId GetTypeOfLoad(TypeId str, uint offs)
{
	// quick quit for types that's not a struct
	if (str < TI_STRUCT) return str == TI_NONE ? TI_NONE : TI_UNK;

	// indirect pointer to a struct..
	if (str & TI_INDIRECT_MASK) {
		if (offs != 0) return TI_UNK;
		return str - TI_INDIRECT;
	}

	// check if the item is in the type cache
	TypeId id = CheckCachedType(str, offs);
	if (id) return id;

	// translate the TypeId to an IDA structure, and check
	// if that structure has a member at offset offs.
	// Then check if that member is of a type.
	struc_t *st = get_struc(_struct_map[str - TI_STRUCT]);
	member_t *m = get_member(st, offs);

	id = TI_UNK;
	if (m != NULL && m->soff == offs) {
		char membercmt[1024];
		get_member_cmt(m->id, false, membercmt, sizeof(membercmt));
		id = ParseCmtString(membercmt, 0);
	}

	// insert cache item to speed up future lookups
	NewCachedType(str, offs, id);
	return id;
}

TypeId HandleAddToStruct(TypeId str, asize_t offs) {
	asize_t structsize = GetSizeOfStruct(str);
	if (offs % structsize == 0)
		return str;

	struc_t *st = get_struc(_struct_map[str - TI_STRUCT]);
	member_t *m = get_member(st, offs);

	TypeId id = TI_UNK;
	if (m != NULL && m->soff == offs) {
		char membercmt[1024];
		get_member_cmt(m->id, false, membercmt, sizeof(membercmt));
		id = ParseCmtString(membercmt, 1);
	}

	return id;
}


TypeId UnifyTypes(TypeId left, TypeId right)
{
	if (left == right) return left;
	if (left == TI_NONE) return right;
	if (right == TI_NONE) return left;
	if (left == TI_NULL) return right; // support null pointers..
	if (right== TI_NULL) return left;
	return TI_UNK;
}

static Exp *RemoveLsl(Exp *e, uint32 mul)
{
	AddMulStruct ams;
	IsAddMul(e->bin.left, ams);
	if (ams.add == 0 && ams.mul == mul) return e->bin.right;
	IsAddMul(e->bin.right, ams);
	if (ams.add == 0 && ams.mul == mul) return e->bin.left;
	return NULL;
}

TypeId GetTypeOf(Exp *e, TypeId regs[16])
{
	switch(e->type) {
	case E_CONST:
		if (e->num == 0) return TI_NULL;
		return GetTypeOfAddress(e->num);

	case E_REG:
		return regs[e->reg];

	case E_BIN: {
		if (e->bin.subtype == E_ADD) {
			// Check if it's XX*4 + Type
			Exp *et = RemoveLsl(e, 4);
			if (et) {
				TypeId x = GetTypeOf(et, regs);
				if (x == TI_NONE) return x;
				if (x != TI_UNK && (x & TI_INDIRECT_MASK)) {
					return x;
				}
			}

			// check if it's EXP + constant
			uint32 num;
			et = IsBinOpWithConstant(e, E_ADD, num);
			if (et) {
				TypeId x = GetTypeOf(et, regs);
				if (x == TI_NONE) return x;
				if (x >= TI_STRUCT && !(x & TI_INDIRECT_MASK)) {
					return HandleAddToStruct(x, num);
				} else if (x & TI_INDIRECT_MASK) {
					if (num == 4)
						return x;
				}
			}
		} else if (e->bin.subtype == E_SUB) {
			uint32 num;
			Exp *et = IsBinOpWithConstant(e, E_SUB, num);
			if (et && num == 4) {
				TypeId x = GetTypeOf(et, regs);
				if (x == TI_NONE) return x;
				if (x & TI_INDIRECT_MASK)
					return x;
			}
		}
		return TI_UNK;
	}

	case E_LOAD: {
		uint32 num;
		TypeId x;

		Exp *et = IsBinOpWithConstant(e->load.ea, E_ADD, num);
		if (!et) {
			et = e->load.ea;
			num = 0;
		}

		// check if it's <R0 + constant> or <R0>
		x = GetTypeOf(et, regs);
		if (x == TI_UNK) {
			if (e->load.subtype == T_I32) {
				x = GetTypeOf(e->load.ea, regs);
				if (x == TI_NONE) return TI_NONE;
				if (x & TI_INDIRECT_MASK)
					return x - TI_INDIRECT;
			}
			return TI_UNK;
		}

		return GetTypeOfLoad(x, num);
		}

	case E_CHOOSE: {
		TypeId left = GetTypeOf(e->choose.left, regs);
		if (left <= TI_UNK) return left;
		return UnifyTypes(left, GetTypeOf(e->choose.right, regs));
	}

	case E_CALL: {
		// support the RemapPtr call
		if (e->call.addr == 0x8009958 && e->call.arg[0]) {
			return GetTypeOf(e->call.arg[0], regs);
		}
		return TI_UNK;
	}
	}
	return TI_UNK;
}

void Analyzer::ComputeTypeState(BasicBlock *bb, TypeId tid[16])
{
	// the initial state is the entry state.
	memcpy(tid, bb->tid, sizeof(bb->tid));

	// for each mov instruction, update the type state.
	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];
		if (i.e->type == E_MOV) {
			tid[i.e->mov.reg] = i.e->mov.tid = GetTypeOf(i.e->mov.e, tid);
//			if (i.e->mov.tid >= 3)
//				msg("R%d = type 0x%x\n", i.e->mov.reg, i.e->mov.tid);
		}
	}
}

static bool MergeTypeState(TypeId dst[16], TypeId src[16]) {
	int changed = 0;
	for(int i=0; i!=16; i++) {
		int d = dst[i], s = src[i];
		if (d == TI_NONE || d == TI_NULL) {
			d = s;
		} else if ((s != TI_NULL && s != TI_NONE) && d != s) {
			d = TI_UNK;
		}
		changed |= dst[i] - d;
		dst[i] = d;
	}
	return !!changed;
}

void Analyzer::PropagateTypes()
{
	BasicBlock *bb;
	bool changed;
	int iterations = 0;
	TypeId tid[16];

	// initialize the type state of the first block to the start value
	memcpy(_list->tid, _inittypes, sizeof(_inittypes));

	// initialize all type states of all other blocks to zero (meaning NONE)
	for(bb=_list->next; bb; bb = bb->next) { memset(bb->tid, 0, sizeof(bb->tid)); }

	// fix point iteration until nothing changes
	do {
		changed = false;
		for(bb = _list; bb; bb = bb->next) {
			ComputeTypeState(bb, tid);
			if (bb->flow) changed |= MergeTypeState(bb->flow->tid, tid);
			if (bb->cond) changed |= MergeTypeState(bb->cond->tid, tid);
		}
		iterations++;
		if (iterations > 1000)
			break;
	} while (changed);

//	msg("Iterations %d\n", iterations);
}

void Analyzer::ParseAnteriorDirective(char *s)
{
	if (s[0] == 'R') {
		char *end;
		uint reg = strtoul(s+1, &end, 10);
		s = end;
		if (s[0] == '=' && reg < 8) {
			ea_t ea = get_name_ea(BADADDR, s + 1);
			if (ea == BADADDR) {
				return;
			}
			addr_t eat = ResolveMemContents(ea);
			if (eat != 0) ea = eat;
			MkInstr(_list->instr.Inject(0), NewMovExp(reg, NewConstExp(ea)));
		} else if (s[0] == ':' && reg < 16) {
			_inittypes[reg] = GetTypeFromCmtString(s + 1, 0);
			if (_inittypes[reg] == TI_UNK)
				printf("Type string '%s' is invalid\n", s + 1);
		}
	}
}

void Analyzer::CheckAnteriorLineDirectives()
{
	if (!hasExtra(getFlags(_list->base)))
		return;

	for(int i=0; i!=10; i++) {
		char s[1024];
		if (netnode(_list->base).supval(2000 + i,s,sizeof(s)) == -1) break;
		if (s[0] == ':') {
			ParseAnteriorDirective(s + 1);
		}
	}
}

void Analyzer::Run()
{
	msg("test1\n");
	BasicBlock *bb, *last = NULL;
	for(bb=_list;bb; bb=bb->next) last = bb;

	msg("test2\n");
	// remove function prologue/epilogue code
	RemoveFunctionPrologueCode(_list, last);

	msg("test3\n");
	_callconv = GetCallingConventionFor(_list->base);
	if (_callconv) {
		_returns = !!(_callconv & CC_RET);
	}

	msg("test4\n");
	// Check if there are any anterior line directives
	CheckAnteriorLineDirectives();

	msg("test5\n");
	InsertReturnStatements(_returns);

	msg("test6\n");
	for(BasicBlock *x=_list; x; x=x->next) ValidateRefs(_list,x);

	msg("test7\n");
	for(int i=0; i!=100; i++) {
		msg("\n\n---Loop %d\n", i);

		size_t siz = _exp_pool.GetSize();

		// determine statically assigned register values at the start of each basic block
		ComputeRegisterState();


		// compute uses field and propagate constants known at the start of a basic block
		for(bb = _list; bb; bb = bb->next) {
			ComputeUsesWrites(bb);
			PropagateInitialConsts(bb);
			ComputeUsesWrites(bb);
		}

		// fix point iteration to determine uses/writes across basblocks
		ComputeUsesWrites();

		// optimize each basic block
		for(bb = _list; bb;) {
			SimplifyBB(bb);

			BasicBlock *next = bb->next;
			if (bb->num_instr == 0 && bb->flow && bb->flow != bb) {
				// basic block can be deleted. it isn't needed anymore.
				DeleteEmptyBB(bb);
			}
			bb = next;
		}

		// continue until no more expressions are created..
		if (_exp_pool.GetSize() == siz && i > 3) {
			break;
		}
	}

	IdentifyLogicalAndOr();
	ComputeBBOrder();
	RestructureWhile();
	PropagateTypes();

	ComputeImmediateDominators();
	StructureLoops();
	for(BasicBlock *bb=_list; bb; bb=bb->next) {
//		printbb(bb);
	}

	StructureIfs();

	msg("Pool size %d\n",_exp_pool.GetSize());


#if 0
	for(BasicBlock *bb=_list; bb; bb=bb->next) {
		msg("%2d: ", bb->ord());
		if (bb->flow) msg("%2d ", bb->flow->ord()); else msg("   ");
		if (bb->cond) msg("%2d ", bb->cond->ord()); else msg("   ");
		msg(" : if=%d dom=%d lh=%d\n", bb->if_follow->ord(), bb->immed_dom->ord(), bb->loop_head->ord());
	}
#endif
}


EmittedEnt *Analyzer::GenerateCode()
{
	EmittedEnt *r = EmitCode(_list, NULL);

	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (!bb->written && !IsReturn(bb))
			r = NewEmitSeq(r, EmitCode(bb, NULL));
	}
	return r;
}


