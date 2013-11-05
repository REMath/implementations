
#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <netnode.hpp>
#include <struct.hpp>
#include <xref.hpp>
#include <auto.hpp>
#include <typeinf.hpp>
#include <offset.hpp>
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <windows.h>
#include <ida.hpp>
#include <idp.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include "default.h"
#include "insn.h"
#include "exp.h"



LList<byte *> lines;
static char linebuf[512];
static int linepos;
static uint pendlabel;

// stuff in linebuf is escaped.
// Escape codes:
//   1 <BYTE>   - Register Number
//   2 <UINT16> <UINT32> - Integer formatted in some special way. also used for addresses and refs.
//   3 <UINT16> <BYTE> - label name. the index is the index of the label. the byte is reserved.
//   4 <REG:4> <TYPE:4> <UINT16>  - Register displacement memory access
//   5 <TYPE:4> <TID:32> <OFFS:32> - Struct offset memory load. On the form dword<R1 + StructName.member + 1>. starts a nesting group
//   6 - End of nesting.


// format of integer formatting word.
//  &0x78 = 0x00 - normal number which is not an address
//  &0x78 = 0x08 - dereferenced address, store
//  &0x78 = 0x10 - dereferenced address, load
//  &0x78 = 0x18 - address, but don't add a reference
//  &0x78 = 0x20 - subroutine call
//  &7           - access data type

enum {
	TF_MASK = 0x78,
	TF_CALL = 0x20,
	TF_NUM = 0x00,
	TF_DEREF_STORE = 0x08,
	TF_DEREF_LOAD  = 0x10,

	TF_ADDRESS_NOREF = 0x18,
};

struct OutHdr {
	byte version;
	byte flags;
	uint16 len;
	ea_t ea; // real address of this instruction, when flags&2 this is instead num remaining bytes
	uint16 label;
	int get_indent() { return flags >> 4; }
	bool is_empty_line_after() { return !!(flags & 4); }
};

// output a single bute
static void outbyte(byte b)
{
	if (linepos != sizeof(linebuf))
		linebuf[linepos++] = b;
}

static void outundo()
{
	linepos--;
}

// output a formatted string
static void out(const char *s, ...)
{
	va_list va;
	va_start(va,s);
	int r = _vsnprintf(linebuf + linepos, sizeof(linebuf) - linepos, s, va);
	if (r != -1)
		linepos += r;
	else
		linepos = sizeof(linebuf);
	va_end(va);
}

static void outbytes(const void *b, size_t len)
{
	if (linepos + len > sizeof(linebuf)) return;
	memcpy(linebuf + linepos, b, len);
	linepos += len;
}

static void outstr(const char *s)
{
	outbytes(s, strlen(s));
}

// flush the line
static void outnewline(int indent = 0)
{
	if (linepos) {
		((OutHdr*)linebuf)->len = linepos;
		lines.Append((byte*)memdup(linebuf, linepos));
	}
	
	((OutHdr*)linebuf)->version = 0x11;	
	((OutHdr*)linebuf)->flags = (indent > 15 ? 15 : indent)<<4; // max indent is 15
	((OutHdr*)linebuf)->label = pendlabel; pendlabel = 0;
	((OutHdr*)linebuf)->ea = 0;

	linepos = sizeof(OutHdr);
}	

static void outspacedline()
{
	((OutHdr*)linebuf)->flags |= 4;
}

static void undospacedline()
{
	((OutHdr*)linebuf)->flags &= ~4;
}

static void outorigea(ea_t ea)
{
	((OutHdr*)linebuf)->ea = ea;
}

static void outlabeldef(uint label)
{
	pendlabel = label;
}

static void outnum(uint32 num, uint16 format)
{
	outbyte(2);
	outbyte(format & 0xff);
	outbyte(format>>8);
	outbyte(byte(num));
	outbyte(byte(num>>8));
	outbyte(byte(num>>16));
	outbyte(byte(num>>24));
}

static void outreg(uint r)
{
	outbyte(1);
	outbyte(r);
}

static void outdispl(uint r, uint t, uint32 num)
{
	outbyte(4);
	outbyte((r << 4) | (t & 0xF));
	outbyte(byte(num));
	outbyte(byte(num>>8));
}

static void outstruct(tid_t tid, uint32 offs, uint t)
{
	outbyte(5);
	outbyte(t);
	outbyte(byte(tid));
	outbyte(byte(tid>>8));
	outbyte(byte(tid>>16));
	outbyte(byte(tid>>24));
	outbyte(byte(offs));
	outbyte(byte(offs>>8));
	outbyte(byte(offs>>16));
	outbyte(byte(offs>>24));
}

static void outnestend()
{
	outbyte(6);
}

static const char * const _opnames[] = {
	"",
	"&", "^", "<<", ">>", ">>s", ">><", "|", "*", "&~", "+", "-", 
	
	"||","&&",


	"==", // EQ
	"!=", // NE
	">=u", // CS
	"<u",  // CC
	"?mi?",  // 
	"?pl?",
	"?vs?",
	"?vc?",
	">u",		// HI
	"<=u",	// LS
	">=",		// GE
	"<",		// LT
	">",		// GT
	"<=",		// LE

	// unary operators
	"~", "-", "!",
	"EXTB(","EXTW(",
	"EXTSB(","EXTSW(",
};

static const char * const _typenames[] = {
	"char<",
	"byte<",
	"short<",
	"word<",
	"dword<",
};

static const byte _typesize[] = {
	1,1,2,2,4,
};

static bool LooksLikeArrayBase(uint32 addr)
{
	return addr >= 0x1000000 && isEnabled(addr);
}

struct TidBk {
	TypeId r[16];
};
static TidBk cur_tid;

static void outexp(Exp *e, uint flags);

#define CPUFASTSET_ADDR 0x0809DFBC
static bool HandleSpecialCall(Exp *e)
{
	if ((e->call.addr == CPUFASTSET_ADDR || e->call.addr == 0x0809DFC0) && 
		e->call.arg[0] && e->call.arg[1] && e->call.arg[2] && !e->call.arg[3] && e->call.arg[2]->type == E_CONST) {
		// CPUFastSet or CPUSet
		uint32 num = e->call.arg[2]->num;
		uint size = num & 0x3ffff;

		if (e->call.addr == CPUFASTSET_ADDR)
			size *= 4;
		else if (num & (1 << 26))
			size *= 4;
		else
			size *= 2;
			
		if ((num >> 24) & 1) {
			outstr("bios_set(");
		} else {
			outstr("bios_copy(");
		}
		
		outexp(e->call.arg[1],0);
		outstr(", ");		
		outexp(e->call.arg[0],0);
		outstr(", ");
		outnum(size, 0);
		outstr(")");
		return true;
	}

	return false;
}

static Exp *RemoveLsl4(Exp *e, Exp *&mul)
{
	if (e->type == E_BIN && e->bin.subtype == E_ADD) {
		AddMulStruct ams;
		Exp *l = IsAddMul(e->bin.left, ams);
		if (ams.add == 0 && ams.mul == 4) { mul = l; return e->bin.right; }
		l = IsAddMul(e->bin.right, ams);
		if (ams.add == 0 && ams.mul == 4) { mul = l; return e->bin.left; }
	}
	return e;
}

enum {
	PF_TYPEMASK = 7, // optional type when using PF_EA
	PF_EA = 8,
	PF_NEGCONST = 16,
	PF_NEGATE = 32,
	PF_EA_STORE = 64,
};
#define PF_TYPE(x) ((x)+1)


static void outea(Exp *eax, int type, bool store)
{
	if (type == T_I32) {
		Exp *eamul = NULL;
		Exp *eal = RemoveLsl4(eax, eamul);

		if (eal->type == E_LOAD) {
			TypeId id = GetTypeOf(eal, cur_tid.r);
			if (id & TI_INDIRECT_MASK) {
				outexp(eal, 0);
				outbyte('[');
				if (eamul == NULL)
					outnum(0,0);
				else
					outexp(eamul, 0);
				outbyte(']');
				return;
			}
		}
	}

	AddMulStruct ams;
	Exp *ea = IsAddMul(eax, ams);
	if (ams.mul == 1) {
		TypeId id = GetTypeOf(ea, cur_tid.r);
//		out("{tid=%x}", id);
		if (id >= TI_STRUCT && !(id & TI_INDIRECT_MASK)) {
			outstruct(GetTidForType(id), ams.add, (type + 1) | (store ? 0x8 : 0));
			outexp(ea, 0);
			outnestend();
			return;
		}
	}
		
	if (ams.add!=0 && ams.mul % _typesize[type] == 0 && LooksLikeArrayBase(ams.add)  ) {
		ams.mul /= _typesize[type];
		outnum(ams.add, (store ? TF_DEREF_STORE : TF_DEREF_LOAD) | PF_TYPE(type));
		outbyte('[');
		if (ams.mul != 1) out("(");
		outexp(ea, 0);
		if (ams.mul != 1) { out(") * "); outnum(ams.mul,0); }
		outbyte(']');
	} else if (ea->type == E_REG && ams.mul == 1 && ((long)ams.add >= -32768 && (long)ams.add <= 32767)) {
		outdispl(ea->reg, (type + 1) | (store ? 0x8 : 0), ams.add);
	} else {
		outexp(eax, PF_EA | (store ? PF_EA_STORE : 0) | PF_TYPE(type));
	}
}


static void outexp(Exp *e, uint flags)
{
	bool need_type = false;
	static char charbuf[80];

	if (flags & PF_NEGATE) { outbyte('!'); }

	if (flags & PF_EA && flags & PF_TYPEMASK && e->type != E_CONST) {
		outstr(_typenames[(flags & PF_TYPEMASK) - 1]);
		flags &= ~PF_TYPEMASK;
		need_type = true;
	}

	switch(e->type) {
	case E_CONST: {
		uint f = flags & PF_TYPEMASK;
		if (flags & PF_EA) {
			if (flags & PF_EA_STORE) {
				f |= TF_DEREF_STORE;
			} else {
				f |= TF_DEREF_LOAD;
			}
		}
		outnum(e->num, f); // TODO: XXX
		break;
	}
	case E_REG: 
		outreg(e->reg);
		break;
	case E_MOV:
		outreg(e->reg);
//		out("{tid=%x}", e->mov.tid);
		outstr(" = ");
		outexp(e->mov.e, flags &~ PF_NEGATE);
		break;
	case E_BIN: {
		int st = e->bin.subtype;

		if (st == E_ADD && e->bin.right->type == E_CONST) {
			uint32 num = e->bin.right->num;
			// add with constant. check if the item to the left is a structure..
			TypeId x = GetTypeOf(e->bin.left, cur_tid.r);
			if (x >= TI_STRUCT && !(x & TI_INDIRECT_MASK) && num < GetSizeOfStruct(x)) {
				// taking address of struct item
				outstruct(GetTidForType(x), num, 0);
				outexp(e->bin.left, 0);
				outnestend();
				break;
			}
		}

		// handle negation...
		if ((flags & PF_NEGATE) && st >= E_COMP_EQ && st <= E_COMP_LE) {
			outundo();
			st = ((st - E_COMP_EQ) ^ 1) + E_COMP_EQ;
			flags ^= PF_NEGATE;
		} else if ((flags & PF_NEGATE) && (st == E_LAND || st == E_LOR)) {
			outundo();
			st ^= E_LAND ^ E_LOR;
		} else if (flags & PF_NEGATE) {
			flags |= 0x7f000000;
			flags ^= PF_NEGATE;
		}
		
		// need () ?
		uint prec = _expression_prec[st];
		bool paren = false;
		if ((prec&0x3F) < (flags >> 24)) { paren = true; outbyte('('); }

		outexp(e->bin.left, (flags & PF_NEGATE) | (((prec & 0x3F) + (prec>>7))<<24));
		outbyte(' ');
		outstr(_opnames[st]);
		outbyte(' ');
		outexp(e->bin.right, (flags & PF_NEGATE) | (((prec & 0x3F) + (prec>>6&1))<<24) );
		
		if (paren) { outbyte(')'); }
		break;
	}
	case E_UN:
		if (e->un.subtype == E_LNOT) {
			if (flags & PF_NEGATE) outundo();
			flags ^= PF_NEGATE;
			outexp(e->un.left, (flags & PF_NEGATE));
		} else {
			outstr(_opnames[e->un.subtype]);
			outexp(e->un.left, _expression_prec[e->un.subtype]<<24);
			if (e->un.subtype >= E_FROM_U8 && e->un.subtype <= E_FROM_I16)
				outbyte(')');
		}
		break;
	case E_STOR: {
		outea(e->store.ea, e->store.subtype, true);
		outbyte(' ');
		if (e->store.oper) {
			outstr(_opnames[e->store.oper]);
		}
		outstr("= ");
		outexp(e->store.value, (e->store.oper == E_AND ? PF_NEGCONST | PF_TYPE(e->store.subtype) : 0));
		outbyte(';');
		break;
	}
	case E_LOAD: {
		outea(e->load.ea, e->load.subtype, false);
		break;
	}
	case E_CALL: {
		if (!HandleSpecialCall(e)) {
			outnum(e->call.addr, TF_CALL);
			outbyte('(');
			
			int num = 4;
			while (num && !e->call.arg[num-1]) num--;

			for(int i=0; i!=num; i++) {
				if (i != 0) { outstr(", "); }
				if (e->call.arg[i])
					outexp(e->call.arg[i], 0);
				else {
					outbyte('?');
					outbyte('?');
				}
			}
			outbyte(')');
		}
		break;
	}
	case E_OTHER: {
		outstr("__asm  ");
		PrintThumb(e->other.ins, charbuf);
		outstr(charbuf);
		break;
	}
	case E_CHOOSE: {
		outbyte('(');
		outexp(e->choose.e, 0);
		outstr(" ? ");
		outexp(e->choose.left, 0);
		outstr(" : ");
		outexp(e->choose.right, 0);
		outbyte(')');
		break;
	case E_RETURN:
		outstr("return ");
		if (e->ret.e)
			outexp(e->ret.e, 0);
		else
			outstr("void");
		break;		
	}
	default:
		assert(0);
	}

	if (need_type) {
		outbyte('>');
	}
}

static void outbb(BasicBlock *bb, int indent)
{
	memcpy(cur_tid.r, bb->tid, sizeof(cur_tid.r));

	for(size_t j=0; j!=bb->num_instr; j++) {
		Instr &i = bb->instr[j];
		if (i.e->type != E_COND) {
			outnewline(indent);
			outorigea(i.addr);
			outexp(i.e, 0);
		}
		if (i.e->type == E_MOV) {
			cur_tid.r[i.e->mov.reg] = i.e->mov.tid;
		}
	}
}

static EmittedEnt *SkipEmptyEE(EmittedEnt *ee)
{
	while (ee->type == EE_BAS && !ee->bas.bas->need_label && (ee->bas.bas->num_instr == 0 || (ee->bas.bas->num_instr == 1 && ee->bas.bas->cond)) && ee->next)
		ee = ee->next;
	return ee;
}


void outrs(const RegState &rs)
{
	int i;
	uint regs = rs.changed;
	for(i=0; regs; regs>>=1, i++) {
		if (regs & 1) {
			if (rs.known & (1 << i)) {
				out(": %s=0x%X ", _regs[i], rs.values[i]);
			} else {
//				out(": %s=? ", _regs[i]);
			}
		}
	}
}

void outtid(const TypeId tid[16])
{
	for(int i=0; i!=16; i++) {
		if (tid[i] >= 2) 
			out(": %s=0x%X ", _regs[i], tid[i]);
	}
}


void outlbl(BasicBlock *bas)
{
	outbyte(3);
	outbyte(bas->order & 0xff);
	outbyte(bas->order >> 8);
	outbyte(0);
}

static bool QualifiesForSingleLineIf(EmittedEnt *e)
{
	if (e->type == EE_GOTO || e->type == EE_RETURN)
		return true;
	if (e->type == EE_BAS && IsReturn(e->bas.bas) && e->next == NULL)
		return true;
	if (e->type == EE_BAS && e->bas.bas->num_instr == 1 && e->next == NULL)
		return true;

	return false;
}



static void PrintEmittedEnt(EmittedEnt *e, int indent, BasicBlock *enclosing_for, int flags = 0)
{
	for(;e;e=e->next) {
		switch(e->type) {
		case EE_BAS: {
			BasicBlock *bb = e->bas.bas;

#if 0
			outnewline(indent);
			out("/* %d: 0x%X: %d %d : if=%d dom=%d lh=%d", bb->order, bb->base, bb->flow->ord(), bb->cond->ord(), bb->if_follow->ord(), bb->immed_dom->ord(), bb->loop_head->ord());

			if (bb->loop_type) {
				static const char * const _loopnames[] = {
					"for loop","while loop", "repeat loop",
				};
				out(": %s latch=%d follow=%d", _loopnames[bb->loop_type-1], bb->loop_latch->ord(), bb->loop_follow->ord());
			}

			//outrs(bb->rs);
			outtid(bb->tid);
			out("*/");
#endif
			if (bb->need_label) {
				outlabeldef(bb->order);
			}
			outbb(bb , indent);
			break;
		}

		case EE_GOTO:
			outnewline(indent);
			
			if (enclosing_for) {
				if (enclosing_for->loop_type == LT_PRE_TESTED) {
					if (enclosing_for->num_instr == 1 && e->bas.bas == enclosing_for) {
						out("continue // ");
						outlbl(e->bas.bas);
						break;
					}
				} else if (enclosing_for->loop_type == LT_ENDLESS) {
					if (e->bas.bas == enclosing_for) {
						out("continue //");
						outlbl(e->bas.bas);
						break;
					}
				}

				if (enclosing_for->loop_follow == e->bas.bas) {
					out("break //");
					outlbl(e->bas.bas);
					break;
				}
			}

//			if (enclosing_for && enclosing_for->loop_latch == e->bas.bas)
//				out("continue");
			

			out("goto ");
			outlbl(e->bas.bas);
			break;

		case EE_IF: {
			if (!(flags&1))
				outnewline(indent);
			flags &= ~1;

			bool skip_bracket = (e->cond.left && !e->cond.right && QualifiesForSingleLineIf(e->cond.left));
						
			out("if (");
			outexp(e->cond.exp, e->cond.negate ? PF_NEGATE : 0);
			out(skip_bracket ? ")" : ") {");
			if (e->cond.left) PrintEmittedEnt(e->cond.left, indent + 1, enclosing_for);
			if (!skip_bracket) {
				undospacedline();
				outnewline(indent);
				out("}");
			}
			if (e->cond.right) {
				EmittedEnt *er = SkipEmptyEE(e->cond.right);
				if (er->type == EE_IF && er->cond.bas->if_follow == e->cond.bas->if_follow && er->next == NULL) {
					out(" else ");
					PrintEmittedEnt(er, indent, enclosing_for, 1);
				} else {
					out(" else {");
					PrintEmittedEnt(er, indent + 1, enclosing_for);
					undospacedline();
					outnewline(indent);
					out("}");
					outspacedline();
				}
			} else {
				outspacedline();
			}
			break;
		}
			
		case EE_ENDLESS:
			outnewline(indent);
			out("for(;;) {");
			PrintEmittedEnt(e->loop.body, indent + 1, e->loop.bas);
			undospacedline();
			outnewline(indent);
			out("} /* for */");
			outspacedline();
			break;

		case EE_REPEAT:
			outnewline(indent);
			out("do {");
			PrintEmittedEnt(e->loop.body, indent + 1, e->loop.bas);
			undospacedline();
			outnewline(indent);
			out("} while (");
			outexp(e->loop.exp, e->loop.negate ? PF_NEGATE : 0);
			out(")");
			outspacedline();
			break;

		case EE_WHILE:
			outnewline(indent);
			out("while (");
			outexp(e->loop.exp, e->loop.negate ? PF_NEGATE : 0);
			out(") {");
			PrintEmittedEnt(e->loop.body, indent + 1, e->loop.bas);
			undospacedline();
			outnewline(indent);
			out("} /* while */");
			outspacedline();
			break;

		case EE_RETURN:
			outnewline(indent);
			out("return ");
			if (e->ret.e)
				outexp(e->ret.e, 0);
			else
				out("void");
			break;

		default:
			assert(0);
		}
	}
}

byte Analyzer::CheckRegFuncPar(int r)
{
	BasicBlock *bb = _list;
	// someone jumps to the bb?
	if (bb->ref != 0) return r;

	int found = -1;
	uint found_reg = 0;

	// search the first instructions to see if we find a move from this register
	for(uint i=0; ; i++) {
		if (i == bb->num_instr) {
			if (HASBIT(bb->liveout, r))
				return r;
			break;
		}
		Instr &j = bb->instr[i];

		if (HASBIT(j.uses, r)) {
			// check if it's one of
			// MOV r2,r
			// MOV r2,r & 0xff
			// mov r2,r & 0xffff

			if (found != -1 || j.e->type != E_MOV) return r;
			Exp *e = j.e->mov.e;

			if (e->type == E_REG) {
				// direct reg
				found_reg = 0;
			} else if (e->type == E_BIN && 
								e->bin.subtype == E_AND && 
								e->bin.left->type == E_REG && 
								e->bin.right->type == E_CONST && ((found_reg = T_U8<<4, e->bin.right->num == 0xff) || (found_reg = T_U16<<4, e->bin.right->num == 0xffff))) {
				// and..
			} else {
				return r;
			}
			found = i;
			found_reg += j.e->mov.reg;
		}

		if (HASBIT(j.changes, r))
			break;
	}

	if (found == -1) return r;

	// if we get here, then there's exactly one write to the reg.. so delete the instr,
	// and return the mod reg..	
	KillInstr(bb, found);

	return found_reg;
}

int Analyzer::DetermineFunctionArgs(byte *p)
{
	int n = 0;
	for(int i=0; i!=16; i++) {
		if (HASBIT(_callconv, i)) {
			p[n++] = CheckRegFuncPar(i);
		}
	}
	return n;
}

void Analyzer::Dump2()
{
//	PrintConstant(buf, _list->base, PF_EA);

	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (bb->next == NULL && bb->num_instr == 0)
			bb->written = true;
	}
	
	outnewline();
	
	if (_returns)
		outstr("int ");
	else
		outstr("void ");
	
//	outstr("function ");
	outnum(_function_base, TF_ADDRESS_NOREF);
	outstr("(");

	byte args[16];
	int n = DetermineFunctionArgs(args);

	for(int i=0; i!=n; i++) {
		if (i != 0) out(", ");
		switch(args[i] >> 4) {
		case T_U8: outstr("byte "); break;
		case T_U16: outstr("word "); break;
		default: outstr("int "); break;
		}
		outreg(args[i] & 0xF);
	}
	
	outstr(") {");

	if (_framesize) {
		outstr(" // framesize ");
		outnum(_framesize, 0);
	}
	
	EmittedEnt *r = GenerateCode();

	PrintEmittedEnt(r, 1, NULL);
	outnewline(0);
	outstr("}");
	outnewline(0);

}




void Analyzer::Dump()
{
	BasicBlock *bb;
	BasicBlock *flow = NULL;

	msg("\n\n");

	// first see if it exists already?
	for(bb = _list; bb; bb = bb->next) {
		int ref = bb->ref;

		if (flow != NULL) {
			if (bb != flow) {
				if (flow->flow == NULL)
					msg("\n    return");
				else	
					msg("\n    goto L_%d", flow->order);
			} else {
				ref--;
			}
		}


//		msg("\n// %2d:%2d,%2d, refs:%d", bb->order, bb->interval->order,
//			bb->loop_head ? bb->loop_head->order : 0, bb->ref - bb->back_ref);

//		msg("\n// immediate dominiator %d", bb->immed_dom ? bb->immed_dom->order : 0);

		if (bb->if_follow) {
			msg("\n// if follow %d", bb->if_follow->order);
		}

		if (bb->loop_type) {
			static const char * const _ln[] = { "endless loop", "while loop", "repeat loop" };
			msg("\n// %s starts here. follow = %d, latch = %d", _ln[bb->loop_type - 1], bb->loop_follow ? bb->loop_follow->order : 0, bb->loop_latch->order);
		}

#if 0
		msg("\n%2d,%2d: BAS %X-%X: ", bb->order, bb->interval->order, bb->base, bb->end);
		if (bb->flow) msg("%X ", bb->flow->base);
		if (bb->cond) msg("%X ", bb->cond->base);

		msg(": ");
		DumpRegs(bb->uses);
		msg(": ");
		DumpRegs(bb->writes);
		msg(": ");
		DumpRegs(bb->liveout);

		msg("\nREG ");
		DumpRS(bb->rs);

#endif


#if 0
		if (ref != 0)
			msg("L_%d: /* %d */\n", bb->order, bb->interval->order);
		else
			msg("/* %2d,%2d */\n", bb->order, bb->interval->order);
#else
		if (ref != 0)
			msg("\nL_%d:", bb->order);

#endif

		outbb(bb, 1);

		if (bb->cond) {
			msg("\n    if(");
			outexp(GetIfExp(bb), 0);
			msg(") goto L_%d", bb->cond->order);

		}

		flow = bb->flow;
	}
}

void printnum(uint32 num, uint16 fmt)
{
	msg("0x%X", num);	

}

const byte *scantoken(const byte *s, const byte *e)
{
	while (s<e && *s > 10) s++;
	return s;
}


void printlines()
{
	for(size_t i=0; i!=lines.GetCount(); i++) {
		const byte *s = lines[i];
		const byte *e = s + ((OutHdr*)s)->len;

		if (((OutHdr*)s)->get_indent()) {
			msg("%*c", ((OutHdr*)s)->get_indent() * 4, ' ');
		}

		s += sizeof(OutHdr);

		assert(s <= e);

		for(;;) {
			const byte *t = s;
			s = scantoken(s,e);

			if (t != s) {
				msg("%.*s", s - t, t);
			}

			assert(s<=e);
			if (s == e)
				break;

			switch(*s++) {
			case 1: // register
				msg("%s", _regs[*s++]);
				break;
			case 2: // integer
				printnum(*(uint32*)(s+2), *(uint16*)s);
				s += 6;
				break;
			case 3: // label
				s += 3;
				break;
			default:
				assert(0);
			}
		}
		msg("\n");
	}
}

void printexp(Exp *e)
{
	bool need_type = false;
	static char charbuf[80];
	switch(e->type) {
	case E_CONST: {
		msg("0x%x", e->num);
		break;
	}
	case E_REG:
		msg(_regs[e->reg]);
		break;
	case E_MOV:
		msg(_regs[e->reg]);
		msg(" = ");
		printexp(e->mov.e);
		break;
	case E_BIN: {
		int st = e->bin.subtype;
		printexp(e->bin.left);
		msg(" %s ", _opnames[st]);
		printexp(e->bin.right);
		break;
	}
	case E_UN:
		msg("%s",_opnames[e->un.subtype]);
		printexp(e->un.left);
		break;
	case E_STOR: {
		msg(_typenames[e->store.subtype]);
		printexp(e->store.ea);
		msg("> %s= ", _opnames[e->store.oper]);
		printexp(e->store.value);
		break;
	}
	case E_LOAD: {
		msg(_typenames[e->load.subtype]);
		printexp(e->load.ea);
		msg(">");
		break;
	}
	case E_CALL: {
		msg("%X(", e->call.addr);
		int num = 4;
		while (num && !e->call.arg[num-1]) num--;

		for(int i=0; i!=num; i++) {
			if (i != 0) { msg(", "); }
			if (e->call.arg[i])
				printexp(e->call.arg[i]);
			else {
				msg("??");
			}
		}
		msg(")");
		break;
	}
	case E_OTHER: {
		PrintThumb(e->other.ins, charbuf);
		msg("__asm  %s", charbuf);
		break;
	}
	case E_COND:
		msg("if (");
		printexp(e->cond.e);
		msg(") goto");
		break;

	case E_RETURN:
		msg("return ");
		if (e->ret.e)
			printexp(e->ret.e);
		else
			msg("void");
		break;
				
	default:
		msg("??XXX??");
//		assert(0);
	}
}


void printregs(uint32 r)
{
	for(int i=0; i!=16; i++) {
		if (r & (1 << i))
			msg("R%d ", i);
	}
}

void printrs(const RegState &rs)
{
	int i;
	uint regs = rs.changed;
	for(i=0; regs; regs>>=1, i++) {
		if (regs & 1) {
			if (rs.known & (1 << i)) {
				msg(": %s=0x%X ", _regs[i], rs.values[i]);
			} else {
//				out(": %s=? ", _regs[i]);
			}
		}
	}
}


void printbb(BasicBlock *bb)
{
	msg("\n// %d: 0x%X: %d %d : %d : if=%d ", bb->order, bb->base, bb->flow->ord(), bb->cond->ord(), bb->ref, bb->if_follow->ord());

	if (bb->loop_type) {
		static const char * const _loopnames[] = {
			"for loop","while loop", "repeat loop",
		};
		msg(": %s latch=%d follow=%d", _loopnames[bb->loop_type-1], bb->loop_latch->ord(), bb->loop_follow->ord());
	}

//	printrs(bb->rs);

	msg("\n");
#if 0

	msg("// ");
	printregs(bb->uses);
	msg(": ");
	printregs(bb->writes);
	msg(": ");
	printregs(bb->liveout);
	msg("\n");
#endif
	for(uint i=0; i<bb->num_instr; i++) {
		printexp(bb->instr[i].e);
		msg("\n");
	}

}


OutHdr dummy_supval = {
	0x11,
	0,
	sizeof(OutHdr),
	0,
	0,
};

#define PSEUDO_NETNODE_SUPVAL 0x997

static bool IsConstantPoolItem(ea_t addr)
{
	flags_t f = getFlags(addr);
	
	if (has_name(f))
		return false;

	if (isData(f)) {
		
		// only dword items in direct data segment
		if (get_item_size(addr) != 4)
			return false;
	} else if (isUnknown(f)) {
		if (get_byte(addr) != 0)
			return false;
	} else
		return false;

	return true;
}

bool _need_refresh;

void importtodb(ea_t addr, ea_t addr_end)
{
	size_t i;
	ea_t add = addr;

	// check if to extend the addr_end so it includes the constant area right after the function
	for(;;) {
		if (!IsConstantPoolItem(addr_end))
			break;
		
		addr_end = get_item_end(addr_end);
	}

	ea_t first_bad = BADADDR;

	for(i=0; i!=lines.GetCount() && add < addr_end; i++) {
		byte *s = lines[i];
		size_t len = ((OutHdr*)s)->len;
		uint itemsize = 1;
		
		byte flags = 0;
		if (i == 0) {
			((OutHdr*)s)->flags |= 1;
			itemsize = 2;
		}
		if (i == lines.GetCount() - 1) {
			((OutHdr*)s)->flags |= 2;
			((OutHdr*)s)->ea = addr_end - add;
			itemsize = addr_end - add;
		}

		// remember the first instruction with a not matching itemsize
		if (first_bad == BADADDR && get_item_size(add) != itemsize) first_bad = add;
			
//		if (add >= 0x8001800)
//			msg("Setting %x %d %d\n", add, len, get_item_size(add));
		netnode(add++).supset(PSEUDO_NETNODE_SUPVAL, s, len);

		if (i == 0 && lines.GetCount() != 1) {
			netnode(add++).supset(PSEUDO_NETNODE_SUPVAL, &dummy_supval, sizeof(dummy_supval));
		}
	}

	while(add < addr_end)
		netnode(add++).supdel(PSEUDO_NETNODE_SUPVAL);

//	if (first_bad == BADADDR) {
		_need_refresh = true;
	//} else if (first_bad == addr) {
		// need to remake the whole function
		do_unknown_range(addr, addr_end - addr, 0);
		analyze_area(addr, addr_end);
		add_func(addr, addr_end);
		_need_refresh = true;
	//} else {
		// just the part from first_bad to addr_end needs to be reanalyzed
	//	do_unknown_range(first_bad, addr_end - first_bad, false);
	//	analyze_area(first_bad, addr_end);
//	//		ua_code(first_bad);
	//	_need_refresh = true;
	//}
}

void free_lines()
{
	for(size_t i=0; i!=lines.GetCount(); i++)
		free(lines[i]);
	lines.Free();
}

void rundec(ea_t ea = get_screen_ea())
{
	
	Analyzer ana;
	/*hwnd = NULL;
			if(0==form){  
			form = create_tform("Decompiled view", &hwnd);
			msg("form: %x\n", form);
			  if ( hwnd == NULL )
			  {
				warning("Could not create custom view window\n"
						"perhaps it is open?\n"
						"Switching to it.");
				form = find_tform("Decompiled view");
				if ( form != NULL )
				  switchto_tform(form, true);
				return;
			  }
				// allocate block to hold info about our sample view
		  sample_info_t *si = new sample_info_t;
		  si->form = form;
		  // prepare the data to display. we could prepare it on the fly too.
		  // but for that we have to use our own custom place_t class decendant.
		  for ( int i=0; i < qnumber(sample_text); i++ )
		  {
			si->sv.push_back(simpleline_t("")); // add empty line
			si->sv.push_back(simpleline_t(sample_text[i].text));
			si->sv.back().bgcolor = sample_text[i].color;
		  }
		  // create two place_t objects: for the minimal and maximal locations
		  simpleline_place_t s1;
		  simpleline_place_t s2(si->sv.size()-1);
		  // create a custom viewer
		  si->cv = create_custom_viewer("", (TWinControl *)form, &s1, &s2, &s1, 0, &si->sv);
		  // set the handlers so we can communicate with it
		  set_custom_viewer_handlers(si->cv, NULL, NULL, NULL, NULL, NULL, si);
		  // also set the ui event callback
		  hook_to_notification_point(HT_UI, ui_callback, si);
		  // finally display the form on the screen
		  open_tform(form, FORM_TAB|FORM_MENU|FORM_RESTORE);
			}*/
  
	ana.Init();
//	msg("\nanainited\n");
	func_t *func = get_func(ea);
	//uint32 tm = rdtsc();

	if (!func)  {
		msg("No such function at %x\n", get_screen_ea());
		return;
	}

	if (func->endEA - func->startEA <= 6) {
		msg("too small to decompile\n");
		return;
	}

	if (func) {			

		msg("Start %x\nEnd: %x\n",func->startEA,func->endEA);
		if (!ana.AnalyzeOwn(func->startEA,func->endEA)) {
			msg("AnalyzeOwn error\n");
			return;
		}
	}
	msg("AnalyzeOwn has been ran\n");
	ana.Run();
	
	linepos = 0;
	lines.Init();
	ana.Dump2();
	//tm = rdtsc() - tm;

//	char buf[128];
//	msg("%s decompiled. clocks=%d\n", get_name(BADADDR, func->startEA, buf, sizeof(buf)), tm);
	importtodb(func->startEA, func->endEA);
	free_lines();
	ana.Free();
}

void killpseudo()
{
	ea_t ea = get_screen_ea();
	
	OutHdr oh;
	
	if (netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) {
		msg("No pseudocode at %x\n", ea);
		return;
	}

	// scan to start
	ea_t start = ea;
	// delete to start
	while (!(oh.flags & 1)) {
		start--;
		
		if ((netnode(start).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) || (oh.flags & 2)) { 
			msg("Netnode sync error %x\n", start); netnode(ea).supdel(PSEUDO_NETNODE_SUPVAL); 
			return; 
		}
		netnode(start).supdel(PSEUDO_NETNODE_SUPVAL);
	}

	// scan to end
	assert(netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) != -1);
	for(;;) {
		netnode(ea).supdel(PSEUDO_NETNODE_SUPVAL);
		if (oh.flags & 2) {
			ea += oh.ea;
			break;
		}
		ea++;
		if ((netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) || (oh.flags & 1)) { 
			msg("Netnode sync error %x\n", ea);
			return; 
		}
	}

	msg("Killing pseudo code from %x to %x\n", start, ea);
	do_unknown_range(start, ea - start, 0);
	analyze_area(start, ea);
	add_func(start, ea);
	_need_refresh = true;
}

ea_t get_orig_addr_from(ea_t ea)
{
	OutHdr oh;
	
	if (netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) return 0;

	if (oh.ea) return oh.ea;

	uint f = oh.flags, g=f;
		
	// if not found, search 2 items down and 2 items up
	for(int i=1; i<=2 && !(g&1); i++) {
		if (netnode(ea-i).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) break;
		if (oh.ea) return oh.ea;
		g = oh.flags;
	}

	for(int i=1; i<2 && !(f&2); i++) {
		if (netnode(ea+i).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) break;
		if (oh.ea) return oh.ea;
		g = oh.flags;
	}

	return 0;
}

ea_t get_pseudo_addr_from(ea_t fstart, ea_t ea)
{
	OutHdr oh;
	long thres = 0x7fffffff;
	ea_t best = 0;

	do {
		if (netnode(fstart).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) { return 0; }

		if (oh.ea == ea)
			return fstart;

		if (oh.ea > ea) {
			long diff = oh.ea - ea;
			if (diff < thres) {
				thres = diff;
				best = fstart;
			}
		}
	
		fstart++;
	} while (!(oh.flags & 2));

	return best;
}


void togglepseudo()
{
	ea_t ea = get_screen_ea();

	if (ea >= 0x8000000 && ea < 0xA000000) {
		func_t *ff = get_func(ea);
		if (!ff) { msg("%x: no function defined at current address\n", ea); return; }

		ea_t eax = get_orig_addr_from(ea);
		if (!eax) eax = ea;

		jumpto(eax + 0x400000);
	} else if (ea >= 0x8400000 && ea < 0x8800000) {
		func_t *ff = get_func(ea - 0x400000);
		if (!ff) { msg("%x: no function defined here in orig code\n", ea); jumpto(ea - 0x400000); return; }

		ea_t eax = get_pseudo_addr_from(ff->startEA, ea - 0x400000);
		if (!eax) eax = ea - 0x400000;

		jumpto(eax);
	} else {
		msg("%x: unknown region, cannot toggle pseudo code\n", ea);
	}
}

void mkfunctab()
{
	ea_t ea = get_screen_ea();
	if (ea & 3)
		return;

	if (has_dummy_name(getFlags(ea))) {
		char buf[32];
		for(int i=1; i!=1000; i++) {
			qsnprintf(buf, 32, "functable%d", i);
			if (set_name(ea, buf, SN_AUTO | SN_NOWARN))
				break;
		}
	}

	for(;;) {
		ea_t fea = get_long(ea);
		if (!(fea & 1))
			break;
		if (fea < 0x8000000 || fea >= 0x8400000)
			break;

		if (isUnknown(getFlags(fea))) {
			add_func(fea & ~1, BADADDR);
		}

		set_offset(ea, 0, 0);
	
		ea += 4;
		if (has_any_name(getFlags(ea)))
			break;
	}
	
}

void dbgline(byte *s)
{
	while (*s) {
		if (*s == 1) {
			msg("\\on%X\\", *++s);
		} else if (*s == 2) {
			msg("\\off%X\\", *++s);
		} else if (*s < 32 || *s >= 128)
			msg("\\%d", *s);
		else
			msg("%c", *s);
		s++;
	}
	msg("\n");
	
}
struct sample_info_t
{
  TForm *form;
  TCustomControl *cv;
  strvec_t sv;
};
int idaapi ui_callback(void *ud, int code, va_list va)
{
  sample_info_t *si = (sample_info_t *)ud;
  switch ( code )
  {
    // how to implement a simple hint callback
    case ui_get_custom_viewer_hint:
      {
        TCustomControl *viewer = va_arg(va, TCustomControl *);
        place_t *place         = va_arg(va, place_t *);
        int *important_lines   = va_arg(va, int *);
        qstring &hint          = *va_arg(va, qstring *);
        if ( si->cv == viewer ) // our viewer
        {
          if ( place == NULL )
            return 0;
          simpleline_place_t *spl = (simpleline_place_t *)place;
          hint.sprnt("Hint for line %d", spl->n);
          *important_lines = 1;
          return 1;
        }
      }
    case ui_tform_invisible:
      // a form is being closed, free the resources
      delete si;
      break;
  }
  return 0;
}

//---------------------------------------------------------------------------
// Create a custom view window
void decompall()

{
  
	
	    func_t *f;
		ea_t start = 0x080000C0;
//		ea_t start = 0x8001F17 - 1;

		LList<ea_t> funcs;

		funcs.Init();
		
		uint i = 0;
		while ( (f = get_next_func(start)) != NULL) {
			if (f->startEA >= 0x0A000000)
				break;
			
			char buf[50];
			if (get_name(BADADDR, f->startEA, buf, sizeof(buf)) && memcmp(buf, "asm", 3) == 0	) {
				// 
			} else {
				OutHdr oh;
				if (netnode(f->startEA).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) != -1)
					funcs.Append(f->startEA);
			}
			start = f->startEA + 1;
		}
		msg("There are %d funcs", funcs.GetCount());
		for(i=0; i!=funcs.GetCount(); i++) {
			msg("Decomp %x\n", funcs[i]);
			
			rundec(funcs[i]);
		}
		funcs.Free();
}

void fixgd(ea_t base, char *prefix)
{
	struc_t *st = get_struc(get_struc_id("GameDesc"));
	ea_t offset = get_struc_first_offset(st);

	char buf[100];

	do {
		char memname[MAXNAMESIZE];

		member_t *m = get_member(st, offset);
		if (!m)
			continue;

		get_member_name(m->id,memname,sizeof(memname));
		qsnprintf(buf, 100, "%s_%s", prefix, memname);
		ea_t ea = base + m->soff;

		if (isUnknown(getFlags(ea))) {
			switch(m->eoff - m->soff) {
			case 1:doByte(ea, 1); break;
			case 2:doWord(ea,2); break;
			case 4:doDwrd(ea,4); break;
			default:
				msg("%x foo %d\n", ea, m->eoff - m->soff);
			}
		}

		set_name(ea, buf);

		char comm[1024];
		if (get_member_cmt(m->id, false,comm,sizeof(comm)) != -1) {
//			msg("%x: comm %s\n", ea, comm);
			set_cmt(ea, comm, false);
		}

	} while ( (offset = get_struc_next_offset(st, offset)) != BADADDR);

}

void testme(int entry)
{
	//__try {

//		char buf[1024];
//		generate_disasm_line(get_screen_ea(), buf, sizeof(buf));
//		dbgline((byte*)buf);

//		return;

//		for(int i=0; i!=0xE54; i++)
//			put_byte(0x2000000 + i, get_byte(0x83E16D0 + i));

//		msg("\n");

		switch(entry) {
		case 0: rundec(); msg("rundec from LUDDE/&tryme"); break;
		case 1:killpseudo(); msg("killpseudo from LUDDE/&tryme"); break;
		//case 2: mkfunctab(); break;
		case 2:togglepseudo(); break;
		case 3:fixgd(0x083DA9C0, "SW"); fixgd(0x03008000, "GD"); break;//decompall(); break;
		case 4:mkfunctab(); break;
		}

		if (_need_refresh)
			refresh_idaview_anyway();


	//} __except(1) {
	//	msg("Exception\n");
	//}
//	msg("Foobar2\n");
}

void *LUDDE = &testme;
