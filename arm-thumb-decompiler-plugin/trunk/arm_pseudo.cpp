#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <netnode.hpp>
#include <struct.hpp>

#include "arm.h"


// stuff in linebuf is escaped.
// Escape codes:
//   1 <BYTE>   - Register Number
//   2 <UINT16> <UINT32> - Integer formatted in some special way. also used for addresses and refs.
//   3 <UINT16> <BYTE> - label name. the index is the index of the label. the byte is reserved.
//   4 <REG:4> <STORE:1> <TYPE:3> <UINT16>  - Register displacement memory access
//   5 <TYPE:4> <TID:32> <OFFS:32> - Struct offset memory load. On the form dword<R1 + StructName.member + 1>. starts a nesting group
//   6 - End of nesting.
// format of integer formatting word.
//  &0x78 = 0x00 - normal number which is not an address
//  &0x78 = 0x08 - dereferenced address, store
//  &0x78 = 0x10 - dereferenced address, load
//  &0x78 = 0x18 - address, but don't add a reference
//  &0x78 = 0x20 - subroutine call
//  &7           - access data type



static inline void mkimm(int n, long imm) {
	cmd.Operands[n].type = o_imm;
	cmd.Operands[n].value = imm;
	cmd.Operands[n].dtyp = dt_dword;
}

static inline void mkjmp(int n, ea_t ea)
{
	cmd.Operands[n].type = o_near;
	cmd.Operands[n].addr = ea;
}

static inline void mkdispl(int n, uint reg, uint type, long imm) {
	cmd.Operands[n].type = o_displ;
	cmd.Operands[n].reg = reg;
	cmd.Operands[n].addr = imm;
	cmd.Operands[n].dtyp = dt_dword;
	cmd.Operands[n].specflag1 = type;
}

const byte *scantoken(const byte *s, const byte *e)
{
	while (s<e && *s > 10) s++;
	return s;
}

enum {
	TF_TYPE_MASK = 7,
	TF_MASK = 0x78,
	TF_CALL = 0x20,
	TF_NUM = 0x00,
	TF_DEREF_STORE = 0x08,
	TF_DEREF_LOAD  = 0x10,
	TF_ADDRESS_NOREF = 0x18,

};

struct OutHdr {
	byte version;
	byte flags;		// upper 4 bits is indentation
	uint16 len;		// length of line
	ea_t ea;			// real address of this instruction, when flags&2 this is instead num remaining bytes
	uint16 label;
	int get_indent() { return flags >> 4; }
	bool is_empty_line_after() { return !!(flags & 4); }
};

/*


// stuff in linebuf is escaped.
// Escape codes:
//   1 <BYTE>   - Register Number
//   2 <UINT16> <UINT32> - Integer formatted in some special way. also used for addresses and refs.
//   3 <UINT16> <BYTE> - label name. the index is the index of the label. the byte is reserved.
//   4 <REG:4> <TYPE:4> <UINT16>  - Register displacement memory access
//   5 <TYPE:4> <TID:32> <OFFS:32> - Struct offset memory load. On the form dword<R1 + StructName.member + 1>. starts a nesting group
//   6 - End of nesting.


static const char * const _dereftypes[] = {
	"<&",
	"char<&",
	"byte<&",
	"short<&",
	"word<&",
	"dword<&",
};

static const char * const _dereftypes2[] = {
	"<",
	"char<",
	"byte<",
	"short<",
	"word<",
	"dword<",
};
*/

static const char * const _dereftypes[] = {
	"<&",
	"(char*)&",
	"(unsigned char*)&",
	"(unsigned short*)&",
	"(unsigned short*)&",
	"(unsigned long*)&",
};

static const char * const _dereftypes2[] = {
	"<",
	"(char)",
	"(unsigned char)",
	"(short)",
	"(unsigned short)",
	"(unsigned long)",
};
ea_t resolve_label(ea_t base, uint16 id)
{
	ea_t ea = base;
	OutHdr oh;
	// first search down, then search up
	for(;;) {
		if (netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) return NULL;
		if (oh.label == id)
			return ea;
		if (oh.flags & 1)
			break;
		ea--;
	}

	ea = base;
	// first search down, then search up
	for(;;) {
		if (netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,&oh,sizeof(oh)) == -1) return NULL;
		if (oh.label == id)
			return ea;
		if (oh.flags & 2)
			break;
		ea++;
	}

	return 0;
}


// Load type
enum {
	T_UNK,			// no idea what type it is

	T_I8, T_U8,
	T_I16,T_U16,
	T_I32,

	T_8BIT,			// 8 bit, but signedness is unknown
	T_16BIT,		// 16 bit, but signedness is unknown
};

uint GetMemberType(member_t *m)
{
	char cm;

	switch(m->eoff - m->soff) {
	case 4: return T_I32;
	case 2: {
		if (get_member_cmt(m->id, false, &cm, 1) == -1) return T_UNK;
		if (cm == 'S') return T_I16;
		return T_U16;
	}
	case 1: {
		if (get_member_cmt(m->id, false, &cm, 1) == -1) return T_UNK;
		if (cm == 'S') return T_I8;
		return T_U8;
	}
	}
	return T_UNK;
}

static int GetTypeOfStructInstance(ea_t ea, ea_t head, flags_t flags)
{
	typeinfo_t ti;
	if (!get_typeinfo(head, 0, flags, &ti)) return T_UNK;
	struc_t *sptr = get_struc(ti.tid);
	if (!sptr) return T_UNK;
	member_t *mptr = get_best_fit_member(sptr, ea - head);
	if (!mptr || mptr->soff != ea - head) return T_UNK;

	return GetMemberType(mptr);

}


static int GetTypeOf(ea_t ea)
{
	flags_t flags = getFlags(ea);

	if (isTail(flags)) {
		// check if it's a struct ptr
		ea_t head = get_item_head(ea);
		if (head == ea) return T_UNK;
		flags = getFlags(head);
		if (!isData(flags) || !isStruct(flags)) return T_UNK;
		return GetTypeOfStructInstance(ea, head, flags);
	}

	if (!isData(flags)) return T_UNK;
	
	if (isStruct(flags)) return GetTypeOfStructInstance(ea, ea, flags);

	if (isByte(flags)) {
		char s;
		if (has_cmt(flags) && (get_cmt(ea, false, &s, 1) != -1) && s == 'S') return T_I8;
		return T_U8;
	}
	if (isWord(flags)) {
		char s;
		if (has_cmt(flags) && (get_cmt(ea, false, &s, 1) != -1) && s == 'S') return T_I16;
		return T_U16;
	}
	if (isDwrd(flags))  return T_I32;

	return T_UNK;
}

static bool DontNeedExplicitType(int datatype, int reftype, bool store)
{
	if (datatype == reftype && datatype != T_UNK)
		return true;

	if (store) {
		switch(datatype) {
		case T_8BIT:
		case T_I8:
		case T_U8:
			return reftype == T_I8 || reftype == T_U8;

		case T_16BIT:
		case T_I16:
		case T_U16:
			return reftype == T_I16 || reftype == T_U16;

		default:
			return false;
		}
	} else {
		switch(datatype) {
		case T_8BIT: return reftype == T_U8;
		case T_16BIT:return reftype == T_U16;
		default:
			return false;
		}
	}
}


int ana_pseudo(const byte *s)
{
	if ( ((OutHdr*)s)->version != 0x11) {
		msg("%x: pseudo netnode version mismatch\n", cmd.ea);
		netnode(cmd.ea).supdel(PSEUDO_NETNODE_SUPVAL);
		return 0;
	}

	const byte *e = s + ((OutHdr*)s)->len;
	int nbytes = 1;

	if (((OutHdr*)s)->flags & 2) nbytes = ((OutHdr*)s)->ea;
	else if ( ((OutHdr*)s)->flags & 1 ) {
		OutHdr t;
		if (netnode(cmd.ea+1).supval(PSEUDO_NETNODE_SUPVAL, &t, sizeof(t) != -1) && t.len == sizeof(OutHdr))
			nbytes = 2;
	}

	cmd.itype = ARM_pseudo;

	s += sizeof(OutHdr);

	int n = 0;

	for(;;) {
		const byte *t = s;
		s = scantoken(s,e);
		if (s == e)
			break;
		switch(*s++) {
		case 1: // register
			s++;
			break;
		case 2: { // integer
			uint32 num = *(uint32*)(s+2);
			uint flags = *(uint16*)s;	
			s += 6;
			
			switch( (flags & TF_MASK) ) {
			case TF_CALL:
			case TF_DEREF_STORE:
			case TF_DEREF_LOAD:
			case TF_ADDRESS_NOREF:
				break;

			case TF_NUM:
				if (isEnabled(num) || n>= 6) {
					break;
				} else {
					mkimm(n++, num);
				}
				break;
			default:
				if (n < 6) {
					mkimm(n++, num);
				}
				break;
			}
			
			break;
		}
		case 3: // label
			if (n < 6) {
				ea_t ea= resolve_label(cmd.ea, *(uint16*)s);
				mkjmp(n++, ea);	
			}
			s += 3;
			break;

		case 4: { // reg displacement memory access
			if (n < 6) {
				mkdispl(n++, *(byte*)s >> 4, *(byte*)s & 0xF, *(int16*)(s+1));
			}
			s += 3;
			break;
		}

		case 5: // struct offset thingy
			s += 9; // skip 1+4+4 bytes
			break;

		case 6: // end of nesting
			break;	// no params

		default:
			msg("ANA ERROR!!\n");
			return nbytes; // ERROR
		}
	}	

	return nbytes;
}

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

int IsStructOffs(op_t &op, uint32 f, tid_t *path, adiff_t *delta)
{
	uint n;

	if (op.n == 0) {
		if (!isStroff0(f))
			return 0;
		n = get_stroff0(cmd.ea, path, delta);
	} else {
		if (!isStroff1(f))
			return 0;	
		n = get_stroff1(cmd.ea, path, delta);
	}
	return n;
}

bool IsOperandValueShown(op_t &op, uint32 f)
{
	if (op.addr)
		return true;
	if (op.n == 0) return isDefArg0(f);
	else return isDefArg1(f);	
}


void outhexnumpm(long a)
{
	if (a >= 0)
		out_symbol('+');
	else if (a < 0) {
		a = -a;
		out_symbol('-');
	}
	out_tagon(COLOR_NUMBER);
	OutLong(a, a <= 9 ? 10 : 16);
	out_tagoff(COLOR_NUMBER);
}


bool outop_pseudo(op_t *op)
{
	int ctrl=1;
	if (op->type == o_imm) {
		flags_t f = getFlags(cmd.ea);		
		bool b = (op->n == 0) ? isOff0(f) : isOff1(f);
		if (b && has_dummy_name(getFlags(op->value)) )
			out_symbol('&');

		//OutValue(*op, (op->value & 0xffff0000) == 0xffff0000 ? OOF_SIGNED : 0);
		OutValue(*op);
		return true;
	}
	
	if (op->type == o_displ) {
		adiff_t delta;
		tid_t path[MAXSTRUCPATH];
		int n;

		flags_t f = getFlags(cmd.ea);		

		// check if it's a structure offset
		if ((n=IsStructOffs(*op, f, path, &delta)) != 0) {
			ea_t soff = op->addr + delta;
			
			struc_t *st = get_struc(path[0]);
			member_t *mem = st ? get_best_fit_member(st, soff) : NULL;
			bool dont_need_type = mem && mem->soff == soff && DontNeedExplicitType(GetMemberType(mem), op->specflag1&7, !!(op->specflag1&0x8));
			
			if (!dont_need_type) { 
				if((op->specflag1 & 7)==0){
					ctrl=0;
					
				} 
				OutLine(_dereftypes[op->specflag1 & 7]); 
			
			}

			if (delta != 0) {
				out_symbol('(');
				out_register(_regs[op->reg]);
				outhexnumpm(delta);
				out_symbol(')');
			} else {
				out_register(_regs[op->reg]);
			}
	
			out_symbol('.');
//			out_symbol('>');

			if (mem == NULL) {
				out_tagon(COLOR_ERROR);
				OutLine("ERR");
				OutLong(soff, 16);
				out_tagoff(COLOR_ERROR);
			} else {
				char strucname[MAXNAMESIZE], membername[MAXNAMESIZE];

				if ((get_struc_name(st->id,strucname,sizeof(strucname)) != -1) && 
					(get_member_name(mem->id,membername,sizeof(membername)) != -1)) {

					out_tagon(COLOR_DNAME);
					out_snprintf("%s.%s", strucname,membername);
					out_tagoff(COLOR_DNAME);

					if (mem->soff != soff) {
						outhexnumpm(soff - mem->soff);
					}
				}
			}

			if (!dont_need_type&&(op->specflag1 & 7)==0) { OutLine(">"); }
		
		} else {
			OutLine(_dereftypes2[op->specflag1 & 7]);
			out_register(_regs[op->reg]);
			if (IsOperandValueShown(*op, f)) {
				OutValue(*op, OOFS_NEEDSIGN | OOF_SIGNED | OOF_ADDR);
			}
			if((op->specflag1 & 7)==0)OutLine(">");
		}

		
		return true;
	}

	return false;
}


static char *DecodeAddress(ea_t ea, int &type)
{
	char b[MAXNAMESIZE];
	if (get_name_expr(cmd.ea, 0, ea, ea, b, sizeof(b)) == -1) return NULL;
	type = GetTypeOf(ea);
	return strdup(b);
}


void printnum(uint32 num, uint16 fmt)
{
	out_long(num, 10);
}

union StackedOutOp {
	struct {
		byte type;
		bool dont_need_type;
		tid_t tid;
		struc_t *st;
		member_t *mb;
		uint32 offs;
	} str;
};


void out_pseudo()
{
	char buf[1024];
	const byte *s, *e, *sb;
	OutHdr oh;
		
	StackedOutOp soo[16];
	int nsoo = 0;


	init_output_buffer(buf, sizeof(buf));
	if (netnode(cmd.ea).supval(PSEUDO_NETNODE_SUPVAL,&oh, sizeof(oh)) == -1) {
		MakeLine("<netnode error>"); msg("no netnode anymore at %x\n", cmd.ea); return; 
	}

	sb = (byte *)malloc(oh.len);
	if (!sb) {	MakeLine("<netnode error>"); msg("no netnode anymore at %x\n", cmd.ea); return; }

	if (netnode(cmd.ea).supval(PSEUDO_NETNODE_SUPVAL,(void *)sb,sizeof(oh)+oh.len) == -1) {
		MakeLine("<netnode error>"); msg("no netnode anymore at %x\n", cmd.ea); 
		free((void *)sb);
		return; 
	}

	s=sb;
	// determine end of buffer
	e = s + ((OutHdr*)s)->len;

	bool empty_line = ((OutHdr*)s)->is_empty_line_after();

	// print indent?
	if (((OutHdr*)s)->get_indent()) {
		int n = ((OutHdr*)s)->get_indent();
		if (n > 1) n = n*3-2;
		out_snprintf("%*c",n , ' ');
	}

	s += sizeof(OutHdr);

	assert(s <= e);

	int n = 0;

	for(;;) {
		const byte *t = s;
		s = scantoken(s,e);

		if (t != s) {
			out_snprintf("%.*s", s - t, t);
		}

		assert(s<=e);
		if (s == e)
			break;

		switch(*s++) {
		case 1: // register
			out_register(_regs[*s++]);
			break;
		case 2: {
			uint32 num = *(uint32*)(s+2);
			uint flags = *(uint16*)s;	
			s += 6;

			switch( (flags & TF_MASK) ) {

			case TF_ADDRESS_NOREF: {
				char b[MAXNAMESIZE];
				if (get_name_expr(cmd.ea, 0, num, num, b, sizeof(b)) == -1)
					qstrncpy(b,"<UNK>",MAXNAMESIZE);
				OutLine(b);
				break;
			}

			case TF_CALL: {
				char buf[64];
				if (get_name(cmd.ea, num, buf, sizeof(buf))) {
					out_tagon(COLOR_LIBNAME);
					OutLine(buf);
					out_tagoff(COLOR_LIBNAME);
				} else {
					char b[MAXNAMESIZE];
					if (get_name_expr(cmd.ea, 0, num, num, b, sizeof(b)) == -1)
						qstrncpy(b,"<UNK>",MAXNAMESIZE);
					OutLine(b);
				}
				break;
			}

			case TF_DEREF_LOAD:
			case TF_DEREF_STORE: {
				int type;
				char *b = DecodeAddress(num,type);
				if (b) {
					bool dont_need_type = DontNeedExplicitType(type, flags & TF_TYPE_MASK, (flags & TF_MASK) == TF_DEREF_STORE);
					if (!dont_need_type) out_keyword(_dereftypes[flags & TF_TYPE_MASK]);
					OutLine(b);
					if (!dont_need_type&&((flags & TF_TYPE_MASK)==0)) out_keyword(">");
				} else {
					out_keyword(_dereftypes2[flags & TF_TYPE_MASK]);
					out_long(num,16);
					if(((flags & TF_TYPE_MASK)==0))out_keyword(">");
				}
				break;
			}

			case TF_NUM: {
				if (isEnabled(num) || n>= 6) {
					char b[MAXNAMESIZE];
					if (get_name_expr(cmd.ea, 0, num, num, b, sizeof(b)) == -1) {
						out_long(num, 16);
					} else {
						out_symbol('&');
						OutLine(b);
					}
				} else {
					out_one_operand(n++);
				}
				break;
			}

			default:
				if (n < 6) {
					out_one_operand(n++);
				}
				break;
			}

			break;
		}

		case 3: // label
			if (n < 6) {
				if (cmd.Operands[n].addr == 0) {
					OutLine("<unresolved label>");
				} else {
					out_one_operand(n);
				}
				n++;
			}
			s += 3;
			break;

		case 4: // register displacement
			if (n < 6) {
				out_one_operand(n++);
			}
			s += 3;
			break;

		case 5: {// struct offset
			StackedOutOp &so = soo[nsoo++];
			so.str.type = *(byte*)(s + 0); // low 3 bits are type, bit 0x8 is if it's a store
			so.str.tid = *(tid_t*)(s + 1);
			so.str.offs = *(uint32*)(s + 5);
			s += 9;

			// locate the member
			so.str.st = get_struc(so.str.tid);
			so.str.mb = so.str.st ? get_best_fit_member(so.str.st, so.str.offs) : NULL;
			
			if (so.str.type == 0) {
				so.str.dont_need_type = true;
				out_symbol('&');
			} else {
				so.str.dont_need_type = so.str.mb && so.str.mb->soff == so.str.offs && DontNeedExplicitType(GetMemberType(so.str.mb), so.str.type & 0x7, !!(so.str.type & 0x8));
				// if a type is neccessary, print the deref thing..
				if (!so.str.dont_need_type) {
					OutLine(_dereftypes2[so.str.type & 7]);
				}
			}
			break;
		}

		case 6: {
			StackedOutOp &so = soo[--nsoo];
			// prints in one of two formats:
			//   EXP:StructName.VarName
			// dword<EXP + StructName.VarName + 2>

			// print the rest of the line
			if (so.str.dont_need_type) {
				out_symbol(':');
			} else {
				OutChar(' '); out_symbol('+'); OutChar(' ');
			}

			// print StructName.VarName.. OR.. <RED>Offs</RED>.. OR.. StructName.<RED>Offs</RED>
			if (so.str.mb) {
				char fullname[MAXNAMESIZE];
				get_member_fullname(so.str.mb->id,fullname,sizeof(fullname));
				OutLine(fullname);
				if (so.str.mb->soff != so.str.offs) { outhexnumpm(so.str.offs - so.str.mb->soff); }
			} else {
				if (so.str.st) {
					char strucname[MAXNAMESIZE];
					get_struc_name(so.str.st->id,strucname,sizeof(strucname));
					OutLine(strucname);
					out_symbol('.');
				}
				out_tagon(COLOR_ERROR);
				OutLong(so.str.offs, 16);
				out_tagoff(COLOR_ERROR);
			}

			if((so.str.type&7)==0)
				if (!so.str.dont_need_type) out_symbol('>');
	
			break;
		}

		default:
			OutLine("<ERROR!!>");
			goto out;
		}
	}
out:
	term_output_buffer();
	
	gl_comm = 1;
	MakeLine(buf);

	if (empty_line)
		MakeNull();

	free((void *)sb);
}

void emu_pseudo()
{
	OutHdr oh;
	const byte *s, *buf;

	if (netnode(cmd.ea).supval(PSEUDO_NETNODE_SUPVAL,&oh, sizeof(oh)) == -1) return;
	if ((buf= (byte *)malloc(oh.len)) == NULL) return;

	if (netnode(cmd.ea).supval(PSEUDO_NETNODE_SUPVAL,(void *)buf,sizeof(oh)+oh.len) == -1) {
		free((void *)buf);
		return; 
	}

	s = buf;
	const byte *e = s + ((OutHdr*)s)->len;
	uint n = 0;
	if (!(((OutHdr*)s)->flags & 2)) {
		ua_add_cref(0,cmd.ea+cmd.size,fl_F);
	}	
	s += sizeof(OutHdr);

	for(;;) {
		const byte *t = s;
		s = scantoken(s,e);
		if (s == e)
			break;
		switch(*s++) {
		case 1: // register
			s++;
			break;
		case 2: { // integer
			uint32 num = *(uint32*)(s+2);
			uint flags = *(uint16*)s;	
			s += 6;
			
			switch( (flags & TF_MASK) ) {
			case TF_ADDRESS_NOREF:
				break;

			case TF_CALL:
				ua_add_cref(0,num,fl_CN);	
				break;
			case TF_DEREF_STORE:
			case TF_DEREF_LOAD: {
				
				//msg("Adding dref from %x to %x\n", cmd.ea, num);
				ua_add_dref(0,num, (flags & TF_MASK) == TF_DEREF_STORE ? dr_W : dr_R);
				
				if (isUnknown(getFlags(num)) && isEnabled(num)) {
					switch(flags & TF_TYPE_MASK) {
					case T_I8: case T_U8:  doByte(num,1); break; 
					case T_I16: case T_U16:doWord(num,2); break;
					case T_I32: doDwrd(num,4); break;
					}
				}
				break;
			}
			case TF_NUM: {
				if (isEnabled(num)) {
					ua_add_dref(0,num,dr_O);
				} else if (n>=6) {
				} else {
					op_t &op = cmd.Operands[n];
					if (isOff(getFlags(cmd.ea), op.n))
						ua_add_off_drefs(op, dr_O);
					doImmd(cmd.ea);
				}
				break;
			}
			}
			
			break;
		}
		case 3: // label
			if (n < 6) {
				ea_t ea= resolve_label(cmd.ea, *(uint16*)s);
				if (ea)
					ua_add_cref(0,ea,fl_JN);		
			}
			s += 3;
			break;

		case 4: // register displacement
			s += 3;
			doImmd(cmd.ea);
			break;

		case 5:
			s += 9; // 1+4+4
			break;

		case 6:
			break;	// no params

		default:
			free((void *)buf);
			return;
		}
	}
	free((void *)buf);

}
