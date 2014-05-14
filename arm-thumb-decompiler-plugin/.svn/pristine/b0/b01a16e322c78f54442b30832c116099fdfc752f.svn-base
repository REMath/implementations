#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <netnode.hpp>
#include <struct.hpp>

#include "arm.h"


// first two bytes mean length of instruction.
// if 0x8000 - chained to address + 1
// if 0x4000 - chained to address - 1

// the rest is a zero terminated string with special tokens in it.

// token 1:
//   byte - register index

// token 2:
//   dword - immediate dword value

// token 3:
//   dword - near label address

// token 4:
//   str - number

// token 5:
//   dword - structid
//   dword - offset

// token 10: newline

enum {
	FLAG_CHAIN_NEXT = 0x8000,
	FLAG_CHAIN_PREV = 0x4000,
	FLAG_LENMASK = 0x3FFF,
	FLAG_SIZE = sizeof(uint16)
};


static inline void mkimm(int n, long imm, int reg = -1) {
	cmd.Operands[n].type = o_imm;
	cmd.Operands[n].value = imm;
	cmd.Operands[n].dtyp = dt_dword;
	cmd.Operands[n].specflag1 = reg;
}

static inline void mkjmp(int n, ea_t ea)
{
	cmd.Operands[n].type = o_near;
	cmd.Operands[n].addr = ea;
}

int ana_manual(char *s)
{
	int len;
	byte c;
	int n = 0;

	cmd.itype = ARM_manual;

	len = *(uint16*)s;
	s += FLAG_SIZE;

	while (c = *s++) {
		if (c == 1) s++; // skip register
		else if (c == 2) {
			if (n == 6) break;
			mkimm(n, *(uint32*)s);
			s += sizeof(uint32);
			n++;
		} else if (c == 3 || c == 6) {
			if (n == 6) break;
			mkjmp(n, *(uint32*)s);
			cmd.Operands[n].specflag1 = (c == 6);
			s += sizeof(uint32);
			n++;
		} else if (c == 4) {
			do s++; while (s[-1]); // skip number
		} else if (c == 5) {
			s += sizeof(uint32) * 2;
		}
	}

	if (n != 6)
		cmd.Operands[n].type = o_void;

	return len & FLAG_LENMASK;
}

void out_manual()
{
	char buf[1024];
	char *s, sb[1024];
	byte c;
	int n;
	char tmp[256];

	init_output_buffer(buf, sizeof(buf));

	if (netnode(cmd.ea).supval(LUDDE_NETNODE_SUPVAL,sb,sizeof(sb)) == -1) {
		MakeLine("<netnode error>"); msg("no netnode anymore at %x\n", cmd.ea); 
		return; 
	}

	s=sb;

	if ( *(uint16*)s & FLAG_CHAIN_PREV) {
		if (*(uint16*)s & FLAG_CHAIN_NEXT) {
			out_symbol('|');
		} else {
			out_symbol('\x19');
		}
	} else {
		if (*(uint16*)s & FLAG_CHAIN_NEXT) {
			out_symbol('\x18');
		} else {
			out_symbol('|');
		}
	
	}

	s += FLAG_SIZE;

	n = 0;
	while (c = *s++) {
		if (c == 1) {
			out_register(_registers[(byte)*s++]);
		} else if (c == 2 || c == 3 || c == 6) {
			if (n == 6) break;
			out_one_operand(n++);
			s += sizeof(uint32);
		} else if (c == 4) {
			// output a number
			out_line(s, COLOR_NUMBER);
			do s++; while (s[-1]);
		} else if (c == 5) {
			tid_t sid = ((uint32*)s)[0];
			ulong offs = ((uint32*)s)[1];
			struc_t *sp;
			member_t *memb;
			s += sizeof(uint32) * 2;
			if ((sp = get_struc(sid)) == NULL || (memb = get_best_fit_member(sp, offs)) == NULL) {
				if (sp) {
					char strucname[MAXNAMESIZE];
					get_struc_name(sid,strucname,sizeof(strucname));
					qsnprintf(tmp, sizeof(tmp), "%s.%u", strucname, offs);
				} else {
					qsnprintf(tmp, sizeof(tmp), "struc%X.%u", sid, offs);
				}
				out_line(tmp, COLOR_ERROR);
			} else {
				char fullname[MAXNAMESIZE];
				get_member_fullname(memb->id,fullname,sizeof(fullname));
				out_line(fullname, COLOR_DEFAULT);
			}
		} else if (c == 10) {
			term_output_buffer();
			gl_comm = 1;
			MakeLine(buf);
			init_output_buffer(buf, sizeof(buf));
			out_symbol('.');
		} else {
			// deduce a keyword
			if (isalpha(c)) {
				// get length of string
				int n = 0;
				do n++; while (isalpha((byte)s[n-1]));
				// output keyword	
				if (--n >= 1) {
					char bak = s[n];
					s[n] = 0;
					out_keyword(s - 1);
					s[n] = bak;
					s += n;
					continue;
				}
			}
			
			if (c >= '!' && c <= '/' || c>=':' && c<='@' || c>='[' && c <= '`')
				out_symbol(c);
			else
				OutChar(c);
		}
	}

	term_output_buffer();
	gl_comm = 1;
	MakeLine(buf);
}

int kill_manual(ea_t ea, int *nchain)
{
	int len;
	ea_t ea_org = ea;
	int n = 0;

	do {
		char s[1024];
		if (netnode(ea).supval(LUDDE_NETNODE_SUPVAL,s,sizeof(s)) == -1)
			break;
		len = *(uint16*)s;
		netnode(ea).supdel(LUDDE_NETNODE_SUPVAL);
		netnode(ea).supdel(LUDDE_NETNODE_SUPVAL2);
		n++;
		ea += (len & FLAG_LENMASK);
	} while (len & FLAG_CHAIN_NEXT);

	*nchain = n;

	return ea - ea_org;
}

int is_register_name(char *s) {
	int r;
	char *end;
	if ((*s != 'r' && *s != 'R') || s[1] == 0 || s[2] != 0 && s[3] != 0) return -1;
	r = strtoul(s + 1, &end, 10);
	if (*end != 0 || r >= 16) return -1; 
	return r;	
}

bool make_manual(ea_t ea, int len, char *s)
{
	char c, *t;
	byte buf[1024];
	byte *p;
	bool last_symbol_hash;
	int opn = 0;
	member_t *mt;
	struc_t *place[16];
	ea_t myea;
	int oldlen = 0;
	char *sorg = s;
	int pos;
	int nchain = 0;
	char oldop[1024];

	if (len < 0 || len > 256) {
		// this must be an error by the user!
		msg("Refusing to add manual operand for %d bytes\n", len);
		return false;
	}

	if (netnode(ea).supval(LUDDE_NETNODE_SUPVAL,oldop,sizeof(oldop)) != -1) {
		if (*(uint16*)oldop & FLAG_CHAIN_PREV) {
			msg("Address %x already has a manual operand\n", ea);
			return false;
		}
		oldlen = kill_manual(ea, &nchain);
	}

	if (*s == 0) {
		if (oldlen) {
			do_unknown_range(ea, oldlen, 0);
			ua_code(ea);
		}
		return true;
	}

	p = buf + FLAG_SIZE;
	pos = 0;

	last_symbol_hash = false;
	opn = 0;

	while (c = *s++) {
		// start of word?
		if (isalnum(c) || c == '_') {
			int n = 0;
			int reg;
			
			s--;
			do n++; while (isalnum((byte)s[n]) || s[n] == '_' || s[n] == '.');
	
			char bak = s[n];
			s[n] = 0;

			reg = is_register_name(s);
			if (reg != -1) {
				*p++ = 1;
				*p++ = reg;
			} else if ((t=strchr(s, '.')) && (mt = get_member_by_fullname(s, place))) {
//				msg("adding struct %s at offset %d\n", s, mt->soff);				
				*p++ = 5;

				char bak = *t;
				*t = 0;
				((uint32*)p)[0] = get_struc_id(s);
				((uint32*)p)[1] = mt->soff;
				p += sizeof(uint32) * 2;
				*t = bak;

			} else if ((myea = get_name_ea(ea + pos, s)) != BADADDR && (myea & 0xFF000000) != 0xFF000000) {
				if (isCode(getFlags(myea))) {
					if (last_symbol_hash) {
						p--;
						*p++ = 6;
					} else {
						*p++ = 3;
					}
				} else {
					*p++ = 2;
				}
				*(ea_t*)p = myea;
				p += sizeof(uint32);
				opn++;
			} else if (s[0] >= '0' && s[0] <= '9') {
				if (last_symbol_hash) {
					p--;
					*p++ = 2;
					*(ea_t*)p = strtoul(s, NULL, 0);
					p += sizeof(uint32);
					opn++;
				} else {
					*p++ = 4;
					qstrncpy((char*)p, s, (1024-(p-buf)));
					p += n + 1;
				}
			} else {
				memcpy(p, s, n);
				p += n;
			}
			s[n] = bak;
			
			s += n;
		} else if (c == 10 && pos+1 < len) {
			// new instruction
			*p++ = 0;

			// commit the instruction!
			*(uint16*)buf = FLAG_CHAIN_NEXT + 1 + (pos == 0 ? 0 : FLAG_CHAIN_PREV);
			netnode(ea + pos).supset(LUDDE_NETNODE_SUPVAL, buf, p - buf);
			p = buf + FLAG_SIZE;

			// move to next instruction
			pos++;

		} else {
			last_symbol_hash = c == '%';
			*p++ = c;
		}
	}
	*p++ = 0;

	// chained also?
	*(uint16*)buf = len - pos + (pos == 0 ? 0 : FLAG_CHAIN_PREV);
	netnode(ea + pos).supset(LUDDE_NETNODE_SUPVAL, buf, p - buf);

	netnode(ea).supset(LUDDE_NETNODE_SUPVAL2, sorg);

	if (len != oldlen || nchain != pos + 1) {
		do_unknown_range(ea, len > oldlen ? len : oldlen, 0);
		ua_code(ea);
	}

	return true;
}

static char *get_string_from(ulong start, int n)
{
	static char buf[4096];
	int pos = 0;
	ulong end = start + n;

	do {
		generate_disasm_line(start, buf + pos, sizeof(buf));
		pos += tag_remove(buf + pos, buf + pos, sizeof(buf) - pos - 1);
		buf[pos++] = '\n';
		start += get_item_size(start);
	} while (start < end && pos + MAXSTR < 4095);
	// remove trailing '\n'
	buf[pos-1] = 0;
	return buf;
}

bool has_man_oper(ea_t start, int len)
{
	char s[1024];

	while (len) {
		if (netnode(start).supval(LUDDE_NETNODE_SUPVAL,s,sizeof(s)) != -1) return true;
		start++;
		len--;
	}
	return false;
}

void domanual()
{
	char buf[1024];
	ulong start, end;
	int n, ret;
	char s[1024];
		
	if (callui(ui_readsel, &start, &end).cnd) {
		n = end - start;
	} else {
		start = get_screen_ea();
		n = get_item_size(start);
	}

	ret = 0;
	// search to the start of the block
	while ((ret = netnode(start).supval(LUDDE_NETNODE_SUPVAL,s,sizeof(s))) != -1) {
		if ( !(*(uint16*)s & FLAG_CHAIN_PREV )) break;
		start--;
		n++;
	}

	int exlen = 0;

	// get the length of the old block...
	if (ret != -1) {
		do {
			if (netnode(start + exlen).supval(LUDDE_NETNODE_SUPVAL,s,sizeof(s)) == -1) { msg("netnode consistency error!\n"); return; }
			exlen += *(uint16*)s & FLAG_LENMASK;
		} while (*(uint16*)s & FLAG_CHAIN_NEXT);

		// make sure we're modifying the whole block.
		if (n < exlen) n = exlen;
	}

	// make sure there are no other manual operands in between
	if (has_man_oper(start + exlen, n - exlen)) {
		msg("Area has manual operands already\n");
		return;
	}

	if (netnode(start).supval(LUDDE_NETNODE_SUPVAL2,s,sizeof(s)) == -1) qstrncpy(s,get_string_from(start, n),1024);

	if (vasktext(sizeof(buf), buf, s, "Enter instruction representation", NULL)) {
		make_manual(start, n, buf);	
	}
}

void emu_manual()
{
	int i;

	for(i=0; i!=6 && cmd.Operands[i].type != o_void; i++) {
		if (cmd.Operands[i].type == o_imm)
			ua_add_off_drefs(cmd.Operands[i], dr_O);
		else if (cmd.Operands[i].type == o_near) {
			ua_add_cref(0,cmd.Operands[i].addr,cmd.Operands[i].specflag1 ? fl_CN : fl_JN);	
		}
	}

	ua_add_cref(0,cmd.ea+cmd.size,fl_F);
}
