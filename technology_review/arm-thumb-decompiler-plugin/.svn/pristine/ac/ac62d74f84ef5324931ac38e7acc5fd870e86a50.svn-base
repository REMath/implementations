


static char charbuf[80];

static int GetTypeOf(ea_t ea)
{
	flags_t flags = getFlags(ea);

	if (!isData(flags)) return T_UNK;
	if (isByte(flags))  return T_8BIT;
	if (isWord(flags))  return T_16BIT;
	if (isDwrd(flags))  return T_I32;

	return T_UNK;
}

static bool DontNeedExplicitType(int datatype, int reftype, bool store)
{
	if (datatype == reftype)
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




static const uint32 _typemask_size_masks[] = {
	0xffffffff,
	0xff,0xff,
	0xffff,0xffff,
	0xffffffff,
};

static char *PrintConstant(char *s, uint32 n, uint flags)
{

	char *q;
	char buf[40];

	
	if (flags & PF_EA && (q = get_name(BADADDR, n, charbuf, sizeof(charbuf))) != NULL) {
		// check if we don't need to write the type explicitly

		if (flags & PF_TYPEMASK && DontNeedExplicitType( GetTypeOf(n),(flags & PF_TYPEMASK) - 1, !!(flags & PF_EA_STORE))) {
			flags &= ~PF_TYPEMASK;
		}
		
	} else {
		q = buf;
		if (flags & PF_NEGCONST) {
			uint32 tmp_n = (~n) & _typemask_size_masks[flags & PF_TYPEMASK];
			if (CountBits(tmp_n) <= 2) {
				*q++ = '~';
				n = tmp_n;
			}
		}

		if (n < 10) {
			sprintf(q, "%d", n);
		} else {
			sprintf(q, "0x%X", n);
		}
		q = buf;
	}

	if (flags & PF_EA && flags & PF_TYPEMASK) { s = strcpy_e(s, TypeNames[(flags & PF_TYPEMASK) - 1]); }
	s = strcpy_e(s, q);
	if (flags & PF_EA && flags & PF_TYPEMASK ) { s = strcpy_e(s, ">"); }

	return s;
}
