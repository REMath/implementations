
typedef unsigned char byte;
static ea_t ea; // current address within the instruction

static const char * const _registers[] = { "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15" };

#define LUDDE_NETNODE_SUPVAL 0x999
#define LUDDE_NETNODE_SUPVAL2 0x998
#define PSEUDO_NETNODE_SUPVAL 0x997


enum nec_insn_type_t
{
  ARM_movl = CUSTOM_CMD_ITYPE,
	ARM_move,

	ARM_ldr_data,
	ARM_str_data,
	ARM_ldrb_data,
	ARM_strb_data,
	ARM_ldrh_data,
	ARM_strh_data,

	ARM_movzb,
	ARM_movsb,
	ARM_movzw,
	ARM_movsw,

	ARM_ldr,
	ARM_ldrb,
	ARM_ldrh,

	ARM_ldrsh,
	ARM_ldrsb,

	ARM_str,
	ARM_strb,
	ARM_strh,

	ARM_add,
	ARM_and,
	ARM_sub,

	ARM_ifgoto,

	ARM_manual, // used by the manual instruction thingy..
	ARM_pseudo, // used for pseudo code
};




extern int ana_manual(char *s);
extern int ana_pseudo(const byte *s);
extern int ana_simplify();

extern void out_manual();
extern void out_pseudo();
extern void out_simplify();

extern void emu_manual();
extern void emu_pseudo();
extern void emu_simplify();

extern bool outop_simplify(op_t *op);
extern bool outop_pseudo(op_t *op);

extern const char *get_insn_mnem(void);
