#include <assert.h>
enum {
	E_CONST = 1,
	E_REG		= 2,
	E_MOV		= 3,
	E_BIN		= 4,
	E_UN    = 5,
	E_STOR  = 6,
	E_LOAD  = 7,

	E_CALL = 8, // function call

	E_OTHER = 9,

	E_COND = 10,

	E_CHOOSE = 11, // trinary choose operator
	E_RETURN = 12, // return value from function
};

enum {
	E_INVALID,

	E_AND,E_EOR,E_LSL,E_LSR,E_ASR,E_ROR,E_ORR,E_MUL,E_BIC,E_ADD,E_SUB, 
	
	E_LOR,E_LAND, 
	
	E_COMP_EQ,
	E_COMP_NE,
	E_COMP_CS,
	E_COMP_CC,
	E_COMP_MI,
	E_COMP_PL,
	E_COMP_VS,
	E_COMP_VC,
	E_COMP_HI,
	E_COMP_LS,
	E_COMP_GE,
	E_COMP_LT,
	E_COMP_GT,
	E_COMP_LE,

	// unary operators
	E_MVN,E_NEG, E_LNOT,
	E_FROM_U8,E_FROM_U16,// zero extend
	E_FROM_I8,E_FROM_I16,// sign extend
};

#define R 0x80
#define L 0x40
#define B 0xC0

// higher number means higher precendence
static const byte _expression_prec[]= {
	1,

//	E_AND,E_EOR,E_LSL,E_LSR,E_ASR,E_ROR,E_ORR,E_MUL,E_BIC,E_ADD,E_SUB, 
	   B|2, B|10, B|16, B|16, B|16, B|16,  B|8, B|20,  B|18, L|18,   L|18,

//	E_LOR,E_LAND, 
	4,6,

	// 14 compare operators
	14,14,14,14,14,14,14,14,14,14,14,14,14,14,

	// 7 unary operators
	20,20,20,
	0,0,0,0,
};

#undef B
#undef R
#undef L

// Load type
enum {
	T_I8, T_U8,
	T_I16,T_U16,
	T_I32,

// extra types only needed by	GetTypeOf()
	T_UNK,			// no idea what type it is
	T_8BIT,			// 8 bit, but signedness is unknown
	T_16BIT,		// 16 bit, but signedness is unknown
};


enum {
	CC_USER = 0x10000, // calling convention was entered by the user, so it's definite
	CC_RET  = 0x20000, // returns a value in R0
};


enum {
	TI_NONE = 0,	// type not determined yet
	TI_UNK = 1,		// type unknown or conflict
	TI_NULL = 2,	// number 0
	TI_STRUCT = 3,
	TI_INDIRECT = 0x1000, // struct has an indirect modifier
	TI_INDIRECT_MASK = 0x3000, // struct has an indirect modifier
};

typedef unsigned short TypeId;



union Exp {
	byte type;
	struct {
		byte type;
		uint32 num;
	};
	struct {
		byte type;
		byte reg;
	};
	struct {
		byte type;
		byte reg;
		TypeId tid; // tagged with the type that's put into the register.
		Exp *e;
	} mov;
	struct {
		byte type;
		byte subtype;
		Exp *left, *right;
	} bin;
	struct {
		byte type;
		byte subtype;
		Exp *left;
	} un;
	struct {
		byte type;
		ea_t addr;
		uint32 conv; // calling convention, low 16 bits = which args are inputs?
		Exp *arg[4];
	} call;
	struct {
		byte type;
		ArmIns ins;
	} other;
	struct {
		byte type;
		byte subtype;
		Exp *ea;
	} load;
	struct {
		byte type;
		byte subtype;
		byte oper;
		Exp *ea;
		Exp *value;
	} store;
	struct {
		byte type;
		Exp *e;
	} cond;
	struct {
		byte type;
		Exp *e, *left,*right;
	} choose;
	struct {
		byte type;
		Exp *e;
	} ret;
};

#ifdef WITH_CONSTRUCTORS

Pool _exp_pool;

static inline Exp *NewExp(int size = sizeof(Exp)) { return (Exp*)_exp_pool.Alloc(size); }

Exp *NewConstExp(uint32 c) {
	Exp *e = NewExp(offsetofend(Exp,num));
	e->type = E_CONST;
	e->num = c;
	return e;
}

Exp *NewRegExp(byte r) {
	Exp *e = NewExp(offsetofend(Exp,reg));
	e->type = E_REG;
	e->reg = r;	
	return e;
}

Exp *NewMovExp(byte r, Exp *ee)
{
	Exp *e = NewExp(offsetofend(Exp,mov));
	e->type = E_MOV;
	e->mov.reg = r;
	e->mov.e = ee;
	return e;
}

Exp *NewBinExp(byte s, Exp *l, Exp *r)
{
	Exp *e = NewExp(offsetofend(Exp,bin));
	e->type = E_BIN;
	e->bin.subtype = s;
	e->bin.left = l;
	e->bin.right = r;
	return e;
}

Exp *NewUnExp(byte s, Exp *l)
{
	Exp *e = NewExp(offsetofend(Exp,un));
	e->type = E_UN;
	e->un.subtype = s;
	e->un.left = l;
	return e;
}

Exp *NewCallExp(ea_t a)
{
	Exp *e = NewExp(offsetofend(Exp,call));
	e->type = E_CALL;
	e->call.addr = a;
	e->call.conv = 0;
	memset(e->call.arg, 0, sizeof(e->call.arg));
	return e;
}

Exp *NewOtherExp(const ArmIns &i)
{
	Exp *e = NewExp(offsetofend(Exp,other));
	e->type = E_OTHER;
	e->other.ins = i;
	return e;	
}

Exp *NewLoadExp(byte s, Exp *ea)
{
	Exp *e = NewExp(offsetofend(Exp,load));
	e->type = E_LOAD;
	e->load.subtype = s;
	e->load.ea = ea;
	return e;
}

Exp *NewStoreExp(byte s, Exp *ea, Exp *v)
{
	Exp *e = NewExp(offsetofend(Exp,store));
	e->type = E_STOR;
	e->store.subtype = s;
	e->store.ea = ea;
	e->store.value = v;
	e->store.oper = 0;
	return e;
}

Exp *NewCondExp(Exp *ee)
{
	Exp *e = NewExp(offsetofend(Exp,cond));
	e->type = E_COND;
	e->cond.e = ee;
	return e;
}

Exp *NewChooseExp(Exp *cond, Exp *left, Exp *right)
{
	Exp *e = NewExp(offsetofend(Exp,choose));
	e->type = E_CHOOSE;
	e->choose.e = cond;
	e->choose.left = left;
	e->choose.right = right;
	return e;
}

Exp *NewReturnExp(Exp *ex)
{
	Exp *e = NewExp(offsetofend(Exp,ret));
	e->type = E_RETURN;
	e->ret.e = ex;
	return e;
}

#else
Exp *NewConstExp(uint32 c);
Exp *NewRegExp(byte r);
Exp *NewMovExp(byte r, Exp *ee);
Exp *NewBinExp(byte s, Exp *l, Exp *r);
Exp *NewUnExp(byte s, Exp *l);
Exp *NewCallExp(ea_t a);
Exp *NewOtherExp(const ArmIns &i);
Exp *NewLoadExp(byte s, Exp *ea);
Exp *NewStoreExp(byte s, Exp *ea, Exp *v);
Exp *NewCondExp(Exp *ee);
Exp *NewChooseExp(Exp *cond, Exp *left, Exp *right);
Exp *NewReturnExp(Exp *ex);
#endif


struct Instr {
	uint16 uses,changes;
	Exp *e;
	ea_t addr; // orig address where this instruction appears
};

struct RegState {
	uint16 changed;
	uint16 known;
	uint32 values[13];
};

enum {
	LT_NONE, LT_ENDLESS,LT_PRE_TESTED,LT_POST_TESTED,
};

struct IntervalNode;

struct BasicBlock {
	ea_t base;		// base address of this basic block
	//ea_t end;			// end address of this basic block

	size_t ref;		// how many other basic blocks jump to this basic block
	size_t back_ref; // how many back references to this node?
	
	BasicBlock *interval;// which interval does this block belong to?

	uint order;			// DFS ordering

	uint uses;				// which registers are live on entry to this basic block?
	uint writes;			// which registers does this basic block assign to?
	uint liveout;    // which registers does this basic block need to output?
	uint uses2;				// which registers are used by this basic block?


#define num_instr instr.GetCount()
	LList<Instr> instr;

	BasicBlock *next; // linked list of basic blocks belonging to the same function...
	BasicBlock *flow, *cond; // next basic blocks in code sequence.

	// used for structuring loops
	BasicBlock *loop_head;
	BasicBlock *loop_latch;
	BasicBlock *loop_follow;
	IntervalNode *intervalnode; // used when computing intervals
	byte loop_type;
	bool in_loop; // temporary used for storing if a block is in the loop

	bool written; // has code for this basic block been written already?

	bool need_label;

	// used for structuring Ifs
	bool if_unresolved;
	byte if_mark;
	BasicBlock *immed_dom; // immediate dominator
	BasicBlock *if_follow; // which one ends the if?
	
	RegState rs;				// register state on entry to this basic block

	TypeId tid[16];			// type information in each register on entry

	int ord() { return (this?order:0); }
};

static inline bool IsTwoWay(BasicBlock *b)
{
	return b->cond != NULL;
}


enum {
	EE_BAS = 0, // output basic block
	EE_GOTO = 1,// output goto to a basic block that was already generated
	EE_IF = 2,  // if construct
	EE_WHILE = 3,// while loop
	EE_REPEAT = 4, // repeat loop
	EE_ENDLESS=5, // endless loop
	EE_RETURN=6,  // return
};

struct EmittedEnt {
	EmittedEnt *next;
	byte type;
	union {
		// used for EE_BAS and EE_GOTO
		struct {
			BasicBlock *bas;
		} bas;
		
		// used for if
		struct {
			bool negate;
			Exp *exp;
			EmittedEnt *left;
			EmittedEnt *right;
			BasicBlock *bas;
		} cond;

		// used for while & repeat
		struct {
			Exp *exp;
			EmittedEnt *body;
			BasicBlock *bas;
			bool negate;
		} loop;

		struct {
			Exp *e;
		} ret;
	};
	
	EmittedEnt(byte t) { type = t;  next = NULL;}
};

#ifdef WITH_CONSTRUCTORS

EmittedEnt *NewEmitBas(BasicBlock *bas)
{
	assert(bas);

	if (bas->num_instr == 0)
		return NULL;

	EmittedEnt *ee = new EmittedEnt(EE_BAS);
	ee->bas.bas = bas;
	return ee;
}

EmittedEnt *NewEmitSeq(EmittedEnt *a, EmittedEnt *b)
{
	if (a == NULL)
		return b;

	EmittedEnt *t = a;
	if (b) {
		while (a->next) a = a->next;
		a->next = b;
	}
	return t;
}

EmittedEnt *NewEmitIf(Exp *e, BasicBlock *bb)
{
	assert(e);
	EmittedEnt *ee = new EmittedEnt(EE_IF);
	ee->cond.negate = false;
	ee->cond.left = NULL;
	ee->cond.right = NULL;
	ee->cond.exp = e;
	ee->cond.bas = bb;
	return ee;
}

EmittedEnt *NewEmitLoop(BasicBlock *bb)
{
	EmittedEnt *ee = new EmittedEnt(bb->loop_type == LT_ENDLESS ? EE_ENDLESS : bb->loop_type == LT_POST_TESTED ? EE_REPEAT : EE_WHILE);
	ee->loop.body = NULL;
	ee->loop.bas = bb;
	ee->loop.exp = NULL;
	ee->loop.negate = false;
	return ee;
}

EmittedEnt *NewEmitReturn(Exp *e)
{
	EmittedEnt *ee = new EmittedEnt(EE_RETURN);
	ee->ret.e = e;
	return ee;
}
#endif


struct SwitchStatement;

class Analyzer {
	BasicBlock *_list;
	EmittedEnt *_ee;

	BasicBlock *GetBasblockAt(ea_t from);

	uint32 _function_base;

	uint32 _uses, _changes;
	BasicBlock *_bb;

	bool _returns;
	uint32 _callconv;
	int _framesize;

	TypeId _inittypes[16];

	// Instruction creation
	Exp *CreateOpExp(const ArmOp &o);
	Exp *CreateEffAddrExp(const ArmOp &o);
	void CreateInstruction(const ArmIns &ai, addr_t ea, BasicBlock *bb);

	void VisitUC(Exp *e);
	void CalcInstrFlags(Instr &i);
	void MkInstr(Instr &i, Exp *e, addr_t ea = 0);

	void DestroyBB(BasicBlock *bb);
	void DeleteEmptyBB(BasicBlock *bd);

	void SimplifyConstants(Exp **e);
	static Exp *SimplifyConstantsCallback(Exp *e, void *p);


	void ComputeRegisterState(BasicBlock *bb, RegState *rs, RegState *rs_cond);
	void PropagateInitialConsts(BasicBlock *bb);
	void ComputeUsesWrites(BasicBlock *bb);

	typedef Exp *ForEachCallback(Exp *, void *);

	bool TryReplaceWithConst(BasicBlock *bb, uint start, uint reg, uint32 value);
	bool TryReplaceWithExpr(BasicBlock *bb, uint start, uint reg, Exp *e, uint uses);

	void SimplifyBB(BasicBlock *bb);
	static void KillInstr(BasicBlock *bb, uint j);

	static bool IsConstantValue(Exp *e, uint32 &num);
	void ComputeUsesWrites();
	void ComputeRegisterState();

	void RemoveFunctionPrologueCode(BasicBlock *first, BasicBlock *last);

	void IdentifyLogicalAndOr();

	static bool IsCondBB(BasicBlock *bb, bool empty = false);
	static Exp *MakeLNot(Exp *e);


	void ComputeBBOrder();
	void ComputeImmediateDominators();

	// functions for finding loops
	void StructureLoops();
	void FindNodesInLoop(BasicBlock *head, BasicBlock *latch);
	BasicBlock *FindEndlessLoopFollow(BasicBlock *head, BasicBlock *latch);
	void ComputeIntervals();
	bool StepIntervals();

	// functions for finding ifs
	void StructureIfs();
	
	BasicBlock *NewBasicBlock();
	void RestructureWhile();
	BasicBlock *HasIfStatement(BasicBlock *a, BasicBlock *b);
	void DoRestructureWhile(BasicBlock *ifb, BasicBlock *whileb);
	bool IfsAreEqual(BasicBlock *ifb, BasicBlock *whileb);

	static bool EeReachesEnd(EmittedEnt *ee);
	static int EeDepth(EmittedEnt *ee);

	EmittedEnt *EmitCode(BasicBlock *bb, BasicBlock *stopper);
	EmittedEnt *EmitCode2(BasicBlock *bb, BasicBlock *stopper);

	void InsertReturnStatements(bool returns);
	bool ShouldBeMoved(Exp *e);

	int DetermineFunctionArgs(byte *p);
	byte CheckRegFuncPar(int r);

	void CheckAnteriorLineDirectives();
	void ParseAnteriorDirective(char *s);
	bool CreateSwitchConds(BasicBlock *bb, SwitchStatement *s);

	void PropagateTypes();
	void ComputeTypeState(BasicBlock *bb, TypeId tid[16]);

public:
	static void ForEachNode(Exp **ep, ForEachCallback *func, uint mask, void *param);

	void Init();

	bool AnalyzeOwn(ea_t start, ea_t end);
	EmittedEnt *GenerateCode();
	void Run();
	void Dump();
	void Dump2();
	void Free();

	void Validate(const char *x);
};

// Function definitions
Exp *GetIfExp(BasicBlock *bb);

//Exp *IsAddMul(Exp *e, uint32 &add, uint32 &mul, uint *depth = NULL);
bool IsReturn(BasicBlock *bb);

void printbb(BasicBlock *bb);
void printexp(Exp *e);


struct AddMulStruct {
	uint32 add,mul;
	bool normal;
};

Exp *IsAddMul(Exp *e, AddMulStruct &ams);
void TrySimplifyStore(Exp *&value, Exp *ea, byte &type, byte &oper);
TypeId GetTypeOf(Exp *e, TypeId regs[16]);
tid_t GetTidForType(TypeId id);
size_t GetSizeOfStruct(TypeId id);

// External variables
extern LList<byte *> lines;
