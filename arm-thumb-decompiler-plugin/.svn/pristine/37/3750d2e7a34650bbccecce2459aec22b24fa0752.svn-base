#include <ida.hpp>
#include <idp.hpp>

#include "default.h"
#include "insn.h"
#include "exp.h"

bool Analyzer::IsCondBB(BasicBlock *bb, bool empty)
{
	// if empty flag is set, it's a sequence of ifs.
	// then it must have exactly one jump to it.
	if (empty) {
		if (bb->num_instr != 1 || bb->ref != 1) return false;
	}

	// flow jumps to itself..??
	if (bb == bb->flow) return false;

	// if cond field is set, it's a conditional
	return bb->num_instr != 0 && bb->instr[bb->num_instr-1].e->type == E_COND && bb->cond != NULL;
}

Exp *Analyzer::MakeLNot(Exp *e)
{
	// TODO: make this more advanced
	return NewUnExp(E_LNOT, e);	
}

static bool QualifiesForChoose(Exp *e)
{
	return e->type == E_CONST || e->type == E_REG;
}

// NOTE: This function doesn't update uses/changes of Instr
void Analyzer::IdentifyLogicalAndOr()
{
	BasicBlock *bb;

restart:
	for(bb = _list; bb; bb = bb->next) {
		if (!IsCondBB(bb) || !IsCondBB(bb->flow, true)) continue;
		BasicBlock *next = bb->flow;
		if (bb->cond == next->cond || bb->cond == next->flow) {		

			// combine the expressions.
			Instr &ie = bb->instr[bb->num_instr-1];
			Instr &in = next->instr[next->num_instr-1];
			assert(ie.e->type == E_COND && in.e->type == E_COND);

			// for AND, repoint the destination and negate the operand
			if (bb->cond == next->flow) {
				bb->cond->ref--;
				next->cond->ref++;
				bb->cond = next->cond;
				ie.e->cond.e = NewBinExp(E_LAND, MakeLNot(ie.e->cond.e), in.e->cond.e);
			} else {
				ie.e->cond.e = NewBinExp(E_LOR, ie.e->cond.e, in.e->cond.e);
			}
			
			// update uses register
			ie.uses |= in.uses;

			// actually delete the 2nd if statement
			bb->flow = next->flow;
			next->cond->ref--;	
			DestroyBB(next);

			goto restart;
		} else
			continue;
	}

restart2:

	for(bb = _list; bb; bb = bb->next) {

	// identify things suitable for the choose operator
	// R1 = 0
	// if EXPRESSION goto LBL
	//   R1 = 1
	// LBL:
		if (bb->flow && bb->cond && bb->flow->ref == 1 && 
				bb->flow->flow == bb->cond && bb->flow->num_instr == 1 && 
				!bb->flow->cond && bb->num_instr >= 2) {
			Instr &i = bb->instr[bb->num_instr-2]; // this must be a assign to register
			Instr &j = bb->flow->instr[0];
			if (i.e->type == E_MOV && 
					j.e->type == E_MOV && 
					i.e->mov.reg == j.e->mov.reg && QualifiesForChoose(i.e->mov.e)) {
				
				// change the first assignment into a choose operation
				i.e->mov.e = NewChooseExp(GetIfExp(bb), i.e->mov.e, j.e->mov.e);

				// delete the IF instruction
				KillInstr(bb, bb->num_instr - 1);
				bb->cond->ref--;
				bb->cond=NULL;
				
				// unlink the basic block
				BasicBlock *deleted =bb->flow;
				bb->flow = bb->flow->flow;
				DestroyBB(deleted);

				goto restart2;
			}
		}

		// second case of choose operator stuff
		// if EXP goto SKIP
		//   R1 = 0
		//   goto END
		// SKIP:
		//   R1 = 1
		// END:

		if (bb->flow && bb->cond && bb->flow->ref == 1 && bb->cond->ref == 1 && bb->flow->num_instr == 1 && bb->cond->num_instr == 1 && !bb->flow->cond && !bb->cond->cond && bb->flow->flow == bb->cond->flow) {
			Instr &i = bb->cond->instr[0];
			Instr &j = bb->flow->instr[0];
			
			if (i.e->type == E_MOV && 
					j.e->type == E_MOV && 
					i.e->mov.reg == j.e->mov.reg) {
				
				// change the IF instruction into a Choose instruction
				bb->instr[bb->num_instr-1].e = NewMovExp(i.e->mov.reg, NewChooseExp(GetIfExp(bb), i.e->mov.e, j.e->mov.e));
				
				BasicBlock *end = bb->flow->flow;

				// delete basicblocks that aren't used anymore
				DestroyBB(bb->flow);
				DestroyBB(bb->cond);

				// repoint the if block to point to END
				bb->cond = NULL;
				bb->flow = end;
				
				// now one less references this
				if (end) end->ref--;
				
				// need to restart search
				goto restart2;
			}
		}
	}
}

struct Stack {
	int n;
	BasicBlock *bb[1];
};

static void DoComputeOrder(BasicBlock *bb, Stack *s)
{
	int sn = s->n;

	bb->order = 1;
	if (bb->flow) {
		bb->flow->order |= (bb->flow->order & 1)<<1;
		if (bb->flow->order == 0) {
			DoComputeOrder(bb->flow, s);			
			// need redo?
			if (bb->order & 2) {
				while (s->n > sn) s->bb[--s->n]->order = 0;
				sn = -1;
			}
		}
	}

	if (bb->cond) {
		bb->cond->order |= (bb->cond->order & 1)<<1;
		if (bb->cond->order == 0)
			DoComputeOrder(bb->cond, s);
	}

	// need redo?
	if (sn<0) {
		bb->flow->order |= (bb->flow->order & 1)<<1;
		if (bb->flow->order == 0)
			DoComputeOrder(bb->flow, s);
	}

	bb->order = 4;
	s->bb[s->n++] = bb;
}

void Analyzer::ComputeBBOrder()
{
	uint count = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) { count++; bb->order = 0;}
	Stack *s = (Stack*)alloca(sizeof(Stack) + count * sizeof(BasicBlock*));
	s->n = 0;
	DoComputeOrder(_list, s);
//	assert(s->n == count);

	for(uint n=0,r=s->n;r;) s->bb[--r]->order = ++n;
}


struct IntervalNode {
	BasicBlock *head;				// which basic block is the head of the node?
	IntervalNode *interval; // which interval does this node belong to?
	bool in_h,tmp;					// temporary variables needed to compute intervals
	uint16 num_out;					// number of outgoing edges
	IntervalNode **out;			// list of outgoing edges
};

static void ComputeIntervals(IntervalNode *nodes, size_t count)
{
	nodes->in_h = true;

	for(;;) {
		IntervalNode *n;

		// find an unprocessed node n <- h
		for(size_t i=0; ; i++) {
			if (i == count) return;
			n = nodes + i;
			if (n->interval == NULL && n->in_h) break;
		}

		n->interval = n;

		// repeat I(n) := I(n) + [m <- G | All p=immedPred(m), p <- I(n)]
		bool changes;
		do {
			changes = false;

			// compute interval_tmp flag. it's FALSE if all predecessors are in the interval
			for(size_t i=0; i!=count; i++) {
				IntervalNode *bb = nodes + i;
				if (bb->interval != n) {
					for(size_t j=0; j!=bb->num_out; j++)
						bb->out[j]->tmp = true;
				}
			}
			for(size_t i=0; i!=count; i++) {
				IntervalNode *bb = nodes + i;
				if (!bb->tmp && bb->interval == NULL) {
					// add bb to the interval if it's not currently in one.
					bb->interval = n;
					changes = true;
				}
				bb->tmp = false;
			}
		} while (changes);

		// H := H + [m <- G | m <-/ H && m <-/ I(n) && Exist p = immedPred(m), p <- I(n)]
		for(size_t i=0; i!=count; i++) {
			IntervalNode *bb = nodes + i;
			if (bb->interval == n) {
				for(size_t j=0; j!=bb->num_out; j++) {
					if (bb->out[j]->interval == NULL)
						bb->out[j]->in_h = true;
				}
			}
		}
	}
}

bool IsBB(BasicBlock *list, BasicBlock *bb)
{
	for(;list;list=list->next)
		if (list == bb) return true;
	return false;
}

// intervals are 1-based
void Analyzer::ComputeIntervals()
{
	size_t count = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) { count++; }

	// allocate space for nodes
	IntervalNode *nodes = StackAlloc(IntervalNode, count);
	memset(nodes, 0, sizeof(IntervalNode) * count);

	// setup interval ptrs
	count = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		bb->intervalnode = &nodes[count];
		nodes[count].head = bb;
		count++;

//		if (bb->flow && !IsBB(_list, bb->flow)) msg("Link %x->%x points bad\n", bb->base, bb->flow->base);
//		if (bb->cond && !IsBB(_list, bb->cond))	msg("Link %x->%x points bad\n", bb->base, bb->cond->base);
	}

	// point links
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		IntervalNode *n = bb->intervalnode;
		n->out = StackAlloc(IntervalNode*,2);
		if (bb->flow) { n->out[n->num_out++] = bb->flow->intervalnode; assert(bb->flow->intervalnode); }
		if (bb->cond) { n->out[n->num_out++] = bb->cond->intervalnode; assert(bb->cond->intervalnode); }
	}

	// compute intervals
	::ComputeIntervals(nodes, count);

	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		IntervalNode *n = bb->intervalnode;
		bb->interval = n->interval->head;
	}
}

static void AddToIntervalNode(IntervalNode *dst, IntervalNode *src)
{
	for(size_t i=0; i!=dst->num_out; i++)
		if (dst->out[i] == src) return;
	dst->out[dst->num_out++] = src;
}

// from each old interval, make a new node, and run the interval analysis on that.
bool Analyzer::StepIntervals()
{
	size_t count = 0, i;
	for(BasicBlock *bb = _list; bb; bb = bb->next)
		if (bb->interval == bb)
			count++;

	// allocate space for nodes
	IntervalNode *nodes = StackAlloc(IntervalNode, count);
	memset(nodes, 0, sizeof(IntervalNode) * count);

	// setup interval ptrs
	i = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (bb->interval == bb) {
			IntervalNode *in = &nodes[i];
			bb->intervalnode = in;
			in->head = bb;
			i++;
			in->out = StackAlloc(IntervalNode*, count); // upper space bound!
		}
	}

	// compute the edges for each interval
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		IntervalNode *in = bb->interval->intervalnode;

		// jumping out of the interval? then add to the interval node.
		if (bb->flow && bb->flow->interval != bb->interval)
			AddToIntervalNode(in, bb->flow->interval->intervalnode);

		if (bb->cond && bb->cond->interval != bb->interval)
			AddToIntervalNode(in, bb->cond->interval->intervalnode);
	}

	// compute intervals
	::ComputeIntervals(nodes, count);

	// propagate interval info to basic block
	size_t count2 = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		IntervalNode *n = bb->interval->intervalnode;
		bb->interval = n->interval->head;
		if (bb->interval == bb)
			count2++;
	}

	// check if the new interval graph is smaller than the old one.
	assert(count2 <= count);
	return count2 < count;
}

BasicBlock *Analyzer::FindEndlessLoopFollow(BasicBlock *head, BasicBlock *latch)
{
	BasicBlock *fol = NULL, *t;
	uint min = 0x7fffffff;
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (bb->in_loop) {
			if ((t=bb->flow) && !t->in_loop && t->order < min) { min = t->order; fol = t; }
			if ((t=bb->cond) && !t->in_loop && t->order < min) { min = t->order; fol = t; }
		}
	}
	return fol;
}

void Analyzer::FindNodesInLoop(BasicBlock *head, BasicBlock *latch)
{
	head->loop_head = head;
	latch->loop_head = head;

	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		bb->in_loop = false;

		if (bb->interval == head && bb->order > head->order && bb->order < latch->order) {
			// for all nodes in the interval that are between the head and latching node
			// mark it as being in the loop
			if (bb->loop_head == NULL) bb->loop_head = head;
			bb->in_loop = true;			
		}
	}
	head->in_loop = true;
	latch->in_loop = true;

	// determine the type of loop and the follow field
	if (IsTwoWay(latch)) {
		// 2-way latching node
		if (IsTwoWay(head) && head->num_instr==1) {
//			if (head == latch || head->flow->in_loop && head->cond->in_loop || 1) {
				head->loop_type = LT_POST_TESTED;
				head->loop_follow = (latch->flow->in_loop) ? latch->cond : latch->flow;
//			} else {
//				head->loop_type = LT_PRE_TESTED;
//				head->loop_follow = (head->flow->in_loop) ? head->cond : head->flow;
//			}
		} else {
			head->loop_type = LT_POST_TESTED;
			head->loop_follow = (latch->flow->in_loop) ? latch->cond : latch->flow;
		}
	} else {
		// 1-way latching node
		if (IsTwoWay(head) && head->num_instr==1) {
			head->loop_type = LT_PRE_TESTED;
			head->loop_follow = (head->flow->in_loop) ? head->cond : head->flow;
		} else {
			head->loop_type = LT_ENDLESS;
			head->loop_follow = FindEndlessLoopFollow(head, latch);
		}
	}
}

static inline bool HasBackEdge(BasicBlock *from, BasicBlock *to)
{
	return from->order >= to->order && (from->flow == to || from->cond == to);
}

void Analyzer::StructureLoops()
{
	ComputeIntervals();
	do {
//		msg("---\n");
//		for(BasicBlock *bb = _list; bb; bb = bb->next)
//			msg("%2d - %d\n", bb->ord(), bb->interval->ord());

		// for each interval in G
		for(BasicBlock *bb = _list; bb; bb = bb->next) if (bb->interval == bb) {
			// find greatest enclosing back edge.
			BasicBlock *latch = NULL;
			for(BasicBlock *bl = _list; bl; bl = bl->next) {
				// member of the interval with a back edge?
				if (bl->interval == bb && HasBackEdge(bl,bb)) {
					bb->back_ref++;
					if ((latch == NULL || bl->order > latch->order) && bl->loop_head == NULL) latch = bl;
				}
			}

//			msg("%2d : %d\n", bb->ord(), latch->ord());

				if (latch) {
				bb->loop_latch = latch;
				FindNodesInLoop(bb, latch);
			}
			// next interval
		}
		// compute new set of intervals for the combined graph
	} while (StepIntervals());
}


static BasicBlock *CommonDom(BasicBlock *curr, BasicBlock *pred)
{
	if (curr == NULL) return pred;
	if (pred == NULL) return curr;

	while (curr != NULL && pred != NULL && curr != pred) {
		if (curr->order < pred->order)
			pred = pred->immed_dom;
		else
			curr = curr->immed_dom;
	}
	return curr;
}

void Analyzer::ComputeImmediateDominators()
{
	// count number of basic blocks
	size_t count = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) { count++; }

	for(size_t cur_order = 1; cur_order <= count; cur_order++) {
		
		for(BasicBlock *bb = _list; bb; bb = bb->next) {
			if (bb->order >= cur_order)
				continue;

			if (bb->flow && bb->flow->order == cur_order) {
				// in edge from bb to bb->flow	
				bb->flow->immed_dom = CommonDom(bb->flow->immed_dom, bb);
			}

			if (bb->cond && bb->cond->order == cur_order) {
				// in edge from bb to bb->cond
				bb->cond->immed_dom = CommonDom(bb->cond->immed_dom, bb);
			}
		}
	}
}

static void MarkFollow(BasicBlock *bb, byte mark)
{
	if (bb->if_mark&mark) return;
	bb->if_mark|=mark;

	if (bb->flow && bb->flow->order > bb->order) MarkFollow(bb->flow,mark);
	if (bb->cond && bb->cond->order > bb->order) MarkFollow(bb->cond,mark);
}

static BasicBlock *FindFollow(BasicBlock *bb)
{
	BasicBlock *found = NULL;

	for(;bb;bb=bb->next) {
		if (bb->if_mark == 3) {
			if (found == NULL || bb->order < found->order)
				found = bb;
		}
		bb->if_mark = 0;
	}
	return found;
}

void Analyzer::StructureIfs()
{
	// make a list of the basic blocks ordered by the DFS order
	uint count = 0;
	for(BasicBlock *bb = _list; bb; bb = bb->next) { count++; }
	BasicBlock **bblist = StackAlloc(BasicBlock *, count);
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (bb->order == 0) {
			msg("%x: Function is not connected (%x). Can't analyze ifs\n", _list->base, bb->base);
			return;
		}
		assert(bb->order > 0 && bb->order <= count);
		bblist[bb->order-1] = bb;
	}

	bool unresolved = false;

	// visit them highest number first
	for(int i=count; --i>=0; ) {
		BasicBlock *bb = bblist[i];

		if (IsTwoWay(bb) && (bb->loop_type != LT_PRE_TESTED)) {
			int edges = 2;
			BasicBlock *follow = NULL;

			if (bb->flow->flow == bb->cond && !bb->flow->cond) {
				follow = bb->cond;
			} else if (bb->cond->flow == bb->flow && !bb->cond->cond) {
				follow = bb->flow;
			} else {
				MarkFollow(bb->flow,1);
				MarkFollow(bb->cond,2);
				follow = FindFollow(_list);
			}

			if (follow) {
				bb->if_follow = follow;
				
				// if we have unresolved nodes, mark them appropriately
				if (unresolved) {
					unresolved = false;
					for(BasicBlock *bb = _list; bb; bb = bb->next) {
						if (bb->if_unresolved) {
							bb->if_unresolved = false;
							if (bb == follow) {

							} else {
//								bb->if_follow = follow;
//								msg("Resolving %d to %d\n", bb->order, follow->order);
							}
						}
					}
				}
			} else {
				bb->if_unresolved = true;
				unresolved = true;
			}
		}
	}
}


void Analyzer::InsertReturnStatements(bool returns)
{
	ComputeBBOrder();

	//msg("returns = %08X\n",returns);
	//msg("_list = %08X\n",&_list);

	for(BasicBlock *bb = _list; bb; bb=bb->next) 
	{
		//msg("bb->base = %08X\n",bb->base);
		//msg("bb->cond = %08X\n",bb->cond);
		//msg("&bb->flow = %08X\n",&bb->flow);
		//msg("bb->flow = %08X\n",bb->flow);
		//msg("bb->num_instr = %08X\n",bb->num_instr);
		//for(int j=0; j<bb->num_instr; j++)
		//{
		//	msg("bb->instr[%d] = %08X\n",j,bb->instr[j]);
		//	msg("bb->instr[%d].e = %08X\n",j,bb->instr[j].e);
		//	msg("bb->instr[%d].e->type = %08X\n",j,bb->instr[j].e->type);
		//}
		if (!bb->flow || (returns && bb->cond == NULL) && IsReturn(bb->flow))
		{
			msg("got here\n");
			assert(!bb->cond);

			Instr &i = bb->instr.Append();
			i.addr = 0;
			i.changes = 0;
			if (returns) {
				i.e = NewReturnExp(NewRegExp(0));
				i.uses = 1<<0;
			} else {
				i.e = NewReturnExp(NULL);
				i.uses = 0;
			}

			if (bb->flow) {
				if (!--bb->flow->ref) {
					DestroyBB(bb->flow);
				}
				bb->flow = NULL;
			}
		}
	}	
}

// convert
// B
// if (A) {
//    do {
//      C
//      D
//    } while(A);
// }
// into
// B
// while(A) {
//   C
//   D
// }


// check if there is an if statement
// that jumps to both a and b,
// and that jumps forward to a.
BasicBlock *Analyzer::HasIfStatement(BasicBlock *a, BasicBlock *b)
{
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		if (bb->order < a->order &&
				bb->cond && bb->flow &&
				(bb->cond == a && bb->flow == b ||
				 bb->flow == a && bb->cond == b)
			) return bb;
	}

	return NULL;
}

void Analyzer::DoRestructureWhile(BasicBlock *ifb, BasicBlock *whileb)
{
	if (ifb->cond != whileb->cond) { swap(ifb->cond, ifb->flow); }

	// delink the while block
	whileb->flow->ref--;
	whileb->cond->ref--;
	whileb->cond = NULL;
	whileb->flow = NULL;

	// replace the conditional instruction in the IF with the one from the while
	// and kill the conditional instruction in the while
	ifb->instr[ifb->num_instr-1] = whileb->instr[whileb->num_instr - 1];
	whileb->instr.SetCount(whileb->num_instr - 1);

	// make sure the head if statement is alone in the bb
	if (ifb->num_instr != 1) {
		BasicBlock *n = NewBasicBlock();

		// move the last instruction
		n->instr.Append(ifb->instr[ifb->num_instr-1]);
		ifb->instr.SetCount(ifb->num_instr - 1);

		n->cond = ifb->cond;
		n->flow = ifb->flow;

		ifb->cond = NULL;
		ifb->flow = n;
		n->ref = 1;

		ifb = n;
	}

	// setup while block to point to the if
	whileb->flow = ifb;
	ifb->ref++;

	// check if the while block became empty, if it did become empty, delete it
	if (whileb->num_instr == 0)
		DeleteEmptyBB(whileb);
}

static inline bool IsCommutative(byte sb)
{
	return sb == E_AND || sb == E_EOR || sb == E_ORR || sb == E_MUL || sb == E_ADD;
}

// rs contains the known values in expr a
static bool CompareExp(Exp *a, Exp *b, RegState *rs = NULL)
{
	if (a->type != b->type) {
		if (rs && a->type == E_REG && b->type == E_CONST && 
			HASBIT(rs->known, a->reg) && b->num == rs->values[a->reg])
				return true;
		return false;
	}
	switch(a->type) {
	case E_CONST:
		return a->num == b->num;
	case E_REG:
		return a->reg == b->reg;
	case E_BIN:
		if (a->bin.subtype != b->bin.subtype) {
			return false;
		}
		
		if (CompareExp(a->bin.left, b->bin.left,rs) && CompareExp(a->bin.right, b->bin.right,rs))
			return true;

		if (IsCommutative(a->bin.subtype) &&
				CompareExp(a->bin.left, b->bin.right,rs) && CompareExp(a->bin.right, b->bin.left	,rs))
			return true;

		return false;
	case E_UN:
		return a->un.subtype == b->un.subtype && CompareExp(a->un.left, b->un.left,rs);
	case E_LOAD:
		return a->load.subtype == b->load.subtype && CompareExp(a->load.ea, b->load.ea);
	default:
		return false;
	}
}



static int ConvertTypeToStoreType(int type)
{
	if (type == T_I8 || type == T_I16) type^=T_I8^T_U8;
	return type;
}

bool IsLoadOfType(Exp *load, Exp *ea, byte type)
{
	// make sure that it's a load and that the type matches
	if (load->type != E_LOAD || ConvertTypeToStoreType(load->load.subtype) != type)
		return false;

	// make sure effective address is equal
	if (!CompareExp(load->load.ea, ea))
		return false;

	return true;
}

// simplify a store operation into a +=
void TrySimplifyStore(Exp *&value, Exp *ea, byte &type, byte &oper)
{
	Exp *v = value;
	Exp *load;

	// must be a binary operator
	if (v->type != E_BIN)
		return;

	if (IsLoadOfType(load=v->bin.left, ea, type) || 
			(IsCommutative(v->bin.subtype) && IsLoadOfType(load=v->bin.right, ea, type))) {
		// good to go!
		oper = v->bin.subtype;
		type = load->load.subtype;
		value = load == v->bin.left ? v->bin.right : v->bin.left;
	}
}


bool Analyzer::IfsAreEqual(BasicBlock *ifb, BasicBlock *whileb)
{
	RegState rs;
	ComputeRegisterState(ifb, &rs, NULL);
	
	Exp *a = GetIfExp(ifb);

	// need to negate the if before checking for equality?
	bool negated = false;
	if (ifb->cond != whileb->cond) {
		if (a->type != E_BIN || a->bin.subtype < E_COMP_EQ || a->bin.subtype > E_COMP_LE) return false;
		a->bin.subtype = ((a->bin.subtype - E_COMP_EQ) ^ 1) + E_COMP_EQ;
		negated = true;
	}
	
	bool r = CompareExp(GetIfExp(whileb), a, &rs);

	// restore negation
	if (negated) a->bin.subtype = ((a->bin.subtype - E_COMP_EQ) ^ 1) + E_COMP_EQ;

	return r;
}


void Analyzer::RestructureWhile()
{
restart:
	for(BasicBlock *bb = _list; bb; bb = bb->next) {
		// must be a two way node
		if (!(bb->flow && bb->cond))
			continue;

		// must have a back jump, the destination
		// of the back jump must have exactly 2 refs.
		if (bb->flow->order <= bb->order && bb->flow->ref == 2) {
			BasicBlock *ifb = HasIfStatement(bb->flow, bb->cond);
			if (ifb && IfsAreEqual(ifb, bb)) {
				DoRestructureWhile(ifb, bb);
				ComputeBBOrder();
				goto restart;
			}
		} 
		
		if (bb->cond->order <= bb->order && bb->cond->ref == 2) {
			BasicBlock *ifb = HasIfStatement(bb->cond, bb->flow);
			if (ifb && IfsAreEqual(ifb, bb)) {
				DoRestructureWhile(ifb, bb);
				ComputeBBOrder();
				goto restart;
			}
		}
	}
}

