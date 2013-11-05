// xgill_file.cc        see license.txt for copyright and terms of use
// translation hooks and entry points for xgill frontend.

#include <cc_ast.h>
#include <cc_env.h>
#include <cc_elaborate.h>
#include <cc_flags.h>
#include <backend/backend_compound.h>
#include <imlang/block.h>
#include <imlang/storage.h>

using Xgill::PPoint;
using Xgill::Transaction;
using Xgill::TOperand;
using Xgill::TOperandString;
using Xgill::TOperandBoolean;
using Xgill::TOperandVariable;
using Xgill::TOperandList;
using Xgill::TAction;
using Xgill::TActionTest;

/*
/////////////////////////////////////

minor easily forgettable TODO items

- T_POINTERTOMEMBER type info
- wide char strings
- destructor in declarations for for-loop and condition declarations
- static initializers for function variables

Elsa issues

- dropped member inits for anonymous union members
- fields with no associated compound type

////////////////////////////////////
*/

// function to call when we hit unexpected data but are able to recover.
// this is (almost) always preferable to having an assert failure.
inline void ProcessFailure(const char *msg)
{
  cout << "WARNING: Translation unexpected data: " << msg << endl;
}

// fixed byte width we use for pointers. we check that this is consistent 
// with what Elsa is producing.
#define POINTER_WIDTH Xgill::Type::PointerWidth()
#define POINTER_BITS (Xgill::Type::PointerWidth() * 8)

// get the bit width and sign of a type, if possible.
void GetTypeBits(Type *type, size_t *bits, bool *sign);

// sometimes static initializer lists are huge, e.g. > 100000 entries.
// use a cutoff for these and only process the first N inits.
#define INITIALIZER_CUTOFF  5000

// environment for processing an Expression and its contents.
struct ExprEnv
{
  // point to hang side effects which execute before this expression
  // (and all its outer expressions). when a new side effect edge is added
  // its source should be this point, its target should be a new point,
  // and this point should be updated to that new target point.
  PPoint *pre_point;

  // whether the result of this expression should branch to true_point
  // or false_point below. after the ProcessExpression, there will be paths
  // from the initial value of *pre_point to true_point and false_point.
  bool result_branch;

  // point to jump to if this expression evaluates to true/false.
  // only used if result_branch is true.
  PPoint true_point;
  PPoint false_point;

  void SetResultBranch(PPoint _true_point, PPoint _false_point)
  {
    result_branch = true;
    true_point = _true_point;
    false_point = _false_point;
  }

  // lvalue to assign the value of this expression to, NULL if there is none.
  // ProcessExpression consumes a reference on this lvalue.
  Xgill::Exp *result_assign;

  // type of result_assign. only used if result_assign != NULL.
  // cannot have reference type.
  Type *result_assign_type;

  // the assignment will store the address of the rhs, not the rhs itself.
  // if this has reference type then the address of the rhs will be taken
  // and assigned to the lhs.
  bool result_assign_address;

  // operand used for the result assignment, only if if result_assign != NULL.
  BinaryOp result_assign_op;

  void SetResultAssign(Xgill::Exp *assign, Type *assign_type,
                       bool assign_address = false,
                       BinaryOp assign_op = BIN_ASSIGN)
  {
    assign->MoveRef(NULL, this);
    result_assign = assign;
    result_assign_type = assign_type;
    result_assign_address = assign_address;
    result_assign_op = assign_op;
  }

  // pointer to receive the lvalue result of the expression. NULL if the
  // expression will not be used as an lvalue. if the expression has reference
  // type an implicit Drf() will be added to the lvalue.
  Xgill::Exp **result_lval;

  // pointer to receive the rvalue result of the expression. NULL if the
  // expression will not be used as an rvalue. if the expression has reference
  // type an implicit Drf() will be added to the value's lvalue.
  Xgill::Exp **result_rval;

  // bits/sign expected for result_rval. this may be different than the
  // bits/sign for the type of the expression itself if there is an implicit
  // coercion needed. only used if result_rval != NULL.
  size_t result_rval_bits;
  bool result_rval_sign;

  // at most one use of the result (branch/assign/lval/rval) can be set.
  // if none are set the result is discarded.
  // TODO: this design drops bare expressions like '{ ...; *x; ... }'. fix?

  // for E_constructor, specifies the instance object to use, NULL to get
  // object from the constructor info. ProcessExpression consumes a reference
  // on this lvalue.
  Xgill::Exp *ctor_instance_lval;

  // whether the result is used in any fashion.
  bool IsResultUsed() const
  {
    return result_branch || result_assign != NULL
        || result_lval != NULL || result_rval != NULL;
  }

  // whether the address of the result is needed.
  bool ResultAddressNeeded() const
  {
    return result_lval || (result_assign && result_assign_address);
  }

  // fill in the bits/sign needed for the result rvalue from type.
  void SetResultType(Type *type)
  {
    if (type) {
      type = type->asRval();
      GetTypeBits(type, &result_rval_bits, &result_rval_sign);
    }
  }

  ExprEnv(PPoint *_pre_point)
    : pre_point(_pre_point),
      result_branch(false), true_point(0), false_point(0),
      result_assign(NULL), result_assign_type(NULL),
      result_assign_address(false), result_assign_op(NUM_BINARYOPS),
      result_lval(NULL), result_rval(NULL),
      result_rval_bits(0), result_rval_sign(true),
      ctor_instance_lval(NULL)
  {}
};

// environment for a local scope and its declarations.
struct ScopeEnv
{
  // statement for which this is the scope.
  Statement *stmt;

  // destructors which must be called upon exiting the scope,
  // in the order in to call them.
  Xgill::Vector<Statement*> destructors;

  // all case and default label statements encountered in 
  Xgill::Vector<Statement*> case_labels;

  // point for break/continue statements to jump to. zero if this is not
  // a scope for a switch or loop body.
  PPoint break_point;
  PPoint continue_point;

  // if non-NULL, this is a scope for a switch statement, and switch_value
  // is the value being switched on.
  Xgill::Exp *switch_value;

  // if non-NULL, this is a scope for a switch statement, and *switch_point
  // indicates the current frontier of the tests generated for the inner
  // case labels.
  PPoint *switch_point;

  // if non-NULL, this is a scope for a switch statement, and *default_point
  // receives the point where the 'default' label is at, if there is any.
  // *default_point starts out a zero when the switch is first processed.
  PPoint *default_point;

  ScopeEnv()
    : stmt(NULL), break_point(0), continue_point(0),
      switch_value(NULL), switch_point(NULL), default_point(NULL)
  {}
};

// data for a label in a Function body.
struct LabelData
{
  // statement for this label.
  S_label *label;

  // point to jump to on a goto for this label.
  PPoint point;

  // statements which this point is nested in.
  Xgill::Vector<Statement*> stmt_list;

  LabelData() : label(NULL), point(0) {}
};

// table indexing the local variables of a function by the variables which
// share that name. if the same name has multiple references, the names
// will be uniqued to avoid collision.
typedef Xgill::HashTable< StringRef, Variable*,
                          Xgill::DataHash<StringRef> > LocalVariableTable;

// environment for processing a Function and its contents.
struct BlockEnv
{
  // base environment for the entire C++ translation.
  Env &base_env;

  // the function a CFG is being generated for. NULL if the CFG is for
  // an initializer.
  Function *func;

  // the variable a static initializer is being generated for. NULL if the
  // CFG is for a function.
  Variable *init;

  // table for all local variables in the environment.
  LocalVariableTable local_table;

  // the CFG this environment is generating points/edges for.
  Xgill::BlockCFG *cfg;

  // number of temporaries generated for this CFG.
  size_t temp_count;

  // scopes enclosing the current analyzed point, outermost scopes first.
  Xgill::Vector<ScopeEnv> scopes;

  // all labels in the source function.
  Xgill::Vector<LabelData> labels;

  BlockEnv(Env &_base_env)
    : base_env(_base_env), func(NULL), init(NULL), cfg(NULL), temp_count(0)
  {}

  // get the ID to use for non-global variables in this environment.
  Xgill::BlockId* GetVariableId()
  {
    Assert(cfg);
    Xgill::BlockId *base_id = cfg->GetId();
    if (base_id->Kind() == Xgill::B_Initializer) {
      base_id->IncRef();
      return base_id;
    }
    else {
      // get the B_Function version of the variable.
      Xgill::Variable *function = base_id->BaseVar();
      function->IncRef();
      return Xgill::BlockId::Make(Xgill::B_Function, function);
    }
  }
};

// active block environment, if there is one.
extern BlockEnv *benv;

// add a skip edge from entry_point to exit_point in env's CFG.
inline void AddSkipEdge(PPoint entry_point, PPoint exit_point)
{
  Xgill::PEdge *skip_edge = Xgill::PEdge::MakeSkip(entry_point, exit_point);
  benv->cfg->AddEdge(skip_edge);
}

// get a file/line location for the specified source location.
Xgill::Location* GetLocation(SourceLoc loc);

// whether to treat a particular variable as having global scope.
// this is any variable with VK_Glob or VK_Func kind, except for static local
// variables of a function (test for DF_STATIC for these).
inline bool IsGlobalVariable(Variable *var)
{
  // this is different from just the DF_GLOBAL flag from Elsa.
  // DF_GLOBAL within Elsa just means a top-level declaration, not a
  // variable that actually has global scope.

  if (var->hasFlag(DF_GLOBAL))
    return true;

  if (!var->hasAnyFlags(DF_MEMBER | DF_BITFIELD) && (!benv || !benv->func))
    return true;

  if (var->type->isFunctionType())
    return true;

  if (var->getScopeKind() == SK_NAMESPACE)
    return true;

  return false;
}

// get a variable from an Elsa variable. the name is a backup in cases
// where the variable itself is NULL (an unknown variable was accessed).
Xgill::Variable* GetVariable(Variable *var,
                             PQName *name = NULL);

// get a type from an Elsa type.
Xgill::Type* GetType(Type *type);

// make a dummy prototype: int foo()
inline Xgill::TypeFunction* GetErrorFunctionType()
{
  Xgill::Type *return_type = Xgill::Type::MakeInt(POINTER_WIDTH, true);
  Xgill::Vector<Xgill::Type*> arguments;
  return Xgill::Type::MakeFunction(return_type, NULL, false, arguments);
}

// for cases where we get confused (probably because of earlier
// parse/check errors) or can't generate the right output code.
Xgill::Field* MakeErrorField(PQName *name);

// get a field from an Elsa field variable. the name is a backup in cases
// where the field variable is NULL (an unknown field was accessed).
Xgill::Field* GetVariableField(Variable *field,
                               PQName *name = NULL);

// get a unique temporary of the specified type.
Xgill::Exp* GetNewTemporary(Xgill::Type *type);

// get an lvalue for a direct call to the specified function.
Xgill::Exp* GetFunctionLval(const char *function);

// insert a call to the specified allocation function at *pre_point,
// of the form 'ret_lval = function_name(size_arg)'
void DoAllocateCall(Xgill::Location *loc, PPoint *pre_point,
                    const char *function_name,
                    Xgill::Exp *ret_lval, Xgill::Exp *size_arg);

// insert a call to the specified free function at *pre_point,
// of the form 'function_name(base_arg)'
void DoFreeCall(Xgill::Location *loc,
                PPoint *pre_point, const char *function_name,
                Xgill::Exp *base_arg);

// fills in env with data from a scope stmt. scans the statement for outer
// labels and declarations with destructors.
void InitializeScope(ScopeEnv &scope_env, Statement *stmt);

// generate edges for any destructors called on exit from the specified scope.
void ProcessExitScope(const ScopeEnv &scope_env,
                      PPoint *cur_point);

// add to the CFG all points and edges encoding the behavior of stmt.
// execution of stmt begins at *cur_point, and at exit *cur_point will be
// filled in with the fall through point of stmt (i.e. if it does not jump
// somewhere else with a break/continue/goto/return). new_scope indicates
// whether an encountered compound statement should be treated as entering
// a new scope.
void ProcessStatement(Statement *stmt, bool new_scope,
                      PPoint *cur_point);

// process a variable declaration plus initialization.
void ProcessDeclarator(PPoint *cur_point, Declarator *decl);

// process a member initializer in a constructor.
void ProcessMemberInit(MemberInit *init,
                       PPoint *cur_point);

// process the outer function body statement and any initializers.
void ProcessFunctionBody(Function *func);

// add to the CFG all points and edges encoding the behavior of expr,
// according to the environment expr_env.
void ProcessExpression(const ExprEnv &expr_env,
                       Expression *expr);

// ditto for the expression within a condition.
void ProcessCondition(const ExprEnv &expr_env,
                      Condition *cond);

// as ProcessCondition, but using a branch as the ExprEnv (the common case).
void ProcessConditionBranch(PPoint *pre_point,
                            PPoint true_point, PPoint false_point,
                            Condition *cond);

// ditto for the expression(s) within an initializer, where assign_lval
// is the lvalue being initialized.
void ProcessInitializer(PPoint *pre_point,
                        Xgill::Exp *assign_lval, Type *assign_type,
                        Initializer *init);

// data on the name for a symbol which we expect to be globally unique,
// such as a type, function or other global variable. if we encounter
// definitions of symbols with the same name multiple times (as determined
// by their file/line), we will uniquify the later definitions.
struct SymbolData
{
  // definition being analyzed. this is a compound type, function or
  // global variable. dfunc and ddecl can *both* be specified, in which
  // case it is a declaration for a static local variable (treated as global).
  TS_classSpec *dspec;
  Function *dfunc;
  Declarator *ddecl;

  // source location of this definition.
  SourceLoc loc;

  // buffer storing the string representation of this symbol's location.
  Xgill::Buffer *location_buf;

  // after generating the transaction to look for previous occurrences
  // of this symbol, this receives the result where the exists/contents
  // list is stored.
  size_t transaction_result;

  // after submitting the transaction, this indicates whether the
  // definition for this symbol at this source location was previously
  // analyzed.
  bool previous_analyzed;

  // indicates if there are multiple definitions sharing the same name as
  // this symbol, and this is not the first one which was encountered.
  bool duplicate_analyzed;

  SymbolData()
    : dspec(NULL), dfunc(NULL), ddecl(NULL),
      loc(SL_UNKNOWN), location_buf(NULL), transaction_result(0),
      previous_analyzed(false), duplicate_analyzed(false)
  {}
};

typedef Xgill::HashTable< Variable*, SymbolData, Xgill::DataHash<Variable*> >
  SymbolDataTable;

// table for class/struct/union names.
extern SymbolDataTable csu_symbol_table;

// table for global variables, including functions.
extern SymbolDataTable var_symbol_table;

// visitor to fill in the keys and locations of csu_symbol_table
// and var_symbol_table with all defined symbols in the source file.
class XgillSymbolVisitor : public ASTVisitor
{
 public:
  Env &base_env;

  // number of enclosing class/struct/union definitions.
  size_t csu_depth;

  // number of enclosing function definitions.
  size_t function_depth;

  XgillSymbolVisitor(Env &_base_env)
    : base_env(_base_env), csu_depth(0), function_depth(0)
  {}

  // types and functions may be nested inside one another.
  // environments for ones not at the top level are stored here.
  Xgill::Vector<BlockEnv*> env_stack;

  // inherited methods.

  bool visitTypeSpecifier(TypeSpecifier *spec);
  bool visitFunction(Function *func);
  bool visitDeclaration(Declaration *decl);

  void postvisitTypeSpecifier(TypeSpecifier *spec);
  void postvisitFunction(Function *func);
};

// visitor over a SymbolDataTable to fill in a transaction with queries
// to determine which symbols have been analyzed and whether there are
// name collisions.
class SymbolDataFillTransaction
  : public Xgill::HashTableVisitor<Variable*,SymbolData>
{
 public:
  Transaction *t;
  const char *hash_name;

  SymbolDataFillTransaction(Transaction *_t, const char *_hash_name)
    : t(_t), hash_name(_hash_name)
  {}

  void Visit(Variable *&name, Xgill::Vector<SymbolData> &data_list);
};

// visitor to run over symbol tables after the transaction has been submitted
// to fill in the fetched information.
class SymbolDataCheckTransaction
  : public Xgill::HashTableVisitor<Variable*,SymbolData>
{
 public:
  Transaction *t;

  SymbolDataCheckTransaction(Transaction *_t)
    : t(_t)
  {}

  void Visit(Variable *&name, Xgill::Vector<SymbolData> &data_list);
};

// threshold for how many database inserts to do in a single transaction.
#define TRANSACTION_ADD_THRESHOLD 50

extern Xgill::ConfigOption print_generated;
extern Xgill::ConfigOption annotate;

// visitor to run over symbol tables and generate database inserts for
// the data on any symbols not previously analyzed.
class SymbolDataProcess
  : public Xgill::HashTableVisitor<Variable*,SymbolData>
{
 public:
  Env &base_env;
  Transaction *t;

  Xgill::Buffer scratch_buf;

  SymbolDataProcess(Env &_base_env, Transaction *_t)
    : base_env(_base_env), t(_t)
  {}

  void Visit(Variable *&name, Xgill::Vector<SymbolData> &data_list);

  void DoTypeSpecifier(Xgill::Buffer *buf, TS_classSpec *spec);
  void DoFunction(Xgill::Buffer *buf, Function *func);
  void DoDeclarator(Xgill::Buffer *buf, Declarator *decl, Function *func);
};

// process any annotation that was interpreted from the parsed data.
// this should only be called after all symbols have been processed.
void ProcessAnnotation();
