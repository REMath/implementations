// cond.cc
// code for cond.h

#include "cond.h"      // this module
#include "trace.h"     // trace
#include "glrtree.h"   // AttrContext
#include "util.h"      // TVAL
#include "exc.h"       // xBase


// ----------------------- Condition --------------------
Condition::~Condition()
{}


// --------------------- ExprCondition ---------------------
ExprCondition::~ExprCondition()
{
  delete expr;
}


bool ExprCondition::test(AttrContext const &actx) const
{
  int val = expr->eval(actx);
  if (val != 0 && val != 1) {
    xfailure(stringb("ExprCondition value must be 0 or 1 (was: " << val << ")"));
  }

  return val==1;
}


string ExprCondition::toString(Production const *prod) const
{
  return expr->toString(prod);
}


// -------------------- Conditions -------------------------
Conditions::Conditions()
{}

Conditions::~Conditions()
{}


bool Conditions::test(AttrContext const &actx) const
{
  FOREACH_OBJLIST(Condition, conditions, iter) {
    try {
      if (!iter.data()->test(actx)) {
	trace("conditions") 
	  << "condition " << iter.data()->toString(actx.reductionC().production)
	  << " not satisfied\n";
	return false;
      }
    }
    catch (xBase &x) {
      cout << "condition " << iter.data()->toString(actx.reductionC().production)
           << " failed with exception: " << x << endl;
      return false;
    }
  }
  return true;
}


string Conditions::toString(Production const *prod) const
{
  stringBuilder sb;
  FOREACH_OBJLIST(Condition, conditions, iter) {
    sb << "  %condition { " << iter.data()->toString(prod) << " }\n";
  }
  return sb;
}


void Conditions::parse(Production const *prod, char const *conditionText)
{
  TVAL(conditionText);

  // it's just an expression
  AExprNode *expr = parseAExpr(prod, conditionText);    // (owner)

  conditions.append(new ExprCondition(transferOwnership(expr)));
}
