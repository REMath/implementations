// const_eval.cc
// code for const_eval.h

#include "const_eval.h"     // this module
#include "cc_ast.h"         // C++ AST
#include "cc_env.h"         // Env
#include "stdconv.h"        // applyIntegralPromotions, etc.


// ----------------------- CValue ------------------------
STATICDEF CValue::Kind CValue::classify(SimpleTypeId t)
{
  switch (t) {
    case ST_CHAR:
    case ST_SIGNED_CHAR:
    case ST_SHORT_INT:
    case ST_WCHAR_T:
    case ST_INT:
    case ST_LONG_INT:
    case ST_LONG_LONG:
      return K_SIGNED;

    case ST_BOOL:
    case ST_UNSIGNED_CHAR:
    case ST_UNSIGNED_SHORT_INT:
    case ST_UNSIGNED_INT:
    case ST_UNSIGNED_LONG_INT:
    case ST_UNSIGNED_LONG_LONG:
      return K_UNSIGNED;

    case ST_FLOAT:
    case ST_DOUBLE:
    case ST_LONG_DOUBLE:
      return K_FLOAT;

    case ST_DEPENDENT:
      return K_DEPENDENT;

    default:
      return K_ERROR;
  }
}


void CValue::dup(CValue const &obj)
{
  type = obj.type;
  switch (classify(type)) {
    case K_SIGNED:    si = obj.si;     break;
    case K_UNSIGNED:  ui = obj.ui;     break;
    case K_FLOAT:     f = obj.f;       break;
    case K_ERROR:     why = obj.why;   break;
    case K_DEPENDENT:                  break;
  }
}


bool CValue::isZero() const
{
  switch (kind()) {
    default: // silence warning
    case K_SIGNED:    return si == 0;
    case K_UNSIGNED:  return ui == 0;
    case K_FLOAT:     return f == 0.0;
  }
}


bool CValue::isIntegral() const
{
  Kind k = kind();
  return k==K_SIGNED || k==K_UNSIGNED;
}

int CValue::getIntegralValue() const
{
  xassert(isIntegral());
  if (kind() == K_SIGNED) {
    return si;
  }
  else {
    return (int)ui;
  }
}


void CValue::setSigned(SimpleTypeId t, long v)
{
  type = t;
  xassert(isSigned());
  si = v;
}


void CValue::setUnsigned(SimpleTypeId t, unsigned long v)
{
  type = t;
  xassert(isUnsigned());
  ui = v;
}


void CValue::setFloat(SimpleTypeId t, float v)
{
  type = t;
  xassert(isFloat());
  f = v;
}


void CValue::setError(rostring w)
{
  type = ST_ERROR;
  why = new string(w);
}


void CValue::setDependent()
{
  type = ST_DEPENDENT;
  si = 0;
}


void CValue::performIntegralPromotions()
{
  convertToType(applyIntegralPromotions(type));
}

void CValue::convertToType(SimpleTypeId newType)
{
  Kind oldKind = classify(type);
  Kind newKind = classify(newType);
  if (newKind != oldKind &&
      oldKind != K_ERROR && oldKind != K_DEPENDENT &&
      newKind != K_ERROR && newKind != K_DEPENDENT) {

    xassert((unsigned)oldKind < 8u);    // for my representation trick

    // sort of like ML-style case analysis on a pair of values
    switch (newKind*8 + oldKind) {
      default:
        xfailure("unexpected type conversion scenario in const-eval");
        break;                   // silence warning

      case K_SIGNED*8 + K_UNSIGNED:
        si = (long)ui;           // convert unsigned to signed
        break;

      case K_SIGNED*8 + K_FLOAT:
        si = (long)f;
        break;

      case K_UNSIGNED*8 + K_SIGNED:
        ui = (unsigned long)si;
        break;

      case K_UNSIGNED*8 + K_FLOAT:
        ui = (unsigned long)f;
        break;

      case K_FLOAT*8 + K_SIGNED:
        f = (float)si;
        break;

      case K_FLOAT*8 + K_UNSIGNED:
        f = (float)ui;
        break;
    }
  }

  type = newType;

  // truncate the value based on the final type
  int reprSize = simpleTypeReprSize(type);
  if (reprSize >= 4) {
    // do no truncation
  }
  else {
    int maxValue = (1 << 8*reprSize) - 1;
    switch (kind()) {
      case K_SIGNED:     if (si > maxValue) { si=maxValue; }  break;
      case K_UNSIGNED:   if (ui > (unsigned)maxValue) { ui=(unsigned)maxValue; }  break;
      default: break;   // ignore
    }
  }
}


void CValue::applyUnary(UnaryOp op)
{
  if (isSticky()) { return; }

  switch (op) {
    default: xfailure("bad code");

    case UNY_PLUS:
      // 5.3.1p6
      performIntegralPromotions();
      break;

    case UNY_MINUS:
      // 5.3.1p7
      performIntegralPromotions();
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:    si = -si;   break;
        case K_UNSIGNED:  ui = -ui;   break;
        case K_FLOAT:     f = -f;     break;
      }
      break;

    case UNY_NOT:
      // 5.3.1p8
      ui = isZero()? 1u : 0u;
      type = ST_BOOL;
      break;

    case UNY_BITNOT:
      // 5.3.1p9
      performIntegralPromotions();
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:    si = ~si;   break;
        case K_UNSIGNED:  ui = ~ui;   break;
        case K_FLOAT:     setError("cannot apply ~ to float types"); break;
      }
  }
}


void CValue::applyUsualArithmeticConversions(CValue &other)
{
  SimpleTypeId finalType = usualArithmeticConversions(type, other.type);
  this->convertToType(finalType);
  other.convertToType(finalType);
}

void CValue::applyBinary(BinaryOp op, CValue other)
{
  if (isSticky()) { return; }
  
  if (other.isSticky()) {
    *this = other;
    return;
  }

  switch (op) {
    default:
      setError(stringc << "cannot const-eval binary operator `" 
                       << toString(op) << "'");
      return;

    // ---- 5.6 ----
    case BIN_MULT:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si * other.si;    break;
        case K_UNSIGNED:   ui = ui * other.ui;    break;
        case K_FLOAT:      f = f * other.f;       break;
      }
      break;

    case BIN_DIV:
      applyUsualArithmeticConversions(other);
      if (other.isZero()) {
        setError("division by zero");
        return;
      }
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si / other.si;    break;
        case K_UNSIGNED:   ui = ui / other.ui;    break;
        case K_FLOAT:      f = f / other.f;       break;
      }
      break;

    case BIN_MOD:
      applyUsualArithmeticConversions(other);
      if (other.isZero()) {
        setError("mod by zero");
        return;
      }
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si % other.si;    break;
        case K_UNSIGNED:   ui = ui % other.ui;    break;
        case K_FLOAT:      setError("mod applied to floating-point args"); return;
      }
      break;

    // ---- 5.7 ----
    case BIN_PLUS:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si + other.si;    break;
        case K_UNSIGNED:   ui = ui + other.ui;    break;
        case K_FLOAT:      f = f + other.f;       break;
      }
      break;

    case BIN_MINUS:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si - other.si;    break;
        case K_UNSIGNED:   ui = ui - other.ui;    break;
        case K_FLOAT:      f = f - other.f;       break;
      }
      break;

    // ---- gcc <? and >? ----
    // guessing that <? and >? behave approximately like '+' in
    // terms of the types
    case BIN_MINIMUM:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case CValue::K_SIGNED:     si = ((si < other.si) ? si : other.si);   break;
        case CValue::K_UNSIGNED:   ui = ((ui < other.ui) ? ui : other.ui);   break;
        case CValue::K_FLOAT:      f = ((f < other.f) ? f : other.f);        break;
      }
      break;

    case BIN_MAXIMUM:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case CValue::K_SIGNED:     si = ((si > other.si) ? si : other.si);   break;
        case CValue::K_UNSIGNED:   ui = ((ui > other.ui) ? ui : other.ui);   break;
        case CValue::K_FLOAT:      f = ((f > other.f) ? f : other.f);        break;
      }
      break;

    // ---- 5.8 ----
    case BIN_LSHIFT:
    case BIN_RSHIFT: {
      this->performIntegralPromotions();
      other.performIntegralPromotions();

      if (kind() == K_FLOAT || other.kind() == K_FLOAT) {
        setError("cannot shift with float types");
        return;
      }

      // get shift amount
      int shamt = 0;
      switch (other.kind()) {
        default: // silence warning
        case K_SIGNED:     shamt = other.si;    break;
        case K_UNSIGNED:   shamt = other.ui;    break;
      }

      // apply it
      if (op == BIN_LSHIFT) {
        switch (kind()) {
          default: // silence warning
          case K_SIGNED:     si <<= shamt;    break;
          case K_UNSIGNED:   ui <<= shamt;    break;
        }
      }
      else {
        switch (kind()) {
          default: // silence warning
          case K_SIGNED:     si >>= shamt;    break;
          case K_UNSIGNED:   ui >>= shamt;    break;
        }
      }
      break;
    }

    // ---- 5.9 ----
    case BIN_LESS:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si < other.si;    break;
        case K_UNSIGNED:   ui = ui < other.ui;    break;
        case K_FLOAT:      ui = f < other.f;       break;
      }
      type = ST_BOOL;
      break;

    case BIN_GREATER:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si > other.si;    break;
        case K_UNSIGNED:   ui = ui > other.ui;    break;
        case K_FLOAT:      ui = f > other.f;       break;
      }
      type = ST_BOOL;
      break;

    case BIN_LESSEQ:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si <= other.si;    break;
        case K_UNSIGNED:   ui = ui <= other.ui;    break;
        case K_FLOAT:      ui = f <= other.f;       break;
      }
      type = ST_BOOL;
      break;

    case BIN_GREATEREQ:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si >= other.si;    break;
        case K_UNSIGNED:   ui = ui >= other.ui;    break;
        case K_FLOAT:      ui = f >= other.f;       break;
      }
      type = ST_BOOL;
      break;

    // ---- 5.10 ----
    case BIN_EQUAL:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si == other.si;    break;
        case K_UNSIGNED:   ui = ui == other.ui;    break;
        case K_FLOAT:      ui = f == other.f;       break;
      }
      type = ST_BOOL;
      break;

    case BIN_NOTEQUAL:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     ui = si != other.si;    break;
        case K_UNSIGNED:   ui = ui != other.ui;    break;
        case K_FLOAT:      ui = f != other.f;       break;
      }
      type = ST_BOOL;
      break;

    // ---- 5.11 ----
    case BIN_BITAND:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si & other.si;    break;
        case K_UNSIGNED:   ui = ui & other.ui;    break;
        case K_FLOAT:      setError("cannot apply bitand to float types"); break;
      }
      break;

    // ---- 5.12 ----
    case BIN_BITXOR:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si ^ other.si;    break;
        case K_UNSIGNED:   ui = ui ^ other.ui;    break;
        case K_FLOAT:      setError("cannot apply bitxor to float types"); break;
      }
      break;

    // ---- 5.13 ----
    case BIN_BITOR:
      applyUsualArithmeticConversions(other);
      switch (kind()) {
        default: // silence warning
        case K_SIGNED:     si = si | other.si;    break;
        case K_UNSIGNED:   ui = ui | other.ui;    break;
        case K_FLOAT:      setError("cannot apply bitor to float types"); break;
      }
      break;

    // ---- 5.14 ----
    case BIN_AND:
      // Note: short-circuit behavior is handled by the caller of
      // this function; by the time we get here, both args have
      // already been evaluated
      this->convertToType(ST_BOOL);
      other.convertToType(ST_BOOL);
      ui = ui && other.ui;
      break;

    // ---- 5.15 ----
    case BIN_OR:
      this->convertToType(ST_BOOL);
      other.convertToType(ST_BOOL);
      ui = ui || other.ui;
      break;
  }
}


string CValue::asString() const
{
  switch (kind()) {
    case K_SIGNED:      return stringc << toString(type) << ": " << si;
    case K_UNSIGNED:    return stringc << toString(type) << ": " << ui;
    case K_FLOAT:       return stringc << toString(type) << ": " << f;
    case K_ERROR:       return stringc << "error: " << *why;
    default:    // silence warning
    case K_DEPENDENT:   return "dependent";
  }
}


// ----------------------- ConstEval ------------------------
ConstEval::ConstEval(Variable *d)
  : dependentVar(d)
{}

ConstEval::~ConstEval()
{}


// external interface
CValue Expression::constEval(ConstEval &env) const
{
  #if 1       // production
    return iconstEval(env);
  #else       // debugging
    #warning debugging code is enabled
    CValue ret = iconstEval(env);
    cout << "const-eval of `" << exprToString() << "' is " << ret.asString() << endl;
    return ret;
  #endif
}


CValue Expression::iconstEval(ConstEval &env) const
{
  if (ambiguity) {
    // 2005-05-26: This used to be cause for an assertion failure, but
    // what can happen (in/c/dC0018.c) is that a user-error here or
    // higher up causes the tcheck to prune, thereby leaving an
    // ambiguity link.  What I will do is make this a user-error
    // condition also, under the premise that (due to disambiguation
    // selecting a different interpretation) the user will never see
    // it; but by adding the error, I ensure this interpretation will
    // not part of a successful parse.
    return CValue("ambiguous expr being const-eval'd (user should not see this)");
  }

  if (type->isError()) {
    // don't try to const-eval an expression that failed
    // to typecheck
    return CValue("failed to tcheck");
  }

  ASTSWITCHC(Expression, this) {
    // Handle this idiom for finding a member offset:
    // &((struct scsi_cmnd *)0)->b.q
    ASTCASEC(E_addrOf, eaddr)
      return eaddr->expr->constEvalAddr(env);

    ASTNEXTC(E_boolLit, b)
      CValue ret;
      ret.setBool(b->b);
      return ret;

    ASTNEXTC(E_intLit, i)
      CValue ret;
      SimpleTypeId id = type->isSimpleType() ? type->asSimpleTypeC()->type : ST_LONG_INT;
      switch (CValue::classify(id)) {
        default: xfailure("unexpected intlit type");
        case CValue::K_SIGNED:     ret.setSigned(id, (long)i->i);              break;
        case CValue::K_UNSIGNED:   ret.setUnsigned(id, (unsigned long)i->i);   break;
      }
      return ret;

    ASTNEXTC(E_floatLit, f)
      CValue ret;
      SimpleTypeId id = type->asSimpleTypeC()->type;
      ret.setFloat(id, (float)f->d);
      return ret;

    ASTNEXTC(E_charLit, c)
      CValue ret;
      SimpleTypeId id = type->asSimpleTypeC()->type;
      switch (CValue::classify(id)) {
        default: xfailure("unexpected charlit type");
        case CValue::K_SIGNED:     ret.setSigned(id, (long)c->c);              break;
        case CValue::K_UNSIGNED:   ret.setUnsigned(id, (unsigned long)c->c);   break;
      }
      return ret;

    ASTNEXTC(E_variable, v)
      return env.evaluateVariable(v->var);

    ASTNEXTC(E_constructor, c)
      if (type->isIntegerType()) {
        // allow it; should only be 1 arg, and that will be value
        return c->args->first()->constEval(env);
      }
      else {
        return CValue("can only const-eval E_constructors for integer types");
      }

    ASTNEXTC(E_sizeof, s)
      // 5.3.3p6: result is of type 'size_t'; most systems (including my
      // elsa/include/stddef.h header) make that the same as 'unsigned';
      // in any case, it must be an unsigned integer type (c99, 7.17p2)
      CValue ret;
      ret.setUnsigned(ST_UNSIGNED_INT, s->size);
      return ret;

    ASTNEXTC(E_unary, u)
      CValue ret = u->expr->constEval(env);
      ret.applyUnary(u->op);
      return ret;

    ASTNEXTC(E_binary, b)
      if (b->op == BIN_COMMA) {
        // avoid trying to eval the LHS
        return b->e2->constEval(env);
      }

      CValue v1 = b->e1->constEval(env);
      if (b->op == BIN_AND && v1.isZero()) {
        CValue ret;
        ret.setBool(false);   // short-circuit: propagate false
        return ret;
      }
      if (b->op == BIN_OR && !v1.isZero()) {
        CValue ret;
        ret.setBool(true);    // short-circuit: propagate false
        return ret;
      }

      CValue v2 = b->e2->constEval(env);

      v1.applyBinary(b->op, v2);
      return v1;

    ASTNEXTC(E_cast, c)
      return constEvalCast(env, c->ctype, c->expr);
      
    ASTNEXTC(E_keywordCast, c)
      if (c->key == CK_DYNAMIC) {
        return CValue("cannot const-eval a keyword_cast");
      }
      else {
        // assume the other three work like C casts
        return constEvalCast(env, c->ctype, c->expr);
      }

    ASTNEXTC(E_cond, c)
      CValue v = c->cond->constEval(env);
      if (v.isSticky()) {
        return v;
      }

      if (!v.isZero()) {
        return c->th->constEval(env);
      }
      else {
        return c->el->constEval(env);
      }

    ASTNEXTC(E_sizeofType, s)
      if (s->atype->getType()->isGeneralizedDependent()) {
        return CValue(ST_DEPENDENT);
      }
      CValue ret;
      ret.setUnsigned(ST_UNSIGNED_INT, s->size);
      return ret;

    ASTNEXTC(E_grouping, e)
      return e->expr->constEval(env);

    // bhackett
    ASTNEXTC(E___builtin_constant_p, bc)
      CValue v = bc->expr->constEval(env);

      int val = 1;
      if (v.isError() || v.isDependent())
        val = 0;

      CValue ret;
      ret.setUnsigned(ST_UNSIGNED_INT, val);
      return ret;

    ASTDEFAULTC
      return extConstEval(env);

    ASTENDCASEC
  }
}

// The intent of this function is to provide a hook where extensions
// can handle the 'constEval' message for their own AST syntactic
// forms, by overriding this function.  The non-extension nodes use
// the switch statement above, which is more compact.
CValue Expression::extConstEval(ConstEval &env) const
{
  return CValue(stringc << kindName() << " is not constEval'able");
}


CValue ConstEval::evaluateVariable(Variable *var)
{
  if (var->isEnumerator()) {
    CValue ret;
    ret.setSigned(ST_INT, var->getEnumeratorValue());
    return ret;
  }

  if (var->type->isCVAtomicType() &&
      (var->type->asCVAtomicTypeC()->cv & CV_CONST) &&
      var->value) {
    // const variable
    return var->value->constEval(*this);
  }

  if (var->type->isGeneralizedDependent() &&
      var->value) {
    return CValue(ST_DEPENDENT);
  }

  if (var->isTemplateParam()) {
    return CValue(ST_DEPENDENT);
  }

  if (var == dependentVar) {
    // value-dependent expression
    return CValue(ST_DEPENDENT);
  }

  return CValue(stringc
    << "can't const-eval non-const variable `" << var->name << "'");
}


// TODO: This function is basically a stub; it does not compute
// the right result in almost any circumstance.
CValue Expression::constEvalAddr(ConstEval &env) const
{
  // FIX: I'm sure there are cases missing from this
  ASTSWITCHC(Expression, this) {
    // These two are dereferences, so they recurse back to constEval().
    ASTCASEC(E_deref, e)
      return e->ptr->constEval(env);

    ASTNEXTC(E_arrow, e)
      return e->obj->constEval(env);

    // These just recurse on constEvalAddr().
    ASTNEXTC(E_fieldAcc, e)
      return e->obj->constEvalAddr(env);

    ASTNEXTC(E_cast, e)
      return e->expr->constEvalAddr(env);

    ASTNEXTC(E_keywordCast, e)
      // FIX: haven't really thought about these carefully
      switch (e->key) {
        default:
          xfailure("bad CastKeyword");

        case CK_DYNAMIC:
          return CValue("can't const-eval dynamic_cast");

        case CK_STATIC:
        case CK_REINTERPRET:
        case CK_CONST:
          return e->expr->constEvalAddr(env);
      }
      break;

    ASTNEXTC(E_grouping, e)
      return e->expr->constEvalAddr(env);

    ASTDEFAULTC
      return CValue("unhandled case in constEvalAddr");

    ASTENDCASEC
  }
}


CValue Expression::constEvalCast(ConstEval &env, ASTTypeId const *ctype,
                                 Expression const *expr) const
{
  CValue ret = expr->constEval(env);
  if (ret.isSticky()) {
    return ret;
  }

  Type *t = ctype->getType();
  if (t->isSimpleType()) {
    ret.convertToType(t->asSimpleTypeC()->type);
  }
  else if (t->isEnumType() ||
           t->isPointer()) {        // for Linux kernel
    ret.convertToType(ST_INT);
  }
  else {
    // TODO: this is probably not the right rule..
    return CValue(stringc
      << "in constant expression, can only cast to arithmetic or pointer types, not `"
      << t->toString() << "'");
  }

  return ret;
}


// EOF
