// const_eval.h
// evaluate Expression AST nodes to a constant, if possible

#ifndef CONST_EVAL_H
#define CONST_EVAL_H

#include "str.h"         // string
#include "cc_flags.h"    // SimpleTypeId
#include "xassert.h"     // xassert

class Variable;          // variable.h
class Env;               // cc_env.h

// represent a value during constant evaluation; in essence, the
// constant evaluator is an interpreter for a small fragment of the
// expression language, and CValue is the type of data manipulated by
// that interpreter
class CValue {
public:      // data
  // This is the type of the value, as one of the C built-in types, or
  // ST_ERROR for a non-const-evaluatable expression, or ST_DEPENDENT
  // for an expression whose value depends on a template parameter.
  SimpleTypeId type;

  // kind of CValue; determines which element of the union below
  // is valid; basically a partition of SimpleTypeId
  enum Kind {
    K_SIGNED,                // signed integer value
    K_UNSIGNED,              // unsigned integer value
    K_FLOAT,                 // floating-point value (even for ST_DOUBLE)
    K_ERROR,                 // ST_ERROR
    K_DEPENDENT              // ST_DEPENDENT
  };

  union {
    long si;                 // K_SIGNED
    unsigned long ui;        // K_UNSIGNED
    float f;                 // K_FLOAT
    string *why;             // K_ERROR
  };

private:
  void dup(CValue const &obj);

public:      // funcs
  explicit CValue(SimpleTypeId t = ST_INT)
    { type=t; si=0; }
  explicit CValue(rostring why)
    { setError(why); }

  CValue(CValue const &obj)
    { dup(obj); }

  CValue& operator= (CValue const &obj)
    { dup(obj); return *this; }

  // map SimpleTypeId to CValue::Kind
  static Kind classify(SimpleTypeId t);

  Kind kind() const          { return classify(type); }
  bool isSigned() const      { return kind() == K_SIGNED; }
  bool isUnsigned() const    { return kind() == K_UNSIGNED; }
  bool isFloat() const       { return kind() == K_FLOAT; }
  bool isError() const       { return kind() == K_ERROR; }
  bool isDependent() const   { return kind() == K_DEPENDENT; }

  // true when the value cannot further be changed by arithmetic
  bool isSticky() const      { return isError() || isDependent(); }

  long getSignedValue() const    { xassert(isSigned()); return si; }
  long getUnsignedValue() const  { xassert(isUnsigned()); return ui; }
  float getFloatValue() const    { xassert(isFloat()); return f; }
  string *getWhy() const         { xassert(isError()); return why; }

  bool isZero() const;
  bool isIntegral() const;
  int getIntegralValue() const;

  void setSigned(SimpleTypeId t, long v);
  void setUnsigned(SimpleTypeId t, unsigned long v);
  void setFloat(SimpleTypeId t, float v);
  void setError(rostring why);
  void setDependent();

  void setBool(bool b)
    { setUnsigned(ST_BOOL, (unsigned)b); }

  // *this = <op> *this;
  void applyUnary(UnaryOp op);

  // *this = *this <op> other;
  void applyBinary(BinaryOp op, CValue other);
  
  // convert this value to 'newType', carrying along the value
  void convertToType(SimpleTypeId newType);

  // promote and convert
  void performIntegralPromotions();

  // convert *this and 'other' to a common type
  void applyUsualArithmeticConversions(CValue &other);
  
  // debugging
  string asString() const;
};


// this is a container for the evaluation state; the actual
// evaluation methods are associated with the AST nodes,
// and declared in cc_tcheck.ast
//
// 2005-03-30: It's become almost an empty container since I
// added the 'CValue' concept.  So be it.
class ConstEval {
public:      // data
  // needed to tell when an expression is value-dependent...
  Variable * /*nullable*/ dependentVar;

public:
  ConstEval(Variable * /*nullable*/ dependentVar);
  ~ConstEval();
  
  // evaluation of a Variable is exposed so that it can be
  // used with a Variable not wrapped in an E_variable
  CValue evaluateVariable(Variable *var);
};

#endif // CONST_EVAL_H
