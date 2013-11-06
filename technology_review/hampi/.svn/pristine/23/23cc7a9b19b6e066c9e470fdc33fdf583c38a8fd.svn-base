/**
The MIT License

Copyright (c) 2007 Adam Kiezun

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

package stp;

/**
 * This class provides raw access to STP.
 * You can use this class or the STPObject class hierarchy (which provides more object-oriented access and is almost always preferable).   
 */
public final class STPJNI {
    static {
//    	System.out.println("java.library.path = " + System.getProperty("java.library.path"));
        System.loadLibrary("STPJNI");
    }

  // o  : optimizations
  // c  : check counterexample
  // p  : print counterexample
  // h  : help
  // s  : stats
  // v  : print nodes
  public native static void vc_setFlags(char c);
  
  //! Flags can be NULL
  public native static long/*VC*/ vc_createValidityChecker();
  
  // Basic types
  public native static long/*Type*/ vc_boolType(long/*VC*/ vc);
  
  //! Create an array type
  public native static long/*Type*/ vc_arrayType(long/*VC*/ vc, long/*Type*/ typeIndex, long/*Type*/ typeData);

  /////////////////////////////////////////////////////////////////////////////
  // Expr manipulation methods                                               //
  /////////////////////////////////////////////////////////////////////////////

  //! Create a variable with a given name and type 
  /*! The type cannot be a function type. The var name can contain
    only variables, numerals and underscore. If you use any other
    symbol, you will get a segfault. */  
  public native static long/*Expr*/ vc_varExpr(long/*VC*/ vc, String name, long/*Type*/ type);

  //The var name can contain only variables, numerals and
  //underscore. If you use any other symbol, you will get a segfault.
  public native static long/*Expr*/ vc_varExpr1(long/*VC*/ vc, String name, int indexwidth, int valuewidth);

  //! Get the expression and type associated with a name.
  /*!  If there is no such Expr, a NULL Expr is returned. */
  //long/*Expr*/ vc_lookupVar(long/*VC*/ vc, char* name, long/*Type*/* type);
  
  //! Get the type of the Expr.
  public native static long/*Type*/ vc_getType(long/*VC*/ vc, long/*Expr*/ e);
  
  public native static int vc_getBVLength(long/*VC*/ vc, long/*Expr*/ e);

  //! Create an equality expression.  The two children must have the same type.
  public native static long/*Expr*/ vc_eqExpr(long/*VC*/ vc, long/*Expr*/ child0, long/*Expr*/ child1);
  
  // Boolean expressions
  
  // The following functions create Boolean expressions.  The children
  // provided as arguments must be of type Boolean (except for the
  // function vc_iteExpr(). In the case of vc_iteExpr() the
  // conditional must always be Boolean, but the ifthenpart
  // (resp. elsepart) can be bit-vector or Boolean type. But, the
  // ifthenpart and elsepart must be both of the same type)
  public native static long/*Expr*/ vc_trueExpr(long/*VC*/ vc);
  public native static long/*Expr*/ vc_falseExpr(long/*VC*/ vc);
  public native static long/*Expr*/ vc_notExpr(long/*VC*/ vc, long/*Expr*/ child);
  public native static long/*Expr*/ vc_andExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_andExprN(long/*VC*/ vc, long/*Expr*/[] children, int numOfChildNodes);
  public native static long/*Expr*/ vc_orExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_orExprN(long/*VC*/ vc, long/*Expr*/[] children, int numOfChildNodes);
  public native static long/*Expr*/ vc_impliesExpr(long/*VC*/ vc, long/*Expr*/ hyp, long/*Expr*/ conc);
  public native static long/*Expr*/ vc_iffExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  //The output type of vc_iteExpr can be Boolean (formula-level ite)
  //or bit-vector (word-level ite)
  public native static long/*Expr*/ vc_iteExpr(long/*VC*/ vc, long/*Expr*/ conditional, long/*Expr*/ ifthenpart, long/*Expr*/ elsepart);
  
  //Boolean to single bit BV Expression
  public native static long/*Expr*/ vc_boolToBVExpr(long/*VC*/ vc, long/*Expr*/ form);

  // Arrays
  
  //! Create an expression for the value of array at the given index
  public native static long/*Expr*/ vc_readExpr(long/*VC*/ vc, long/*Expr*/ array, long/*Expr*/ index);

  //! Array update; equivalent to "array WITH [index] := newValue"
  public native static long/*Expr*/ vc_writeExpr(long/*VC*/ vc, long/*Expr*/ array, long/*Expr*/ index, long/*Expr*/ newValue);
  
  // Expr I/O
  //! long/*Expr*/ vc_parseExpr(long/*VC*/ vc, char* s);

  //! Prlongs 'e' to stdout.
  public native static void vc_printExpr(long/*VC*/ vc, long/*Expr*/ e);

  //! Prints 'e' into an open file descriptor 'fd'
  public native static void vc_printExprFile(long/*VC*/ vc, long/*Expr*/ e, int fd);

  //! Prints 'e' to malloc'd buffer '*buf'.  Sets '*len' to the length of 
  //  the buffer. It is the responsibility of the caller to free the buffer.
  //TODO
  //public native static void vc_printExprToBuffer(long/*VC*/ vc, long/*Expr*/ e, char **buf, unsigned long * len);

  //! Prints counterexample to stdout.
  public native static void vc_printCounterExample(long/*VC*/ vc);

  //! Prints variable declarations to stdout.
  public native static void vc_printVarDecls(long/*VC*/ vc);

  //! Prints asserts to stdout. The flag simplify_print must be set to
  //"1" if you wish simplification to occur dring printing. It must be
  //set to "0" otherwise
  public native static void vc_printAsserts(long/*VC*/ vc, int simplify_print);

  //! Prints the state of the query to malloc'd buffer '*buf' and
  //stores ! the length of the buffer to '*len'.  It is the
  //responsibility of the caller to free the buffer. The flag
  //simplify_print must be set to "1" if you wish simplification to
  //occur dring printing. It must be set to "0" otherwise
  //TODO
  //public native static void vc_printQueryStateToBuffer(long/*VC*/ vc, long/*Expr*/ e, char **buf, unsigned long *len, int simplify_print);

  //! Similar to vc_printQueryStateToBuffer()
  //TODO
  //public native static void vc_printCounterExampleToBuffer(long/*VC*/ vc, char **buf,unsigned long *len);

  //! Prints query to stdout.
  public native static void vc_printQuery(long/*VC*/ vc);

  /////////////////////////////////////////////////////////////////////////////
  // Context-related methods                                                 //
  /////////////////////////////////////////////////////////////////////////////
  
  //! Assert a new formula in the current context.  
  /*! The formula must have Boolean type. */
  public native static void vc_assertFormula(long/*VC*/ vc, long/*Expr*/ e);
  
  //! Simplify e with respect to the current context
  public native static long/*Expr*/ vc_simplify(long/*VC*/ vc, long/*Expr*/ e);

  //! Check validity of e in the current context. e must be a FORMULA
  //
  //if returned 0 then input is INVALID. 
  //
  //if returned 1 then input is VALID
  //
  //if returned 2 then ERROR
  public native static int vc_query(long/*VC*/ vc, long/*Expr*/ e);
  
  //! Return the counterexample after a failed query.
  public native static long/*Expr*/ vc_getCounterExample(long/*VC*/ vc, long/*Expr*/ e);

  //! get size of counterexample, i.e. the number of variables/array
  //locations in the counterexample.
  public native static int vc_counterexample_size(long/*VC*/ vc);
  
  //! Checkpoint the current context and increase the scope level
  public native static void vc_push(long/*VC*/ vc);
  
  //! Restore the current context to its state at the last checkpoint
  public native static void vc_pop(long/*VC*/ vc);
  
  //! Return an int from a constant bitvector expression
  public native static int getBVInt(long/*Expr*/ e);
  //! Return an unsigned int from a constant bitvector expression
  //TODO
  public native static long getBVUnsigned(long/*Expr*/ e);
  //! Return an unsigned long long int from a constant bitvector expressions
  //TODO
  //public native static unsigned long long int getBVUnsignedLongLong(long/*Expr*/ e);
  
  /**************************/
  /* BIT VECTOR OPERATIONS  */
  /**************************/
  public native static long/*Type*/ vc_bvType(long/*VC*/ vc, int no_bits);
  public native static long/*Type*/ vc_bv32Type(long/*VC*/ vc);
  
  public native static long/*Expr*/ vc_bvConstExprFromStr(long/*VC*/ vc, String binary_repr);
  public native static long/*Expr*/ vc_bvConstExprFromInt(long/*VC*/ vc, int n_bits, int value);
  //TODO public native static long/*Expr*/ vc_bvConstExprFromLL(long/*VC*/ vc, int n_bits, unsigned long long value);
  public native static long/*Expr*/ vc_bv32ConstExprFromInt(long/*VC*/ vc, int value);
  
  public native static long/*Expr*/ vc_bvConcatExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvPlusExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bv32PlusExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvMinusExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bv32MinusExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvMultExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bv32MultExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  // left divided by right i.e. left/right
  public native static long/*Expr*/ vc_bvDivExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  // left modulo right i.e. left%right
  public native static long/*Expr*/ vc_bvModExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  // signed left divided by right i.e. left/right
  public native static long/*Expr*/ vc_sbvDivExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  // signed left modulo right i.e. left%right
  public native static long/*Expr*/ vc_sbvModExpr(long/*VC*/ vc, int n_bits, long/*Expr*/ left, long/*Expr*/ right);
  
  public native static long/*Expr*/ vc_bvLtExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvLeExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvGtExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvGeExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  
  public native static long/*Expr*/ vc_sbvLtExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_sbvLeExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_sbvGtExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_sbvGeExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  
  public native static long/*Expr*/ vc_bvUMinusExpr(long/*VC*/ vc, long/*Expr*/ child);

  // bitwise operations: these are terms not formulas  
  public native static long/*Expr*/ vc_bvAndExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvOrExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvXorExpr(long/*VC*/ vc, long/*Expr*/ left, long/*Expr*/ right);
  public native static long/*Expr*/ vc_bvNotExpr(long/*VC*/ vc, long/*Expr*/ child);
  
  public native static long/*Expr*/ vc_bvLeftShiftExpr(long/*VC*/ vc, int sh_amt, long/*Expr*/ child);
  public native static long/*Expr*/ vc_bvRightShiftExpr(long/*VC*/ vc, int sh_amt, long/*Expr*/ child);
  /* Same as vc_bvLeftShift only that the answer in 32 bits long */
  public native static long/*Expr*/ vc_bv32LeftShiftExpr(long/*VC*/ vc, int sh_amt, long/*Expr*/ child);
  /* Same as vc_bvRightShift only that the answer in 32 bits long */
  public native static long/*Expr*/ vc_bv32RightShiftExpr(long/*VC*/ vc, int sh_amt, long/*Expr*/ child);
  public native static long/*Expr*/ vc_bvVar32LeftShiftExpr(long/*VC*/ vc, long/*Expr*/ sh_amt, long/*Expr*/ child);
  public native static long/*Expr*/ vc_bvVar32RightShiftExpr(long/*VC*/ vc, long/*Expr*/ sh_amt, long/*Expr*/ child);
  public native static long/*Expr*/ vc_bvVar32DivByPowOfTwoExpr(long/*VC*/ vc, long/*Expr*/ child, long/*Expr*/ rhs);

  public native static long/*Expr*/ vc_bvExtract(long/*VC*/ vc, long/*Expr*/ child, int high_bit_no, int low_bit_no);
  
  //accepts a bitvector and position, and returns a boolean
  //corresponding to that position. More precisely, it return the
  //equation (x[bit_no:bit_no] = 0)
  //FIXME  = 1 ?
  public native static long/*Expr*/ vc_bvBoolExtract(long/*VC*/ vc, long/*Expr*/ x, int bit_no);  
  public native static long/*Expr*/ vc_bvSignExtend(long/*VC*/ vc, long/*Expr*/ child, int nbits);
  
  /*C pointer support:  C interface to support C memory arrays in CVCL */
  public native static long/*Expr*/ vc_bvCreateMemoryArray(long/*VC*/ vc, String arrayName);
  public native static long/*Expr*/ vc_bvReadMemoryArray(long/*VC*/ vc, long/*Expr*/ array, long/*Expr*/ byteIndex, int numOfBytes);
  public native static long/*Expr*/ vc_bvWriteToMemoryArray(long/*VC*/ vc, long/*Expr*/ array, long/*Expr*/  byteIndex, long/*Expr*/ element, int numOfBytes);
  
  // return a string representation of the long/*Expr*/ e. The caller is responsible
  // for deallocating the string with free()
  public native static String exprString(long/*Expr*/ e);
  
  // return a string representation of the Type t. The caller is responsible
  // for deallocating the string with free()
  public native static String typeString(long/*Type*/ t);

  public native static long/*Expr*/ getChild(long/*Expr*/ e, int i);

  //1.if input expr is TRUE then the function returns 1;
  //
  //2.if input expr is FALSE then function returns 0;
  //
  //3.otherwise the function returns -1
  public native static int vc_isBool(long/*Expr*/ e);

  /* Register the given error handler to be called for each fatal error.*/
  //TODO
  //public native static void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg));

  public native static int vc_getHashQueryStateToBuffer(long/*VC*/ vc, long/*Expr*/ query);

  //destroys the STP instance, and removes all the created expressions
  public native static void vc_Destroy(long/*VC*/ vc);

  //deletes the expression e
  public native static void vc_DeleteExpr(long/*Expr*/ e);

  //Get the whole counterexample from the current context
  public native static long/*WholeCounterExample*/ vc_getWholeCounterExample(long/*VC*/ vc);

  //Get the value of a term expression from the CounterExample
  public native static long/*Expr*/ vc_getTermFromCounterExample(long/*VC*/ vc, long/*Expr*/ e, long/*WholeCounterExample*/ c);

  // get the kind of the expression
  public native static int getExprKind (long/*Expr*/ e);

  // get the number of children nodes
  public native static int getDegree (long/*Expr*/ e);

  // get the bv length
  public native static int getBVLength(long/*Expr*/ e);

  // get expression type
  public native static int getType (long/*Expr*/ e);

  // get value bit width
  public native static int getVWidth (long/*Expr*/ e);

  // get index bit width
  public native static int getIWidth (long/*Expr*/ e);

  // Prints counterexample to an open file descriptor 'fd'
  public native static void vc_printCounterExampleFile(long/*VC*/ vc, int fd);

  // get name of expression. must be a variable.
  public native static String exprName(long/*Expr*/ e);
  
  // get the node ID of an Expr.
  public native static int getExprID (long/*Expr*/ ex);

}
