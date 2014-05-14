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

import static stp.STPJNI.*;

public class VC extends STPObject {
    
    public VC(){
        super(vc_createValidityChecker());
    }
    
    /**
     * destroys the STP instance, and removes all the created expressions
     */
    public void Destroy() {
        STPJNI.vc_Destroy(handle);
    }
    
    public Type boolType()
    {
       return new Type(STPJNI.vc_boolType(handle));   
    }
    
    /** Create an array type */
    public Type arrayType(Type typeIndex, Type typeData)
    {
       return new Type(STPJNI.vc_arrayType(handle, typeIndex.handle, typeData.handle));
    }

    /////////////////////////////////////////////////////////////////////////////
    // Expr manipulation methods                                               //
    /////////////////////////////////////////////////////////////////////////////

    /** Create a variable with a given name and type 
      The type cannot be a function type. The var name can contain
      only variables, numerals and underscore. If you use any other
      symbol, you will get a segfault. 
    */  
    public Expr varExpr(String name, Type type)
    {
       return new Expr(STPJNI.vc_varExpr(handle, name, type.handle));
    }

    /**
     * The var name can contain only variables, numerals and
     * underscore. If you use any other symbol, you will get a segfault. 
     */
    public Expr varExpr1(String name, int indexwidth, int valuewidth)
    {
        return new Expr(STPJNI.vc_varExpr1(handle, name, indexwidth, valuewidth));
    }

    /** Get the type of the Expr. */
    public Type getType(Expr e)
    {
        return new Type(STPJNI.vc_getType(handle, e.handle));
    }
    
    public int getBVLength(Expr e)
    {
        return STPJNI.vc_getBVLength(handle, e.handle);
    }

    /** Create an equality expression.  The two children must have the same type. */
    public Expr eqExpr(Expr child0, Expr child1)
    {
        return new Expr(STPJNI.vc_eqExpr(handle, child0.handle, child1.handle));
    }
    
    // Boolean expressions
    
    // The following functions create Boolean expressions.  The children
    // provided as arguments must be of type Boolean (except for the
    // function iteExpr(). In the case of iteExpr() the
    // conditional must always be Boolean, but the ifthenpart
    // (resp. elsepart) can be bit-vector or Boolean type. But, the
    // ifthenpart and elsepart must be both of the same type)
    public Expr trueExpr()
    {
        return new Expr(STPJNI.vc_trueExpr(handle));
    }
    
    public Expr falseExpr()
    {
        return new Expr(STPJNI.vc_falseExpr(handle));
    }
    
    public Expr notExpr(Expr child)
    {
        return new Expr(STPJNI.vc_notExpr(handle, child.handle));
    }
    
    public Expr andExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_andExpr(handle, left.handle, right.handle));
    }

    public Expr andExprN(Expr[] children)
    {
        long[] childrenHandles= STPObject.handles(children);
        return new Expr(STPJNI.vc_andExprN(handle, childrenHandles, children.length));
    }

    public Expr orExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_orExpr(handle, left.handle, right.handle));
    }
    
    public Expr orExprN(Expr[] children)
    {
        long[] childrenHandles= STPObject.handles(children);
        return new Expr(STPJNI.vc_orExprN(handle, childrenHandles, children.length));
    }
    
    public Expr impliesExpr(Expr hyp, Expr conc)
    {
        return new Expr(STPJNI.vc_impliesExpr(handle, hyp.handle, conc.handle));
    }
    
    public Expr iffExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_iffExpr(handle, left.handle, right.handle));
    }
    
    /**
     * The output type of iteExpr can be Boolean (formula-level ite)
     * or bit-vector (word-level ite) 
     */
    public Expr iteExpr(Expr conditional, Expr ifthenpart, Expr elsepart)
    {
        return new Expr(STPJNI.vc_iteExpr(handle, conditional.handle, ifthenpart.handle, elsepart.handle));
    }
    
    /** Boolean to single bit BV Expression */
    public Expr boolToBVExpr(Expr form)
    {
        return new Expr(STPJNI.vc_boolToBVExpr(handle, form.handle));
    }

    // Arrays
    
    /**  Create an expression for the value of array at the given index */
    public Expr readExpr(Expr array, Expr index)
    {
        return new Expr(STPJNI.vc_readExpr(handle, array.handle, index.handle));
    }

    /** Array update; equivalent to "array WITH [index] := newValue" */
    public Expr writeExpr(Expr array, Expr index, Expr newValue)
    {
        return new Expr(STPJNI.vc_writeExpr(handle, array.handle, index.handle, newValue.handle));
    }
    
    // Expr I/O

    /** Prints 'e' to stdout. */
    public void printExpr(Expr e)
    {
        STPJNI.vc_printExpr(handle, e.handle);
    }

    //! Prints 'e' to malloc'd buffer '*buf'.  Sets '*len' to the length of 
    //  the buffer. It is the responsibility of the caller to free the buffer.
    //TODO
    //public void printExprToBuffer(int/*Expr*/ e, char **buf, unsigned long * len);

    /** Prints counterexample to stdout. */
    public void printCounterExample()
    {
        STPJNI.vc_printCounterExample(handle);
    }

    /** Prints variable declarations to stdout. */
    public void printVarDecls()
    {
        STPJNI.vc_printVarDecls(handle);
    }

    /** Prints asserts to stdout. The flag simplify_print must be set to
     * true if you wish simplification to occur dring printing. It must be
     *  set to false otherwise
     */
    public void printAsserts(boolean simplify_print)
    {
        STPJNI.vc_printAsserts(handle, simplify_print ? 1: 0);
    }

    /** Prints the state of the query to malloc'd buffer '*buf' and
      * stores ! the length of the buffer to '*len'.  It is the
      * responsibility of the caller to free the buffer. The flag
      * simplify_print must be set to "1" if you wish simplification to
      * occur dring printing. It must be set to "0" otherwise*/
    //TODO
    //public void printQueryStateToBuffer(int/*Expr*/ e, char **buf, unsigned long *len, int simplify_print);

    //! Similar to printQueryStateToBuffer()
    //TODO
    //public void printCounterExampleToBuffer(char **buf,unsigned long *len);

    /** Prints query to stdout. */
    public void printQuery()
    {
        STPJNI.vc_printQuery(handle);
    }

    /////////////////////////////////////////////////////////////////////////////
    // Context-related methods                                                 //
    /////////////////////////////////////////////////////////////////////////////
    
    /** Assert a new formula in the current context.  
        The formula must have Boolean type. 
     */
    public void assertFormula(Expr e)
    {
        STPJNI.vc_assertFormula(handle, e.handle);
    }    
    
    /** Simplify e with respect to the current context */
    public Expr simplify(Expr e)
    {
      return new Expr(STPJNI.vc_simplify(handle, e.handle));   
    }

    /** Check validity of e in the current context. e must be a FORMULA.
     *
     * if returned 0 then input is INVALID. 
     *
     * if returned 1 then input is VALID.
     *
     * if returned 2 then ERROR.
     */
    public int query(Expr e)
    {
        return STPJNI.vc_query(handle, e.handle);
    }
    
    /** Return the counterexample after a failed query. */
    public Expr getCounterExample(Expr e)
    {
        return new Expr(STPJNI.vc_getCounterExample(handle, e.handle));
    }

    /**
     *  get size of counterexample, i.e. the number of variables/array
     *  locations in the counterexample.
     */
    public long counterexample_size()
    {
        return STPJNI.vc_counterexample_size(handle);
    }
    
    /** Checkpoint the current context and increase the scope level */
    public void push()
    {
        STPJNI.vc_push(handle);
    }
    
    /** Restore the current context to its state at the last checkpoint */
    public void pop()
    {
        STPJNI.vc_pop(handle);
    }

    /**************************/
    /* BIT VECTOR OPERATIONS  */
    /**************************/
    public Type bvType(int no_bits)
    {
        return new Type(STPJNI.vc_bvType(handle, no_bits));
    }
    
    public Type bv32Type()
    {
        return new Type(STPJNI.vc_bv32Type(handle));
    }
    
    public Expr bvConstExprFromStr(String binary_repr)
    {
        return new Expr(STPJNI.vc_bvConstExprFromStr(handle, binary_repr));
    }
    
    public Expr bvConstExprFromInt(int n_bits, int value)
    {
        //TODO only the bottom 32bits can be used - check that 
        return new Expr(STPJNI.vc_bvConstExprFromInt(handle, n_bits, value));
    }
    
    //TODO public int/*Expr*/ bvConstExprFromLL(int n_bits, unsigned long long value);
    
    public Expr bv32ConstExprFromInt(int value)
    {
        //TODO only the bottom 32bits can be used - check that 
        return new Expr(STPJNI.vc_bv32ConstExprFromInt(handle, value));        
    }
    
    public Expr bvConcatExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvConcatExpr(handle, left.handle, right.handle));
    }
    
    public Expr bvPlusExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvPlusExpr(handle, n_bits, left.handle, right.handle));
    }
    
    public Expr bv32PlusExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bv32PlusExpr(handle, left.handle, right.handle));
    }
    
    public Expr bvMinusExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvMinusExpr(handle, n_bits, left.handle, right.handle));
    }

    public Expr bv32MinusExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bv32PlusExpr(handle, left.handle, right.handle));
    }
    
    public Expr bvMultExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvMultExpr(handle, n_bits, left.handle, right.handle));
    }

    public Expr bv32MultExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bv32MultExpr(handle, left.handle, right.handle));
    }

    /** left divided by right i.e. left/right */
    public Expr bvDivExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvDivExpr(handle, n_bits, left.handle, right.handle));
    }
    
    /** left modulo right i.e. left%right */
    public Expr bvModExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvModExpr(handle, n_bits, left.handle, right.handle));
    }    
    
    /** signed left divided by right i.e. left/right */
    public Expr sbvDivExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvDivExpr(handle, n_bits, left.handle, right.handle));
    }    
    
    /** signed left modulo right i.e. left%right */
    public Expr sbvModExpr(int n_bits, Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvModExpr(handle, n_bits, left.handle, right.handle));
    }    
        
    public Expr bvLtExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvLtExpr(handle, left.handle, right.handle));
    }    

    public Expr bvLeExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvLeExpr(handle, left.handle, right.handle));
    }    

    public Expr bvGtExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvGtExpr(handle, left.handle, right.handle));
    }    
    
    public Expr bvGeExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvGeExpr(handle, left.handle, right.handle));
    }    
    
    public Expr sbvLtExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvLtExpr(handle, left.handle, right.handle));
    }    

    public Expr sbvLeExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvLeExpr(handle, left.handle, right.handle));
    }    

    public Expr sbvGtExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvGtExpr(handle, left.handle, right.handle));
    }    

    public Expr sbvGeExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_sbvGeExpr(handle, left.handle, right.handle));
    }    
    
    public Expr bvUMinusExpr(Expr child)
    {
        return new Expr(STPJNI.vc_bvUMinusExpr(handle, child.handle));
    }    

    /** bitwise operations: these are terms not formulas */  
    public Expr bvAndExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvAndExpr(handle, left.handle, right.handle));
    }    

    public Expr bvOrExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvOrExpr(handle, left.handle, right.handle));
    }    

    public Expr bvXorExpr(Expr left, Expr right)
    {
        return new Expr(STPJNI.vc_bvXorExpr(handle, left.handle, right.handle));
    }    

    public Expr bvNotExpr(Expr child)
    {
        return new Expr(STPJNI.vc_bvNotExpr(handle, child.handle));
    }    

    public Expr bvLeftShiftExpr(int sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bvLeftShiftExpr(handle, sh_amt, child.handle));
    }    
    
    public Expr bvRightShiftExpr(int sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bvRightShiftExpr(handle, sh_amt, child.handle));
    }    
    
    /** Same as bvLeftShift only that the answer in 32 bits long */
    public Expr bv32LeftShiftExpr(int sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bv32LeftShiftExpr(handle, sh_amt, child.handle));
    }    
    
    /** Same as bvRightShift only that the answer in 32 bits long */
    public Expr bv32RightShiftExpr(int sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bv32RightShiftExpr(handle, sh_amt, child.handle));
    }    
    
    public Expr bvVar32LeftShiftExpr(Expr sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bvVar32LeftShiftExpr(handle, sh_amt.handle, child.handle));
    }    
    
    public Expr bvVar32RightShiftExpr(Expr sh_amt, Expr child)
    {
        return new Expr(STPJNI.vc_bvVar32RightShiftExpr(handle, sh_amt.handle, child.handle));
    }    
    
    public Expr bvVar32DivByPowOfTwoExpr(Expr child, Expr rhs)
    {
        return new Expr(STPJNI.vc_bvVar32DivByPowOfTwoExpr(handle, child.handle, rhs.handle));
    }    

    public Expr bvExtract(Expr child, int high_bit_no, int low_bit_no)
    {
        return new Expr(STPJNI.vc_bvExtract(handle, child.handle, high_bit_no, low_bit_no));
    }    
    
    /** accepts a bitvector and position, and returns a boolean
     * corresponding to that position. More precisely, it return the
     * equation (x[bit_no:bit_no] = 0)
     * FIXME  = 1 ?
     */
    public Expr bvBoolExtract(Expr x, int bit_no)
    {
        return new Expr(STPJNI.vc_bvBoolExtract(handle, x.handle, bit_no));
    }    

    public Expr bvSignExtend(Expr child, int nbits)
    {
        return new Expr(STPJNI.vc_bvSignExtend(handle, child.handle, nbits));
    }    

    /*C pointer support:  C interface to support C memory arrays in CVCL */
    public Expr bvCreateMemoryArray(String arrayName)
    {
        return new Expr(STPJNI.vc_bvCreateMemoryArray(handle, arrayName));
    }    
    
    public Expr bvReadMemoryArray(Expr array, Expr byteIndex, int numOfBytes)
    {
        return new Expr(STPJNI.vc_bvReadMemoryArray(handle, array.handle, byteIndex.handle, numOfBytes));
    }    

    public Expr bvWriteToMemoryArray(Expr array, Expr  byteIndex, Expr element, int numOfBytes)
    {
        return new Expr(STPJNI.vc_bvWriteToMemoryArray(handle, array.handle, byteIndex.handle, element.handle, numOfBytes));
    }    

    /* Register the given error handler to be called for each fatal error.*/
    //TODO
    //public void registerErrorHandler(void (*error_hdlr)(const char* err_msg));

    public long getHashQueryStateToBuffer(Expr query)
    {
        return STPJNI.vc_getHashQueryStateToBuffer(handle, query.handle);
    }

    //Get the whole counterexample from the current context
    public WholeCounterExample getWholeCounterExample()
    {
        return new WholeCounterExample(STPJNI.vc_getWholeCounterExample(handle));
    }

    //Get the value of a term expression from the CounterExample
    public Expr getTermFromCounterExample(Expr e, WholeCounterExample c)
    {
        return new Expr(STPJNI.vc_getTermFromCounterExample(handle, e.handle, c.handle));
    }

    /** 
     r  : switch refinement off (optimizations are ON by default)
     w  : switch wordlevel solver off (optimizations are ON by default)
     a  : switch optimizations off (optimizations are ON by default)
     s  : print function statistics
     v  : print nodes 
     c  : construct counterexample
     d  : check counterexample
     p  : print counterexample
     h  : help
     */
    public static void setFlags(char c)
    {
        STPJNI.vc_setFlags(c);
    }
}
