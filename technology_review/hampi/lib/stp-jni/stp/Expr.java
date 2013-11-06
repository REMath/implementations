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

public class Expr extends STPObject{

    public Expr(long handle) {
        super(handle);
    }

    @Override
    public String toString() {
        return exprString();
    }
    
    /**
     * Return an int from a constant bitvector expression.
     */
    public int getBVInt()
    {
        return STPJNI.getBVInt(handle);
    }
    
    /**
     *  Return an unsigned int from a constant bitvector expression
     */
    public long getBVUnsigned()
    {
        return STPJNI.getBVUnsigned(handle);
    }
    
    //! Return an unsigned long long int from a constant bitvector expressions
    //TODO
    //public unsigned long long int getBVUnsignedLongLong(int/*Expr*/ e);
    
    /** return a string representation of the Expr e. */
    public String exprString()
    {
        return STPJNI.exprString(handle);
    }
    
    public Expr getChild(int i)
    {
        return new Expr(STPJNI.getChild(handle, i));
    }        
    
    /** 1.if input expr is TRUE then the function returns 1;
     
      2.if input expr is FALSE then function returns 0;
    
      3.otherwise the function returns -1
      */
    public int isBool(Expr e)
    {
        return STPJNI.vc_isBool(handle);
    }        

    /** deletes the expression e */
    public void DeleteExpr()
    {
        STPJNI.vc_DeleteExpr(handle);
    }

    /** get the kind of the expression */
    public exprkind_t getExprKind ()
    {
        return exprkind_t.values()[STPJNI.getExprKind(handle)];
    }

    /**  get the number of children nodes */
    public int getDegree ()
    {
        return STPJNI.getDegree(handle);
    }

    /** get the bv length */
    public int getBVLength()
    {
        return STPJNI.getBVLength(handle);
    }

    /** get expression type */
    public type_t getType ()
    {
        return type_t.values()[STPJNI.getType(handle)];
    }

    /** get value bit width */
    public int getVWidth ()
    {
        return STPJNI.getVWidth(handle);
    }
    
    /** get index bit width */
    public int getIWidth ()
    {
        return STPJNI.getIWidth(handle);
    }

    /** get name of expression. must be a variable. */
    public String exprName()
    {
        return STPJNI.exprName(handle);
    }
    
    /** get the node ID of an Expr. */
    public int getExprID ()
    {
        return STPJNI.getExprID(handle);
    }
}