/*
 * RTLExpression.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */

package org.jakstab.rtl.expressions;

import java.util.Set;

import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.ssl.Architecture;


/**
 * A class for immutable RTL expression objects. All changes are performed
 * solely on copies.
 *  
 * @author Johannes Kinder
 */
public interface RTLExpression extends BitVectorType {
	
	/**
	 * Generic accept method for an expression visitor to support the
	 * visitor pattern. Calls the appropriate visit method in visitor
	 * and passes through its return value of parameterized type T.
	 * 
	 * @param <T> the return type of the visit method.
	 * @param visitor the visitor being called.
	 * @return the return value of the correspoinding visit method.
	 */
	public <T> T accept(ExpressionVisitor<T> visitor);
	
	/**
	 * Returns a copy of this expression evaluated in the given context. 
	 * Evaluation may change the type of all subexpressions and may reduce 
	 * or increase the total number of objects.
	 * 
	 * @param context the evaluation context, used for variable assignments and 
	 * 				  information propagation.
	 * @return An evaluated copy of this expression
	 */
	public RTLExpression evaluate(Context context);
	
	/**
	 * Returns the set of variables which is contained in this expression. In this
	 * context, variables are only registers and flags, not memory locations.
	 * 
	 * @return the set of variables used in this expression
	 */
	public SetOfVariables getUsedVariables();
	
	/**
	 * Returns the set of memory locations used in this expression.
	 * 
	 * @return the set of used memory locations.
	 */
	public Set<RTLMemoryLocation> getUsedMemoryLocations();
	
	/**
	 * Performs type inference on all subexpressions of unknown bit width. Returns
	 * a new expression with inferred types.  
	 * @param arch TODO
	 * @param expectedBitWidth the bit width this expression is expected to have
	 * 
	 * @return a new expression guaranteed to be of the expected bit width.
	 * @throws TypeInferenceException if a bit width conflict is detected.  
	 */
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth) throws TypeInferenceException;
	
	/**
	 * Returns the total number of subexpressions of this expression, including the
	 * expression itself.
	 * 
	 * @return the size of this expression.
	 */
	public int size();
	
	/**
	 * Returns a string representation of this expression similar to toString(), but with
	 * all numbers in hexadecimal format. Used for memory addresses and jump targets.
	 * 
	 * @return a string representation of this expression.
	 */
	public String toHexString();

}
