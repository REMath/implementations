/*
 * RTLStatement.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.statements;

import java.util.Set;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.ssl.Architecture;

public interface RTLStatement extends Comparable<RTLStatement>, StateTransformer {

	public void setNextLabel(Location nextLabel);

	public Location getNextLabel();
	
	/**
	 * Generic accept method for an statement visitor to support the
	 * visitor pattern. Calls the appropriate visit method in visitor
	 * and passes through its return value of parameterized type T.
	 * 
	 * @param <T> the return type of the visit method.
	 * @param visitor the visitor being called.
	 * @return the return value of the correspoinding visit method.
	 */
	public <T> T accept(StatementVisitor<T> visitor);

	/**
	 * Returns this statement evaluated in the given context. 
	 * Evaluation may change the type of all substatements and expressions, 
	 * and may reduce or increase the total number of objects. Only statements
	 * are actually modified, embedded RTLExpressions are copied on change to
	 * preserve their immutable property. 
	 * 
	 * @param context the evaluation context, used for variable assignments and 
	 * 				  information propagation.
	 * @return An evaluated copy of this statement
	 */
	public RTLStatement evaluate(Context context);

	/**
	 * Returns whether this statement has already been instantiated, that is, whether
	 * it is not a template but a regular statement.
	 * 
	 * @return true if the statement has been instantiated, false if it is a template.
	 */
	public boolean isInstantiated();

	/**
	 * Returns the variables defined in this statement. At the current state of
	 * the implementation, this includes only registers and flags, not memory
	 * locations.
	 * 
	 * @return A set containing all defined variables of this statement.
	 */
	public SetOfVariables getDefinedVariables();

	/**
	 * Returns the variables used by this statement. At the current state of
	 * the implementation, this includes only registers and flags, not memory
	 * locations.
	 * 
	 * @return A set containing all used variables of this statement.
	 */
	public SetOfVariables getUsedVariables();
	
	/**
	 * Returns the set of memory locations used in this statement.
	 * 
	 * @return the set of used memory locations.
	 */
	public Set<RTLMemoryLocation> getUsedMemoryLocations();
	
	/**
	 * Returns the label of this statement consisting of its virtual 
	 * address and RTL-index.
	 * 
	 * @return the label of this statement.
	 */
	public Location getLabel();

	/**
	 * Creates a label for this statement based on address and RTL-index.
	 *  
	 * @param addr the new virtual address of this statement.
	 * @param rtlId the new RTL index of this statement.
	 */
	public void setLabel(AbsoluteAddress addr, int rtlId);
	
	/**
	 * Sets the label of this instruction.
	 * 
	 * @param label the label for this statement.
	 */
	public void setLabel(Location label);

	/**
	 * Returns the virtual address of this statement.
	 * 
	 * @return This statement's virtual address.
	 */
	public AbsoluteAddress getAddress();
	
	/**
	 * Performs type inference on all expressions used in this statement
	 * which have an unknown bit width.  
	 * @param arch TODO
	 * 
	 * @throws TypeInferenceException if a bit width conflict is detected.  
	 */
	public void inferTypes(Architecture arch) throws TypeInferenceException;

	/**
	 * Returns a shallow copy this statement. All expressions are immutable, 
	 * so shared expressions in the copy should not be a problem. 
	 * 
	 * @return a copy of this statement.
	 */
	public RTLStatement copy();

}
