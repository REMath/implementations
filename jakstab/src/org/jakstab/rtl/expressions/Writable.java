/*
 * Writable.java - This file is part of the Jakstab project.
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


/**
 * An interface for expressions that can be the left hand side of
 * an assignment.
 * 
 * @author Johannes Kinder
 */
public interface Writable extends RTLExpression {
	
	/**
	 * Returns the variables which are read if this expression is
	 * used as the lefthandside of an assignment. This is a subset
	 * of getUsedVariables.
	 * 
	 * @return the variables used by this expression when it is 
	 *         written to.
	 */
	public SetOfVariables getUsedVariablesOnWrite();
	
	/**
	 * Returns the variables which are defined if this expression is
	 * used as the lefthandside of an assignment. This is a subset
	 * of getUsedVariables.
	 * 
	 * @return the variables defined by this expression when it is 
	 *         written to.
	 */
	public SetOfVariables getDefinedVariablesOnWrite();
	
	/**
	 * Returns the memory locations which are read if this expression is
	 * used as the lefthandside of an assignment. This is a subset
	 * of getUsedVariables.
	 * 
	 * @return the variables used by this expression when it is 
	 *         written to.
	 */
	public Set<RTLMemoryLocation> getUsedMemoryLocationsOnWrite();
	
	/**
	 * Returns the memory locations which are defined if this expression is
	 * used as the lefthandside of an assignment. This is a subset
	 * of getUsedVariables.
	 * 
	 * @return the variables defined by this expression when it is 
	 *         written to.
	 */
	public Set<RTLMemoryLocation> getDefinedMemoryLocationsOnWrite();
	
}
