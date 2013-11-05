/*
 * Context.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl;

import java.util.*;

import org.jakstab.rtl.expressions.*;

/**
 * A context used for evaluating expressions.
 * 
 * @author Johannes Kinder
 */
public class Context {

	private Map<Writable, RTLExpression> substitutions;
	private Map<Writable, RTLExpression> assignments;

	public Context() {
		this.substitutions = new HashMap<Writable, RTLExpression>();
		this.assignments = new LinkedHashMap<Writable, RTLExpression>();
	}
	
	/**
	 * Copy constructor.
	 * 
	 * @param proto
	 */
	public Context(Context proto) {
		this();
		substitutions.putAll(proto.substitutions);
		assignments.putAll(proto.assignments);
	}
	
	/**
	 * Substitutes a variable or memory location with another expression in this context.
	 * 
	 * @param w the variable or memory location to substitute
	 * @param expr the substitute
	 */
	public void substitute(Writable w, RTLExpression expr) {
		assert (!(w instanceof RTLBitRange));
		this.substitutions.put(w, expr);
	}
	
	/**
	 * Assigns a variable or memory location with a value in this context. 
	 */
	public void addAssignment(Writable w, RTLExpression expr) {
		assert (!(w instanceof RTLBitRange));
		this.assignments.put(w, expr);
	}
	
	public boolean removeAssignment(Writable var) {
		return this.assignments.remove(var) != null ? true : false;
	}
	
	public boolean removeAssignment(SetOfVariables var) {
		return this.assignments.keySet().removeAll(var);
	}
	
	/**
	 * Returns the substitute for a specific variable or memory location 
	 * in this context. If there is no substitute, returns the parameter.
	 * 
	 * @param w the variable or memory location to be queried
	 * @return the substitute of w in this context
	 */
	public RTLExpression getSubstitution(Writable w) {
		RTLExpression result = substitutions.get(w);
		if (result != null)
			return result;
		else
			return w;
	}
	
	/**
	 * Returns the value assigned to a variable or memory location 
	 * in this context.
	 * 
	 * @param w the variable or memory location
	 * @return the assigned value for w, or null if there is no value assigned
	 */
	public RTLExpression getAssignment(Writable w) {
		RTLExpression result = assignments.get(w);
		if (result != null)
			return result;
		else
			return w;
	}
	
	public Map<Writable, RTLExpression> getAssignments() {
		return assignments;
	}
}
