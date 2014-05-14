/*
 * Solver.java - This file is part of the Jakstab project.
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
package org.jakstab.solver;

import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.solver.yices.YicesSolver;
import org.jakstab.util.Logger;

/**
 * A generic interface to SMT solvers, represents a logical context that
 * can be updated with assertions and checked for satisfiability.
 * 
 * @author Johannes Kinder
 */
public abstract class Solver {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(Solver.class);

	/**
	 * Creates a new solver context.
	 * 
	 * @return a new Solver instance, currently always of type YicesSolver
	 */
	public static Solver createSolver() {
		return new YicesSolver();
	}
	
	/**
	 * Checks satisfiability of a single formula.
	 * 
	 * @param f the formula to check
	 * @return true if the formula is satisfiable, false otherwise
	 */
	public static boolean isSatisfiable(RTLExpression f) {
		YicesSolver ys = new YicesSolver();
		ys.addAssertion(f);
		return ys.isSatisfiable();
	}
	
	public static boolean isUnsatisfiable(RTLExpression f) {
		return !isSatisfiable(f);
	}
	
	public static boolean isValid(RTLExpression f) {
		return isUnsatisfiable(ExpressionFactory.createNot(f));
	}

	/**
	 * Adds a formula to the logical context. All assertions
	 * are evaluated in conjunction.
	 *   
	 * @param f the formula to add
	 */
	public abstract void addAssertion(RTLExpression f);

	/**
	 * Checks if the logical context is satisfiable, i.e., if there 
	 * exists a variable assignment such that each assertion evaluates
	 * to the bitvector 1 of size 1 (the RTLExpression TRUE).   
	 * 
	 * @return true if the context is satisfiable, false otherwise
	 */
	public abstract boolean isSatisfiable();
	
	public boolean isUnsatisfiable() {
		return !isSatisfiable();
	}
	
	public abstract void push();
	
	public abstract void pop();

	protected Solver() {
	}
}
