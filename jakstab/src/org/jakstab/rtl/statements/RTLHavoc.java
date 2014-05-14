/*
 * RTLHavoc.java - This file is part of the Jakstab project.
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

import java.util.Collections;
import java.util.Set;

import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Logger;

/**
 * This havoc statements is semantically equivalent to a nondet assignment followed by 
 * an assume, but gives the analysis a hint that it should split states.
 * 
 * @author Johannes Kinder
 */
public class RTLHavoc extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLHavoc.class);

	private RTLVariable var;
	private RTLExpression max;

	public RTLHavoc(RTLVariable var, RTLExpression max) {
		this.var = var;
		this.max = max;
	}

	@Override
	protected SetOfVariables initDefinedVariables() {
		return var.getDefinedVariablesOnWrite();
	}

	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return Collections.emptySet();
	}

	@Override
	protected SetOfVariables initUsedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public RTLStatement evaluate(Context context) {
		// remove all killed assignments from the context
		context.removeAssignment(var);
		var = (RTLVariable)var.evaluate(context);
		max = max.evaluate(context);
		return this;
	}

	public RTLVariable getVariable() {
		return var;
	}

	public RTLExpression getMaximum() {
		return max;
	}

	@Override
	public String toString() {
		return "havoc(" + var + "); assume(" + var + " u<= " + max + ")";
	}

}
