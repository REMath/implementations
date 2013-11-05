/*
 * RTLDebugPrint.java - This file is part of the Jakstab project.
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
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.util.Logger;

/**
 * Statement that causes Jakstab to print debug messages.
 * 
 * @author Johannes Kinder
 */
public class RTLDebugPrint extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLDebugPrint.class);
	
	private final String message;
	private final RTLExpression expression;
	
	public RTLDebugPrint(String message, RTLExpression expression) {
		this.message = message;
		this.expression = expression;
	}
	
	@Override
	public RTLStatement evaluate(Context context) {
		return this;
	}

	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	protected SetOfVariables initUsedVariables() {
		return expression.getUsedVariables();
	}
	
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return Collections.emptySet();
	}

	public String getMessage() {
		return message;
	}

	public RTLExpression getExpression() {
		return expression;
	}

	@Override
	public String toString() {
		return "DebugPrint(" + message + ", " + expression + ")";
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
