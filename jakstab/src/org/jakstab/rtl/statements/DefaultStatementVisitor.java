/*
 * DefaultStatementVisitor.java - This file is part of the Jakstab project.
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

import org.jakstab.util.Logger;

/**
 * Default statement visitor that calls a default implementation for every 
 * type of statement. When the default behavior is not overridden, throws
 * UnsupportedOperationException. 
 * 
 * @author Johannes Kinder
 */
public abstract class DefaultStatementVisitor<T> implements StatementVisitor<T> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(DefaultStatementVisitor.class);

	@Override
	public T visit(RTLVariableAssignment stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLMemoryAssignment stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLGoto stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLAssume stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLAssert stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLSkip stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLHalt stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLAlloc stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLDealloc stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLUnknownProcedureCall stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLHavoc stmt) {
		return visitDefault(stmt);
	}
	
	@Override
	public T visit(RTLMemset stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLMemcpy stmt) {
		return visitDefault(stmt);
	}

	@Override
	public T visit(RTLDebugPrint stmt) {
		return visitDefault(stmt);
	}

	/**
	 * Called by the default implementations of the visit methods. Override this 
	 * to provide a default implementation for statements.
	 * @param stmt the RTLStatement passed to the visit method. 
	 * @return An object of the parameter type.
	 */
	protected T visitDefault(RTLStatement stmt) {
		throw new UnsupportedOperationException("Visitor does not support statements of type " + 
				stmt.getClass().getSimpleName() + "!");
	}
	
}
