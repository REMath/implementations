/*
 * StatementVisitor.java - This file is part of the Jakstab project.
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

/**
 * A visitor interface for RTLStatements with support for return
 * values whose type is specified by the type parameter.
 *  
 * @author Johannes Kinder
 * @param <T> the return type of the visitor.
 */
public interface StatementVisitor<T> {

	T visit(RTLVariableAssignment stmt);
	T visit(RTLMemoryAssignment stmt);
	T visit(RTLGoto stmt);
	T visit(RTLAssume stmt);
	T visit(RTLAssert stmt);
	T visit(RTLSkip stmt);
	T visit(RTLHalt stmt);
	T visit(RTLAlloc stmt);
	T visit(RTLDealloc stmt);
	T visit(RTLUnknownProcedureCall stmt);
	T visit(RTLHavoc stmt);
	T visit(RTLMemset stmt);
	T visit(RTLMemcpy stmt);
	T visit(RTLDebugPrint stmt);

}
