/*
 * RTLDealloc.java - This file is part of the Jakstab project.
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
 * Deallocates (frees) a heap object.
 * 
 * @author Johannes Kinder
 */
public class RTLDealloc extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLDealloc.class);
	
	private RTLExpression pointer;

	public RTLDealloc(RTLExpression pointer) {
		super();
		this.pointer = pointer;
	}

	public RTLExpression getPointer() {
		return pointer;
	}

	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return Collections.emptySet();
	}

	@Override
	protected SetOfVariables initUsedVariables() {
		return pointer.getUsedVariables();
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public RTLStatement evaluate(Context context) {
		pointer = pointer.evaluate(context);
		return this;
	}

	@Override
	public String toString() {
		return "dealloc(" + pointer + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((pointer == null) ? 0 : pointer.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		RTLDealloc other = (RTLDealloc) obj;
		if (pointer == null) {
			if (other.pointer != null)
				return false;
		} else if (!pointer.equals(other.pointer))
			return false;
		return true;
	}
	
}
