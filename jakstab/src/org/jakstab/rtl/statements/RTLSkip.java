/*
 * RTLSkip.java - This file is part of the Jakstab project.
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
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.util.Logger;

/**
 * No operation, do nothing, just fall through to the next statement.
 * 
 * @author Johannes Kinder
 */
public class RTLSkip extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(RTLSkip.class);

	
	public RTLSkip() {
	}
	
	/*
	 * @see org.jakstab.rtl.RTLStatement#evaluate(org.jakstab.rtl.Context)
	 */
	@Override
	public RTLStatement evaluate(Context context) {
		return this;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#initDefinedVariables()
	 */
	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#initUsedVariables()
	 */
	@Override
	protected SetOfVariables initUsedVariables() {
		return SetOfVariables.EMPTY_SET;
	}
	
	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return Collections.emptySet();
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "skip";
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
