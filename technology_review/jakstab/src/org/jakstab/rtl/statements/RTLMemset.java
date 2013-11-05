/*
 * RTLMemset.java - This file is part of the Jakstab project.
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
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class RTLMemset extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLMemset.class);
	
	private RTLExpression destination;
	private RTLExpression value;
	private RTLExpression count;
	
	public RTLMemset(RTLExpression dest, RTLExpression val, RTLExpression cnt) {
		destination = dest;
		value = val;
		count = cnt;
	}

	public RTLExpression getDestination() {
		return destination;
	}

	public RTLExpression getValue() {
		return value;
	}

	public RTLExpression getCount() {
		return count;
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
		SetOfVariables usedVariables = new SetOfVariables();
		usedVariables.addAll(destination.getUsedVariables());
		usedVariables.addAll(value.getUsedVariables());
		usedVariables.addAll(count.getUsedVariables());
		return usedVariables;
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public RTLStatement evaluate(Context context) {
		RTLExpression evaldDestination = destination.evaluate(context);
		RTLExpression evaldValue = value.evaluate(context);
		RTLExpression evaldCount = count.evaluate(context);
		
		destination = evaldDestination;
		value = evaldValue;
		count = evaldCount;
		
		return this;
	}
	
	@Override
	public void inferTypes(Architecture arch) throws TypeInferenceException {
		destination = destination.inferBitWidth(arch, arch.getAddressBitWidth());
		count = count.inferBitWidth(arch, arch.getAddressBitWidth());
	}

	@Override
	public String toString() {
		return "memset(" + destination + ", " + value + ", " + count + ")";
	}

}
