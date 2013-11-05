/*
 * RTLAssume.java - This file is part of the Jakstab project.
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

import java.util.Set;

import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Logger;

/**
 * Assumptions are generated during control flow reconstruction and encode conditions for
 * control flow branches.
 * 
 * @author Johannes Kinder
 */
public class RTLAssume extends AbstractRTLStatement implements RTLStatement {
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLAssume.class);
	
	private RTLExpression assumption;
	private RTLGoto source;

	/**
	 * @param assumption
	 */
	public RTLAssume(RTLExpression assumption, RTLGoto source) {
		super();
		this.assumption = assumption;
		this.source = source;
	}
	
	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return assumption.getUsedMemoryLocations();
	}

	@Override
	protected SetOfVariables initUsedVariables() {
		return assumption.getUsedVariables();
	}
	
	public RTLExpression getAssumption() {
		return assumption;
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public RTLStatement evaluate(Context context) {
		invalidateCache();
		assumption = assumption.evaluate(context);
		ExpressionSimplifier simplifier = ExpressionSimplifier.getInstance();
		assumption = simplifier.simplify(assumption);

		/*if (assumption.equals(ExpressionFactory.getInstance().TRUE)) 
			return null;*/
		return this;
	}

	@Override
	public String toString() {
		return "assume " + assumption.toString();
	}
	
	public RTLGoto getSource() {
		return source;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((assumption == null) ? 0 : assumption.hashCode());
		result = prime * result + ((source == null) ? 0 : source.hashCode());
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
		RTLAssume other = (RTLAssume) obj;
		if (assumption == null) {
			if (other.assumption != null)
				return false;
		} else if (!assumption.equals(other.assumption))
			return false;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		return true;
	}

}
