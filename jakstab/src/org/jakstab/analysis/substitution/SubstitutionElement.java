/*
 * SubstitutionElement.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.substitution;

import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class SubstitutionElement implements AbstractValue {

	public static SubstitutionElement TOP = new SubstitutionElement(null);
	public static SubstitutionElement BOT = new SubstitutionElement(null);
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SubstitutionElement.class);
	
	private final RTLExpression expression;
	
	public SubstitutionElement(RTLExpression e) {
		expression = e;
	}

	public RTLExpression getExpression() {
		return expression;
	}

	/*
	 * @see org.jakstab.analysis.AbstractValue#concretize()
	 */
	@Override
	public Set<RTLNumber> concretize() {
		if (expression instanceof RTLNumber) {
			return Collections.singleton((RTLNumber)expression);
		} else {
			// the "full" set
			return RTLNumber.ALL_NUMBERS;
		}
	}

	/*
	 * @see org.jakstab.analysis.AbstractValue#join(org.jakstab.analysis.LatticeElement)
	 */
	@Override
	public SubstitutionElement join(LatticeElement l) {
		if (l.isBot()) return this;
		SubstitutionElement other = (SubstitutionElement)l;
		if (this.isBot()) return other;
		if (expression.equals(other.getExpression())) return this;
		return TOP;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#isBot()
	 */
	@Override
	public boolean isBot() {
		return this == BOT;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#isTop()
	 */
	@Override
	public boolean isTop() {
		return this == TOP;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#lessOrEqual(org.jakstab.analysis.LatticeElement)
	 */
	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (l.isTop() || this.isBot()) return true;
		if (isTop() || l.isBot()) return false;
		SubstitutionElement other = (SubstitutionElement)l;
		if (expression.equals(other.getExpression())) return true;
		return false;
	}

	@Override
	public String toString() {
		return expression.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((expression == null) ? 0 : expression.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		SubstitutionElement other = (SubstitutionElement) obj;
		if (expression == null) {
			if (other.expression != null)
				return false;
		} else if (!expression.equals(other.expression))
			return false;
		return true;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return (expression instanceof RTLNumber);
	}
}
