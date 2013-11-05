/*
 * RTLConditionalExpression.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.expressions;

import java.util.Set;

import org.jakstab.rtl.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * An if-then-else expression similar to the C syntax of "condition ? trueExpression : falseExpression".
 * 
 * @author Johannes Kinder
 */
public class RTLConditionalExpression extends AbstractRTLExpression implements RTLExpression {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(RTLConditionalExpression.class);

	protected Set<RTLMemoryLocation> usedMemoryLocations = null;

	private final RTLExpression condition;
	private final RTLExpression trueExpression;
	private final RTLExpression falseExpression;
	private final int size;

	/**
	 * @param condition
	 * @param trueExpression
	 * @param falseExpression
	 */
	protected RTLConditionalExpression(RTLExpression condition,
			RTLExpression trueExpression, RTLExpression falseExpression) {
		super();
		this.condition = condition;
		this.trueExpression = trueExpression;
		this.falseExpression = falseExpression;
		this.size = 1 + condition.size() + trueExpression.size() + falseExpression.size();
	}

	/**
	 * @return the condition
	 */
	public RTLExpression getCondition() {
		return condition;
	}

	/**
	 * @return the trueExpression
	 */
	public RTLExpression getTrueExpression() {
		return trueExpression;
	}

	/**
	 * @return the falseExpression
	 */
	public RTLExpression getFalseExpression() {
		return falseExpression;
	}

	@Override
	public String toString() {
		return "(" + condition.toString() + " ? " + trueExpression.toString() + 
		" : " + falseExpression.toString() + ")";
	}

	@Override
	public RTLExpression evaluate(Context context) {
		RTLExpression evaldCondition = this.condition.evaluate(context);
		
		if (evaldCondition.equals(ExpressionFactory.FALSE)) return this.falseExpression.evaluate(context);
		else if (evaldCondition.equals(ExpressionFactory.TRUE)) return this.trueExpression.evaluate(context);
		
		assert !(evaldCondition instanceof RTLNumber) : "Numeric condition result is neither TRUE nor FALSE but " + evaldCondition;
		
		RTLExpression evaldTrue = trueExpression.evaluate(context);
		RTLExpression evaldFalse = falseExpression.evaluate(context);
		
		// Collapse "(x == y) ? 1<1> : 0<1>" to (x == y)
		if (evaldTrue.equals(ExpressionFactory.TRUE) && evaldFalse.equals(ExpressionFactory.FALSE)) {
			return evaldCondition;
		} else if (evaldTrue.equals(ExpressionFactory.FALSE) && evaldFalse.equals(ExpressionFactory.TRUE)) {
				return ExpressionFactory.createOperation(Operator.NOT, evaldCondition);
		}
		
		return ExpressionFactory.createConditionalExpression(evaldCondition, evaldTrue, evaldFalse);
	}

	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			usedVariables.addAll(condition.getUsedVariables());
			usedVariables.addAll(trueExpression.getUsedVariables());
			usedVariables.addAll(falseExpression.getUsedVariables());
		}
		return usedVariables;
	}
	
	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		if (usedMemoryLocations == null) {
			usedMemoryLocations = new FastSet<RTLMemoryLocation>();
			usedMemoryLocations.addAll(condition.getUsedMemoryLocations());
			usedMemoryLocations.addAll(trueExpression.getUsedMemoryLocations());
			usedMemoryLocations.addAll(falseExpression.getUsedMemoryLocations());
		}
		return usedMemoryLocations;
	}

	@Override
	public int size() {
		return size;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) return false;
		RTLConditionalExpression other = (RTLConditionalExpression)obj; 
		return other.condition.equals(condition) && 
		other.trueExpression.equals(trueExpression) && 
		other.falseExpression.equals(falseExpression);
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 17 + condition.hashCode() + trueExpression.hashCode() + falseExpression.hashCode();
	}

	@Override
	public int getBitWidth() {
		return trueExpression.getBitWidth();
	}

	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		RTLExpression typedCondition = condition.inferBitWidth(arch, 1);
		RTLExpression typedTrueExpression = trueExpression.inferBitWidth(arch, expectedBitWidth);
		RTLExpression typedFalseExpression = falseExpression.inferBitWidth(arch, expectedBitWidth);
		if (typedCondition != condition || typedTrueExpression != trueExpression 
				|| typedFalseExpression != falseExpression)
			return ExpressionFactory.createConditionalExpression(
					typedCondition, typedTrueExpression, typedFalseExpression);
		else return this;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
