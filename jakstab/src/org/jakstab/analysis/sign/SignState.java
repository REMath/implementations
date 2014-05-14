/*
 * SignState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.sign;

import java.util.*;

import org.jakstab.analysis.*;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.*;

/**
 * @author Johannes Kinder
 */
public class SignState implements AbstractState {
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SignState.class);
	private static long maxStateId = 0;
	
	static final SignState TOP = new SignState();
	static final SignState BOT = new SignState((Map<RTLVariable, SignElement>)null);

	private Map<RTLVariable,SignElement> aVarVal;
	private final long stateId;
	
	
	SignState() {
		this (new HashMap<RTLVariable, SignElement>());
	}
	
	SignState(Map<RTLVariable,SignElement> aVarVal) {
		stateId = ++maxStateId;
		this.aVarVal = aVarVal;
	}
	
	/**
	 * Copy constructor
	 * 
	 * @param proto
	 */
	SignState(SignState proto) {
		this();
		aVarVal.putAll(proto.aVarVal);
	}
	
	/**
	 * Evaluates an expression in the context of this abstract state to
	 * an abstract value.
	 * 
	 * @param e the expression to be evaluated.
	 * @return the abstract value of the expression in the abstract state.
	 */
	protected SignElement abstractEval(RTLExpression e) {
		ExpressionVisitor<SignElement> visitor = new ExpressionVisitor<SignElement>() {
			
			//private ExpressionFactory ExpressionFactory = ExpressionFactory.getInstance();

			@Override
			public SignElement visit(RTLBitRange e) {
				return SignElement.TOP;
			}

			@Override
			public SignElement visit(RTLConditionalExpression e) {
				SignElement aTrue = e.getTrueExpression().accept(this);
				SignElement aFalse = e.getFalseExpression().accept(this);
				return aTrue.join(aFalse);
			}

			@Override
			public SignElement visit(RTLMemoryLocation m) {
				return SignElement.TOP;
			}

			@Override
			public SignElement visit(RTLNondet e) {
				return SignElement.TOP;
			}

			@Override
			public SignElement visit(RTLNumber e) {
				long v = e.longValue();
				if (v > 0) {
					return SignElement.POSITIVE;
				} else if (v < 0) {
					return SignElement.NEGATIVE;
				} else {
					return SignElement.ZERO;
				}
			}

			@Override
			public SignElement visit(RTLOperation e) {
				SignElement[] aOperands = new SignElement[e.getOperandCount()];
				boolean oneTop = false;
				boolean allPositiveOrZero = true;
				boolean allNegativeOrZero = true;
				boolean allZero = true;
				boolean oneZero = false;
				int negativeOperands = 0;

				for (int i=0; i<e.getOperandCount(); i++) {
					SignElement aOperand = e.getOperands()[i].accept(this);
					switch (aOperand) {
					case POSITIVE:
						allZero = false;
						allNegativeOrZero = false;
						break;
					case NEGATIVE:
						allZero = false;
						allPositiveOrZero = false;
						negativeOperands++;
						break;
					case ZERO:
						oneZero = true;
						break;
					case TOP:
						oneTop = true;
						allPositiveOrZero = false;
						allNegativeOrZero = false;
						allZero = false;
						break;
					default:
					}
					aOperands[i] = aOperand;
				}
				switch (e.getOperator()) {
				case PLUS:
					if (allPositiveOrZero) return SignElement.POSITIVE;
					else if (allNegativeOrZero) return SignElement.NEGATIVE;
					else if (allZero) return SignElement.ZERO;
					else return SignElement.TOP;
				case MUL:
					if (oneZero) return SignElement.ZERO;
					if (oneTop) return SignElement.TOP;
					if (negativeOperands % 2 == 0) return SignElement.POSITIVE;
					else return SignElement.NEGATIVE;
				default:
					return SignElement.TOP;
				}
				
			}

			@Override
			public SignElement visit(RTLSpecialExpression e) {
				return SignElement.TOP;
			}

			@Override
			public SignElement visit(RTLVariable e) {
				return getValue(e);
			}
			
		};
		
		return e.accept(visitor);
	}
	
	@Override
	public boolean isTop() {
		return this == TOP || (aVarVal != null && aVarVal.isEmpty());
	}

	@Override
	public boolean isBot() {
		return this == BOT;
	}
	
	void setValue(RTLVariable var, SignElement v) {
		if (v.isTop()) {
			aVarVal.remove(var);
		} else {
			aVarVal.put(var, v);
		}
	}
	
	public SignElement getValue(RTLVariable v) {
		if (isTop()) return SignElement.TOP;
		if (isBot()) return SignElement.BOT;
		
		if (aVarVal.containsKey(v)) return aVarVal.get(v);
		else return SignElement.TOP;
	}
	
	/*
	 * @see org.jakstab.analysis.AbstractState#join(org.jakstab.analysis.AbstractState)
	 */
	@Override
	public SignState join(LatticeElement l) {
		SignState other = (SignState)l;

		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;
		
		SignState result = new SignState();
		
		// Join variable valuations
		for (Map.Entry<RTLVariable,SignElement> entry : aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			SignElement v = entry.getValue();
			result.setValue(var, v.join(other.getValue(var)));
		}
		if (result.aVarVal.isEmpty()) return TOP;
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		SignState other = (SignState)l;

		if (other.isTop() || isBot()) return true;
		if (isTop() || other.isBot()) return false;
		
		// Check for every element in "other" if its value in "this" is less or equal 
		// than the value in "other". The elements not stored in the valuation maps 
		// of "other" are implicitly TOP and thus every value is less or equal than them.
		for (Map.Entry<RTLVariable,SignElement> entry : other.aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			SignElement v = entry.getValue();
			if (!getValue(var).lessOrEqual(v)) {
				//logger.info(var + ": " + getValue(var) + " is not less or equal to " + v);
				return false;
			}
		}
		
		return true;
	}
	
	@Override
	public String getIdentifier() {
		return Long.toString(stateId);
	}

	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		else if (isBot()) return Characters.BOT;
		else {
			StringBuilder res = new StringBuilder();
			boolean first = true;
			for (Map.Entry<RTLVariable, SignElement> entry : aVarVal.entrySet()) {
				if (!first) {
					res.append(", ");
				} else {
					first = false;
				}
				res.append(entry.getKey() + ": " + entry.getValue());
			}
			return res.toString();
		}
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			SignElement aValue = abstractEval(expressions[i]);
			// Only ZERO elements can be concretized to numbers
			cValues.set(i, Collections.singleton(
					aValue.equals(SignElement.ZERO) ? 
					ExpressionFactory.createNumber(0, expressions[i].getBitWidth()) : null));
		}

		return Sets.crossProduct(cValues);

	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}
	
	public RTLExpression getStateFormula() {

		RTLExpression result = null;
		
		for (Map.Entry<RTLVariable, SignElement> entry : aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			RTLExpression clause;
			switch(entry.getValue()) {
			case POSITIVE:
				clause = ExpressionFactory.createGreaterThan(var, ExpressionFactory.createNumber(0, var.getBitWidth()));
				break;
			case NEGATIVE:
				clause = ExpressionFactory.createLessThan(var, ExpressionFactory.createNumber(0, var.getBitWidth()));
				break;
			case ZERO:
				clause = ExpressionFactory.createEqual(var, ExpressionFactory.createNumber(0, var.getBitWidth()));
				break;
			default:
				clause = null;
			}
			if (clause != null) {
				if (result != null) {
					result = ExpressionFactory.createAnd(result, clause);
				} else {
					result = clause;
				}
			}
		}
		
		if (result == null) result = ExpressionFactory.TRUE;
		
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((aVarVal == null) ? 0 : aVarVal.hashCode());
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
		SignState other = (SignState) obj;
		if (aVarVal == null) {
			if (other.aVarVal != null)
				return false;
		} else if (!aVarVal.equals(other.aVarVal))
			return false;
		return true;
	}

}
