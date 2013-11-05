/*
 * VariableValuation.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis;

import java.util.*;
import java.util.Map.Entry;

import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class VariableValuation<A extends AbstractValue> implements LatticeElement, Iterable<Map.Entry<RTLVariable, A>> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(VariableValuation.class);

	protected final TreeMap<RTLVariable,A> aVarVal;
	protected final AbstractValueFactory<A> valueFactory;

	protected VariableValuation(TreeMap<RTLVariable,A> aVarVal, 
			AbstractValueFactory<A> valueFactory) {
		this.aVarVal = aVarVal;
		this.valueFactory = valueFactory;
	}
	
	public VariableValuation(VariableValuation<A> proto) {
		this(new TreeMap<RTLVariable, A>(proto.aVarVal), 
				proto.valueFactory);
	}
	
	public VariableValuation(AbstractValueFactory<A> valueFactory) {
		this(new TreeMap<RTLVariable, A>(),
				valueFactory);
	}
	

	public A get(RTLVariable var) {
		A e = aVarVal.get(var);
		if (e != null) {
			return e;
		} else {
			// See if we can get the value from a covering register
			RTLBitRange asParent = ExpressionFactory.getRegisterAsParent(var);

			if (asParent != null && asParent.getOperand() instanceof RTLVariable) {
				RTLVariable parent = (RTLVariable)asParent.getOperand();
				// Recursive call for al -> ax -> eax 
				A parentVal = get(parent);
				assert parentVal != null;
				
				Collection<RTLNumber> cValues = new LinkedList<RTLNumber>();
				for (RTLNumber cVal : parentVal.concretize()) {
					if (cVal == null) {
						cValues = null;
						break;
					}
					Context ctx = new Context();
					ctx.addAssignment(parent, cVal);
					RTLExpression result = asParent.evaluate(ctx);
					cValues.add((RTLNumber)result);
				}
				if (cValues != null) {
					e = valueFactory.createAbstractValue(cValues);
					//logger.debug("Generated abstract value " + e + " for " + var + " from value " + parentVal + " of " + parent);
					return e;
				}
			}

			return valueFactory.createTop(var.getBitWidth());
		}
	}
	
	private void clearCovering(RTLVariable var) {
		for (RTLVariable covering : ExpressionFactory.coveringRegisters(var)) {
			aVarVal.remove(covering);
			//clearCovering(covering);
		}
	}
	
	private void clearCovered(RTLVariable var) {
		for (RTLVariable covered : ExpressionFactory.coveredRegisters(var)) {
			aVarVal.remove(covered);
			//clearCovered(covered);
		}
	}
	
	@SuppressWarnings("unchecked")
	public void set(RTLVariable var, A value) {
		
		RTLBitRange asParent = ExpressionFactory.getRegisterAsParent(var);

		// Set parent register - we only do this if the value to set represents 
		// a single concrete value. If we want to generalize this, we have to
		// build the cartesian product of concretizations
		if (asParent != null && asParent.getOperand() instanceof RTLVariable && 
				value.hasUniqueConcretization()) {
			RTLVariable parent = (RTLVariable)asParent.getOperand();
			A parentVal = get(parent);
			RTLNumber cRhs = value.concretize().iterator().next();

			Collection<RTLNumber> cValues = new LinkedList<RTLNumber>();
			for (RTLNumber cVal : parentVal.concretize()) {
				if (cVal == null) {
					cValues = null;
					break;
				}
				Context ctx = new Context();
				ctx.addAssignment(parent, cVal);
				RTLExpression result = asParent.applyInverse(cRhs).evaluate(ctx);
				cValues.add((RTLNumber)result);
			}
			if (cValues != null) {
				A e = valueFactory.createAbstractValue(cValues);
				//logger.debug("Setting parent " + parent + " of " + var + " to value " + e);
				set(parent, e);
				return;
			}
		}

		clearCovering(var);
		clearCovered(var);
		
		if (value.isTop()) {
			aVarVal.remove(var);
		} else {
			aVarVal.put(var, value);
		}
	}
	
	public void setTop(RTLVariable var) {
		clearCovering(var);
		clearCovered(var);

		aVarVal.remove(var);
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return aVarVal.isEmpty();
	}

	@SuppressWarnings("unchecked")
	@Override
	public VariableValuation<A> join(LatticeElement l) {
		VariableValuation<A> other = (VariableValuation<A>)l;
		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;

		VariableValuation<A> joinedValuation = new VariableValuation<A>(valueFactory);
		// Join variable valuations
		for (Map.Entry<RTLVariable,A> entry : aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			A value = entry.getValue();
			joinedValuation.set(var, (A)value.join(other.get(var)));
		}
				
		return joinedValuation;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (this == l) return true;
		VariableValuation<A> other = (VariableValuation<A>)l;
		if (other.isTop()) return true;
		if (isTop()) return false;

		// For all variables in other valuation, check if their
		// value in this valuation is less. Other way round is not
		// possible, as their could be variables present in the other
		// valuation but not in this one.
		for (Map.Entry<RTLVariable,A> entry : other.aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			A value = entry.getValue();
			if (!get(var).lessOrEqual(value)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return aVarVal.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((aVarVal == null) ? 0 : aVarVal.hashCode());
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		VariableValuation<A> other = (VariableValuation<A>) obj;
		if (aVarVal == null) {
			return other.aVarVal == null;
		} else {
			return aVarVal.equals(other.aVarVal);
		}
	}

	@Override
	public Iterator<Entry<RTLVariable, A>> iterator() {
		return aVarVal.entrySet().iterator();
	}
	
}
