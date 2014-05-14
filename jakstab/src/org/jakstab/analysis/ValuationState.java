/*
 * ValuationState.java - This file is part of the Jakstab project.
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

import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

/**
 * A generic class for abstract states that map each variable and memory location
 * to some abstract value. It provides functions for abstract expression evaluation
 * via power set expansion or subexpression joining, getters and setters for variables
 * and memory, as well as Cartesian lattice operators. For this to work, you need to
 * supply it with an AbstractValueFactory that creates abstract elements of the
 * specific abstract domain that should be implemented. 
 * 
 * The abstract post remains to be implemented by the main analysis class. 
 * 
 * @author Johannes Kinder
 */
public class ValuationState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ValuationState.class);
	
	private static long maxStateId = 0;

	private final long id;
	private final AbstractValueFactory<AbstractDomainElement> valueFactory;
	private VariableValuation<AbstractDomainElement> varVal;
	private PartitionedMemory<AbstractDomainElement> store;
	
	public ValuationState(ValuationState proto) {
		this(proto.valueFactory, 
				new VariableValuation<AbstractDomainElement>(proto.varVal), 
				new PartitionedMemory<AbstractDomainElement>(proto.store));
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public ValuationState(AbstractValueFactory valueFactory) {
		this(valueFactory, 
				new VariableValuation<AbstractDomainElement>(valueFactory), 
				new PartitionedMemory<AbstractDomainElement>(valueFactory));
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private ValuationState(AbstractValueFactory valueFactory, VariableValuation<AbstractDomainElement> varVal, PartitionedMemory<AbstractDomainElement> store) {
		this.valueFactory = valueFactory;
		this.varVal = varVal;
		this.store = store;
		this.id = maxStateId++;
	}
	
	public AbstractDomainElement abstractEval(RTLExpression e) {	
		// TODO: Create a fast, specific implementation for this
		Set<AbstractDomainElement> result = abstractEvalPowerSet(e);
		return Lattices.joinAll(result);
	}
	
	public Set<AbstractDomainElement> abstractEvalPowerSet(RTLExpression e) {
		return e.accept(new ExpressionVisitor<Set<AbstractDomainElement>>() {

			@Override
			public Set<AbstractDomainElement> visit(RTLBitRange e) {
				AbstractDomainElement first = Lattices.joinAll(e.getFirstBitIndex().accept(this));
				AbstractDomainElement last = Lattices.joinAll(e.getLastBitIndex().accept(this));
				if (first.hasUniqueConcretization() && last.hasUniqueConcretization()) {
					Set<AbstractDomainElement> res = new FastSet<AbstractDomainElement>();
					for (AbstractDomainElement aOp : e.getOperand().accept(this)) {
						res.add(aOp.bitExtract(first.concretize().iterator().next().intValue(),
								last.concretize().iterator().next().intValue()));
					}
					return res;
				} else {
					return Collections.singleton(valueFactory.createTop(e.getBitWidth()));
				}
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLMemoryLocation e) {
				Set<AbstractDomainElement> res = new FastSet<AbstractDomainElement>();
				for (AbstractDomainElement aAddress : e.getAddress().accept(this)) {
						res.addAll(aAddress.readStorePowerSet(e.getBitWidth(), store));
				}
				return res;
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLOperation e) {
				Tuple<Set<AbstractDomainElement>> aOperandSets = 
					new Tuple<Set<AbstractDomainElement>>(e.getOperandCount());
				for (int i=0; i<e.getOperandCount(); i++) {
					aOperandSets.set(i, e.getOperands()[i].accept(this));
				}

				int bitWidth = e.getBitWidth();

				Set<AbstractDomainElement> res = new FastSet<AbstractDomainElement>();

				for (Tuple<AbstractDomainElement> aOperands : Sets.crossProduct(aOperandSets)) {

					AbstractDomainElement result;

					switch (e.getOperator()) {
					case PLUS:
						result = aOperands.get(0);
						for (int i=1; i<aOperands.size(); i++) {
							AbstractDomainElement aOp = aOperands.get(i);
							result = aOp.plus(result);
						}
						break;

					case MUL:
						result = aOperands.get(0);
						for (int i=1; i<aOperands.size(); i++) {
							AbstractDomainElement aOp = aOperands.get(i);
							result = aOp.multiply(result);
						}
						break;

					case EQUAL:
						// If both sides can only have AbstractDomainElement single value, just
						// see if they are equal.
						if (aOperands.get(0).hasUniqueConcretization() && 
								aOperands.get(1).hasUniqueConcretization()) {
							if(aOperands.get(0).concretize().equals(
									aOperands.get(1).concretize())) {
								result = valueFactory.createTrue();
							} else {
								result = valueFactory.createFalse();
							}
						} else {
							result = valueFactory.createTop(bitWidth);
						}
						break;

					case SIGN_EXTEND: {
						int from = ((RTLNumber)e.getOperands()[0]).intValue();
						int to = ((RTLNumber)e.getOperands()[1]).intValue();
						result = aOperands.get(2).signExtend(from, to);
						break;
					}

					case ZERO_FILL: {
						int from = ((RTLNumber)e.getOperands()[0]).intValue();
						int to = ((RTLNumber)e.getOperands()[1]).intValue();
						result = aOperands.get(2).zeroFill(from, to);
						break;
					}

					default:
						result = valueFactory.createTop(bitWidth);
					}

					res.add(result);

				}
				return res;
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLVariable e) {
				return Collections.singleton(varVal.get(e));
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLConditionalExpression e) {
				Set<AbstractDomainElement> res = new FastSet<AbstractDomainElement>();
				res.addAll(e.getTrueExpression().accept(this));
				res.addAll(e.getFalseExpression().accept(this));
				return res;
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLNondet e) {
				return Collections.singleton(valueFactory.createTop(e.getBitWidth()));
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLNumber e) {
				return Collections.singleton(valueFactory.createAbstractValue(e));
			}

			@Override
			public Set<AbstractDomainElement> visit(RTLSpecialExpression e) {
				return Collections.singleton(valueFactory.createTop(e.getBitWidth()));
			}
			
		});
	}

	public void setMemoryValue(AbstractDomainElement address,
			int bitWidth, AbstractDomainElement value) {
		address.writeStore(bitWidth, store, value);
	}
	
	public void setMemoryValue(MemoryRegion region, long offset, int bitWidth, AbstractDomainElement value) {
		store.set(region, offset, bitWidth, value);
	}

	public void setVariableValue(RTLVariable var, AbstractDomainElement value) {
		varVal.set(var, value);
	}
	
	public AbstractDomainElement getMemoryValue(AbstractDomainElement address, int bitWidth) {
		return address.readStore(bitWidth, store);
	}
	
	public AbstractDomainElement getMemoryValue(MemoryRegion region, long offset, int bitWidth) {
		return store.get(region, offset, bitWidth);
	}
	
	public AbstractDomainElement getVariableValue(RTLVariable var) {
		return varVal.get(var);
	}
	
	public Iterator<Map.Entry<RTLVariable, AbstractDomainElement>> variableIterator() {
		return varVal.iterator();
	}
	
	public EntryIterator<MemoryRegion, Long, AbstractDomainElement> storeIterator() {
		return store.entryIterator();
	}

	@Override
	public String getIdentifier() {
		return Long.toString(id);
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public ValuationState join(LatticeElement l) {
		ValuationState other = (ValuationState)l;
		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;

		// Join variable valuations
		VariableValuation<AbstractDomainElement> jVarVal = varVal.join(other.varVal);
		PartitionedMemory<AbstractDomainElement> jStore = store.join(other.store);
		
		return new ValuationState(valueFactory, jVarVal, jStore);
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		Tuple<Set<RTLNumber>> tupleOfSets = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			Set<RTLNumber> concreteValues = new FastSet<RTLNumber>();
			for (AbstractDomainElement el : abstractEvalPowerSet(expressions[i])) {
				Set<RTLNumber> c = el.concretize();
				
				if (c == RTLNumber.ALL_NUMBERS) {
					if (expressions[i].getBitWidth() == 1) {
						// bitWidth is 1, we can just force 1 and 0 here
						concreteValues.add(ExpressionFactory.TRUE);
						concreteValues.add(ExpressionFactory.FALSE);
					} else {
						concreteValues = RTLNumber.ALL_NUMBERS;
						break;
					}
				} else {
					concreteValues.addAll(c);
				}
			}
			tupleOfSets.set(i, concreteValues);
		}
		return Sets.crossProduct(tupleOfSets);
	}

	@Override
	public boolean isBot() {
		return varVal.isBot() && store.isBot();
	}

	@Override
	public boolean isTop() {
		return varVal.isTop() && store.isTop();
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (this == l) return true;
		ValuationState other = (ValuationState)l;
		if (isBot() || other.isTop()) return true;
		if (isTop() || other.isBot()) return false;

		if (!varVal.lessOrEqual(other.varVal))
			return false;

		if (!store.lessOrEqual(other.store)) 
			return false;
		
		return true;
	}
	
	@Override
	public String toString() {
		return "I: " + varVal.toString() + " Mem:" + store.toString();  
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((store == null) ? 0 : store.hashCode());
		result = prime * result + ((varVal == null) ? 0 : varVal.hashCode());
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
		ValuationState other = (ValuationState) obj;
		if (store == null) {
			if (other.store != null)
				return false;
		} else if (!store.equals(other.store))
			return false;
		if (varVal == null) {
			if (other.varVal != null)
				return false;
		} else if (!varVal.equals(other.varVal))
			return false;
		return true;
	}

}
