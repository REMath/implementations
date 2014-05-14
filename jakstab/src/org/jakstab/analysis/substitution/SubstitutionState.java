/*
 * SubstitutionState.java - This file is part of the Jakstab project.
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

import java.util.*;

import org.jakstab.analysis.*;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.*;

/**
 * The abstract state for constant propagation. There are two explicit states 
 * TOP and BOT, all other states use two collections of CPValue elements to
 * assign values to variables and memory. Elements not present in the 
 * collections are implicitly set to a TOP value. BOT elements cannot be
 * present, since a single BOT element makes the whole state turn to BOT.
 * 
 * @author Johannes Kinder
 */
public final class SubstitutionState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SubstitutionState.class);
	private static long maxStateId = 0;
	
	public static final SubstitutionState TOP = new SubstitutionState();
	public static final SubstitutionState BOT = new SubstitutionState();

	private Map<Writable,SubstitutionElement> aVarVal;
	private final long stateId;
	
	
	private SubstitutionState() {
		this (new HashMap<Writable, SubstitutionElement>());
	}
	
	private SubstitutionState(Map<Writable,SubstitutionElement> aVarVal) {
		stateId = ++maxStateId;
		this.aVarVal = aVarVal;
	}
	
	/**
	 * Copy constructor
	 * 
	 * @param proto
	 */
	private SubstitutionState(SubstitutionState proto) {
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
	protected SubstitutionElement abstractEval(RTLExpression e) {
		ExpressionVisitor<SubstitutionElement> visitor = new ExpressionVisitor<SubstitutionElement>() {
			
			@Override
			public SubstitutionElement visit(RTLBitRange e) {
				SubstitutionElement aFirstBit = e.getFirstBitIndex().accept(this);
				SubstitutionElement aLastBit = e.getLastBitIndex().accept(this);
				SubstitutionElement aOperand = e.getOperand().accept(this);
				
				return new SubstitutionElement(
						ExpressionFactory.createBitRange(aOperand.getExpression(), aFirstBit.getExpression(), aLastBit.getExpression())
				);
			}

			@Override
			public SubstitutionElement visit(RTLConditionalExpression e) {
				SubstitutionElement aCondition = e.getCondition().accept(this);
				SubstitutionElement aTrue = e.getTrueExpression().accept(this);
				SubstitutionElement aFalse = e.getFalseExpression().accept(this);
				return new SubstitutionElement(
						ExpressionFactory.createConditionalExpression(aCondition.getExpression(), aTrue.getExpression(), aFalse.getExpression())
						);
			}

			@Override
			public SubstitutionElement visit(RTLMemoryLocation m) {
				SubstitutionElement aAddress = m.getAddress().accept(this);
				if (!aAddress.isTop()) {
					m = ExpressionFactory.createMemoryLocation(m.getSegmentRegister(), aAddress.getExpression(), m.getBitWidth());
				}
				SubstitutionElement s = getValue(m);
				if (s.isTop()) {
					return new SubstitutionElement(m);
				} else {
					return s;
				}
			}

			@Override
			public SubstitutionElement visit(RTLNondet e) {
				return new SubstitutionElement(e);
			}

			@Override
			public SubstitutionElement visit(RTLNumber e) {
				return new SubstitutionElement(e);
			}

			@Override
			public SubstitutionElement visit(RTLOperation e) {
				RTLExpression[] aOperands = new RTLExpression[e.getOperandCount()];
				for (int i=0; i<e.getOperandCount(); i++) {
					aOperands[i] = e.getOperands()[i].accept(this).getExpression();
				}
				return new SubstitutionElement(
						ExpressionFactory.createOperation(e.getOperator(), aOperands).evaluate(new Context())
						);
			}

			@Override
			public SubstitutionElement visit(RTLSpecialExpression e) {
				RTLExpression[] aOperands = new RTLExpression[e.getOperandCount()];
				for (int i=0; i<e.getOperandCount(); i++) {
					aOperands[i] = e.getOperands()[i].accept(this).getExpression();
				}
				return new SubstitutionElement(
						ExpressionFactory.createSpecialExpression(e.getOperator(), aOperands)
						);
			}

			@Override
			public SubstitutionElement visit(RTLVariable e) {
				SubstitutionElement s = getValue(e);
				if (s.isTop()) {
					return new SubstitutionElement(e);
				} else {
					return s;
				}
			}
			
		};
		
		SubstitutionElement result = e.accept(visitor);
		RTLExpression simplified = ExpressionSimplifier.getInstance().simplify(result.getExpression());
		if (simplified != result.getExpression())
			result = new SubstitutionElement(simplified);
		return result;
	}
	
	
	public AbstractState abstractPost(StateTransformer transformer, Precision precision) {
		if (isBot()) return BOT;
		
		final RTLStatement statement = (RTLStatement)transformer;
		
		return statement.accept(new DefaultStatementVisitor<SubstitutionState>() {

			private SubstitutionState clobber(Writable x) {
				SubstitutionState post = new SubstitutionState(SubstitutionState.this);
				
				// Remove existing substitutions for the pointer
				post.aVarVal.remove(x);
				// Remove substituted expressions that contain the pointer
				for (Iterator<Map.Entry<Writable, SubstitutionElement>> iter = post.aVarVal.entrySet().iterator(); iter.hasNext();) {
					Map.Entry<Writable, SubstitutionElement> e = iter.next();
					if (e.getValue().getExpression().getUsedVariables().contains(x)) {
						iter.remove();
					}
				}

				if (post.aVarVal.isEmpty()) return TOP;
				if (post.equals(SubstitutionState.this)) return SubstitutionState.this;
				return post;
			}
			
			@Override
			protected SubstitutionState visitDefault(RTLStatement stmt) {
				return SubstitutionState.this;
			}
			
			@Override
			public SubstitutionState visit(RTLVariableAssignment stmt) {

				// Copy old state to new state
				SubstitutionState post = new SubstitutionState(SubstitutionState.this);
				Writable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				
				// Evaluate righthandside
				rhs = abstractEval(rhs).getExpression();
				
				// Remove existing substitution for the LHS
				post.aVarVal.remove(lhs);
				// If RHS is a pure variable, assign RHS to LHS as substitution
				if (!containsNondet(rhs)) {
					post.setValue(lhs, new SubstitutionElement(rhs));
				}

				// If any expression in the map uses the LHS variable, it is now invalid, so remove it
				// Note: This also removes substitutions that were just added such
				//       as esp = esp - 4
				List<RTLVariable> aliasing = new LinkedList<RTLVariable>();
				aliasing.add((RTLVariable)lhs);
				// Remove mappings of all aliasing registers 
				aliasing.addAll(ExpressionFactory.coveredRegisters((RTLVariable)lhs));
				aliasing.addAll(ExpressionFactory.coveringRegisters((RTLVariable)lhs));

				for (RTLVariable v : aliasing) {
					for (Iterator<Map.Entry<Writable, SubstitutionElement>> iter = post.aVarVal.entrySet().iterator(); iter.hasNext();) {
						Map.Entry<Writable, SubstitutionElement> e = iter.next();
						if (e.getKey().getUsedVariablesOnWrite().contains(v) || 
								e.getValue().getExpression().getUsedVariables().contains(v)) {
							iter.remove();
						}
					}
				}

				if (post.aVarVal.isEmpty()) return TOP;
				if (post.equals(SubstitutionState.this)) return SubstitutionState.this;
				//logger.info("Post: " + post);
				return post;
			}
			
			@Override
			public SubstitutionState visit(RTLMemoryAssignment stmt) {

				// Copy old state to new state
				SubstitutionState post = new SubstitutionState(SubstitutionState.this);
				RTLMemoryLocation lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				
				// Evaluate righthandside
				rhs = abstractEval(rhs).getExpression();
				
				// Substitute address elements in a memory location LHS
				SubstitutionElement aAddress = abstractEval(lhs.getAddress());
				if (!aAddress.isTop())
					lhs = ExpressionFactory.createMemoryLocation(lhs.getSegmentRegister(), aAddress.getExpression(), lhs.getBitWidth());

				// Remove existing substitution for the LHS
				post.aVarVal.remove(lhs);
				// If RHS is a pure memory expression, assign RHS to LHS as substitution
				if (!containsNondet(rhs)) {
					post.setValue(lhs, new SubstitutionElement(rhs));
				}

				// If any expression in the map uses the LHS variable, it is now invalid, so remove it
				// Note: This also removes substitutions that were just added such
				//       as esp = esp - 4
				// Remove all substitutions that might alias with it
				// (trivial implementation of memory aliasing, always yes)
				for (Iterator<Map.Entry<Writable, SubstitutionElement>> iter = post.aVarVal.entrySet().iterator(); iter.hasNext();) {
					Map.Entry<Writable, SubstitutionElement> e = iter.next();
					if (e.getKey() instanceof RTLMemoryLocation || !e.getValue().getExpression().getUsedMemoryLocations().isEmpty()) {
						iter.remove();
					}
				}

				if (post.aVarVal.isEmpty()) return TOP;
				if (post.equals(SubstitutionState.this)) return SubstitutionState.this;
				//logger.info("Post: " + post);
				return post;
			}

			@Override
			public SubstitutionState visit(RTLAlloc stmt) {
				return clobber(stmt.getPointer());
			}

			@Override
			public SubstitutionState visit(RTLUnknownProcedureCall stmt) {
				// Remove all substitutions				
				return TOP;
			}

			@Override
			public SubstitutionState visit(RTLHavoc stmt) {
				return clobber(stmt.getVariable());
			}
			
		});
	}

	@Override
	public boolean isTop() {
		return this == TOP;
	}

	@Override
	public boolean isBot() {
		return this == BOT;
	}
	
	private void setValue(Writable w, SubstitutionElement v) {
		if (v.isTop()) {
			aVarVal.remove(w);
		} else {
			aVarVal.put(w, v);
		}
	}
	
	public Location getProgramCounter() {
		return null;
	}

	public SubstitutionElement getValue(Writable v) {
		if (isTop()) return SubstitutionElement.TOP;
		if (isBot()) return SubstitutionElement.BOT;
		
		if (aVarVal.containsKey(v)) return aVarVal.get(v);
		else return SubstitutionElement.TOP;
	}
	
	/*
	 * @see org.jakstab.analysis.AbstractState#join(org.jakstab.analysis.AbstractState)
	 */
	@Override
	public SubstitutionState join(LatticeElement l) {
		SubstitutionState other = (SubstitutionState)l;

		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;
		
		SubstitutionState result = new SubstitutionState();
		
		// Join variable valuations
		for (Map.Entry<Writable,SubstitutionElement> entry : aVarVal.entrySet()) {
			Writable w = entry.getKey();
			SubstitutionElement v = entry.getValue();
			result.setValue(w, v.join(other.getValue(w)));
		}
		if (result.aVarVal.isEmpty()) return TOP;
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		SubstitutionState other = (SubstitutionState)l;

		if (other.isTop() || isBot()) return true;
		if (isTop() || other.isBot()) return false;
		
		// Check for every element in "other" if its value in "this" is less or equal 
		// than the value in "other". The elements not stored in the valuation maps 
		// of "other" are implicitly TOP and thus every value is less or equal than them.
		for (Map.Entry<Writable,SubstitutionElement> entry : other.aVarVal.entrySet()) {
			Writable w = entry.getKey();
			SubstitutionElement v = entry.getValue();
			if (!getValue(w).lessOrEqual(v)) {
				//logger.info(w + ": " + getValue(w) + " is not less or equal to " + v);
				return false;
			}
		}
		
		return true;
	}
	
	@Override
	public String getIdentifier() {
		return Long.toString(stateId);
	}

	private boolean containsNondet(RTLExpression rhs) {
		return rhs.accept(new ExpressionVisitor<Boolean>() {

			@Override
			public Boolean visit(RTLBitRange e) {
				return e.getFirstBitIndex().accept(this) || e.getLastBitIndex().accept(this) || e.getOperand().accept(this);
			}

			@Override
			public Boolean visit(RTLConditionalExpression e) {
				return e.getCondition().accept(this) || e.getTrueExpression().accept(this) || e.getFalseExpression().accept(this);
			}

			@Override
			public Boolean visit(RTLMemoryLocation e) {
				return e.getAddress().accept(this);
			}

			@Override
			public Boolean visit(RTLNondet e) {
				return true;
			}

			@Override
			public Boolean visit(RTLNumber e) {
				return false;
			}

			@Override
			public Boolean visit(RTLOperation e) {
				for (RTLExpression op : e.getOperands()) {
					if (op.accept(this)) return true;
				}
				return false;
			}

			@Override
			public Boolean visit(RTLSpecialExpression e) {
				for (RTLExpression op : e.getOperands()) {
					if (op.accept(this)) return true;
				}
				return false;
			}

			@Override
			public Boolean visit(RTLVariable e) {
				return false;
			}
			
		});
	}


	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		else if (isBot()) return Characters.BOT;
		else return stateId + ": " + aVarVal.toString();
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			SubstitutionElement aValue = abstractEval(expressions[i]);
			cValues.set(i, aValue.concretize());			
		}

		return Sets.crossProduct(cValues);

	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
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
		SubstitutionState other = (SubstitutionState) obj;
		if (other.isTop()) return this.isTop();
		if (other.isBot()) return this.isBot();
		if (aVarVal == null) {
			if (other.aVarVal != null)
				return false;
		} else if (!aVarVal.equals(other.aVarVal))
			return false;
		return true;
	}
}
