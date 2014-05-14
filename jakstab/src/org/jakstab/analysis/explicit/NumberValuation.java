/*
 * NumberValuation.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.io.IOException;
import java.util.*;

import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.loader.ExecutableImage;
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
public final class NumberValuation implements AbstractState {

	private static final Logger logger = Logger.getLogger(NumberValuation.class);
	private static long maxStateId = 0;
	
	static final NumberValuation TOP = new NumberValuation(new HashMap<RTLVariable, NumberElement>(), new HashMap<RTLMemoryLocation, NumberElement>(), true);

	
	public static NumberValuation createInitialState() {
		NumberValuation initial = new NumberValuation();
		// init stack pointer
		//RTLNumber espStartValue = factory.createNumber(0x1000, 32);
		//initial.setValue(Program.getProgram().getArchitecture().stackPointer(), new NumberElement(espStartValue));
		// push the address of a halt instruction on the stack
		//initial.setValue(factory.createMemoryLocation(espStartValue, 32), new NumberElement(factory.createNumber(0, 32)));
		initial.setValue(ExpressionFactory.createVariable("%DF", 1), new NumberElement(ExpressionFactory.createNumber(0, 1)));
		return initial;
	}
	
	private Map<RTLVariable,NumberElement> aVarVal;
	private Map<RTLMemoryLocation,NumberElement> aMemVal;
	private boolean dataIsTop;
	private final long stateId;
	
	
	/**
	 * Creates a new state which is equivalent to TOP.
	 */
	private NumberValuation() {
		this (new HashMap<RTLVariable, NumberElement>(), new HashMap<RTLMemoryLocation, NumberElement>(), false);
	}
	
	private NumberValuation(Map<RTLVariable,NumberElement> aVarVal, Map<RTLMemoryLocation,NumberElement> aMemVal, boolean dataIsTop) {
		stateId = ++maxStateId;
		this.aVarVal = aVarVal;
		this.aMemVal = aMemVal;
		this.dataIsTop = dataIsTop;
	}
	
	/**
	 * Copy constructor
	 * 
	 * @param proto
	 */
	private NumberValuation(NumberValuation proto) {
		this();
		aVarVal.putAll(proto.aVarVal);
		aMemVal.putAll(proto.aMemVal);
		dataIsTop = proto.dataIsTop;
	}
	
	/**
	 * Evaluates an expression in the context of this abstract state to
	 * an abstract value.
	 * 
	 * @param e the expression to be evaluated.
	 * @return the abstract value of the expression in the abstract state.
	 */
	protected NumberElement abstractEval(RTLExpression e) {
		
		ExpressionVisitor<NumberElement> visitor = new ExpressionVisitor<NumberElement>() {
			
			@Override
			public NumberElement visit(RTLBitRange e) {
				NumberElement aFirstBit = e.getFirstBitIndex().accept(this);
				NumberElement aLastBit = e.getLastBitIndex().accept(this);
				NumberElement aOperand = e.getOperand().accept(this);
				
				if (aFirstBit.isTop() || aLastBit.isTop() || aOperand.isTop())
					return NumberElement.getTop(e.getBitWidth());
				
				return new NumberElement(RTLBitRange.calculate(aFirstBit.getNumber(), aLastBit.getNumber(), aOperand.getNumber()));
			}

			@Override
			public NumberElement visit(RTLConditionalExpression e) {
				NumberElement aCondition = e.getCondition().accept(this);
				NumberElement result = null;
				// If aCondition is TOP, the both branches are joined
				if (NumberElement.TRUE.lessOrEqual(aCondition)) 
					result = e.getTrueExpression().accept(this);
				if (NumberElement.FALSE.lessOrEqual(aCondition)) {
					NumberElement falseVal = e.getFalseExpression().accept(this); 
					result = result == null ? falseVal : result.join(falseVal);
				}
				return result;
			}

			@Override
			public NumberElement visit(RTLMemoryLocation m) {
				// abstractly evaluate the address first
				NumberElement abstractAddress = m.getAddress().accept(this);
				// if the address cannot be resolved to a constant, return top 
				if (abstractAddress.isTop()) return NumberElement.getTop(m.getBitWidth());
				// create constant memory location
				RTLNumber constantAddress = abstractAddress.getNumber();
				m = ExpressionFactory.createMemoryLocation(m.getSegmentRegister(), constantAddress, m.getBitWidth());
				// check value of the constant memory location in this state 
				return getValue(m);
			}

			@Override
			public NumberElement visit(RTLNondet e) {
				return NumberElement.getTop(e.getBitWidth());
			}

			@Override
			public NumberElement visit(RTLNumber e) {
				return new NumberElement(e);
			}

			@Override
			public NumberElement visit(RTLOperation e) {
				RTLExpression[] aOperands = new RTLExpression[e.getOperandCount()];
				for (int i=0; i<e.getOperandCount(); i++) {
					NumberElement aOperand = e.getOperands()[i].accept(this);
					if (aOperand.isTop()) aOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
					else aOperands[i] = aOperand.getNumber();
				}
				RTLExpression result = ExpressionFactory.createOperation(e.getOperator(), aOperands).evaluate(new Context());
				if (result instanceof RTLNumber) return new NumberElement((RTLNumber)result);
				else return NumberElement.getTop(e.getBitWidth());
			}

			@Override
			public NumberElement visit(RTLSpecialExpression e) {
				if (e.getOperator().equals(RTLSpecialExpression.GETPROCADDRESS)) {
					NumberElement aLibNameAddr = e.getOperands()[0].accept(this);
					NumberElement aProcNameAddr = e.getOperands()[1].accept(this);
					if (!aLibNameAddr.isTop() && !aProcNameAddr.isTop()) {
						long libNameAddr = aLibNameAddr.getNumber().longValue();
						long procNameAddr = aProcNameAddr.getNumber().longValue();
						String libName = getCString(libNameAddr);
						// If it's length 1, it's most probably a unicode string:
						if (libName.length() <= 1) {
							libName = getWString(libNameAddr);
						}
						String procName = getCString(procNameAddr);
						logger.info("GetProcAddress for " + procName + " from module " + libName);
						long procAddress = Program.getProgram().getProcAddress(libName, procName).getValue();
						return new NumberElement(ExpressionFactory.createNumber(procAddress, 32));
						
					} else {
						logger.info("Could not determine parameters of GetProcAddress!");
					}
				}
				return NumberElement.getTop(e.getBitWidth());
			}

			@Override
			public NumberElement visit(RTLVariable e) {
				return getValue(e);
			}
			
		};
		
		return e.accept(visitor);
	}
	
	
	public AbstractState abstractPost(StateTransformer transformer, Precision precision) {
		
		final RTLStatement statement = (RTLStatement)transformer;

		return statement.accept(new DefaultStatementVisitor<NumberValuation>() {

			private final NumberValuation fallThroughState() {
				return NumberValuation.this; //new NumberValuation(NumberValuation.this);
			}
			
			@Override
			public NumberValuation visit(RTLVariableAssignment stmt) {
				NumberValuation post = new NumberValuation(NumberValuation.this);
				NumberElement evaledRhs = abstractEval(stmt.getRightHandSide());

				post.setValue(stmt.getLeftHandSide(), evaledRhs);
				if (post.aVarVal.isEmpty() && post.aMemVal.isEmpty() && post.dataIsTop) return TOP;
				return post;
			}

			@Override
			public NumberValuation visit(RTLMemoryAssignment stmt) {
				NumberValuation post = new NumberValuation(NumberValuation.this);
				NumberElement evaledRhs = abstractEval(stmt.getRightHandSide());

				// only store constant memory addresses
				RTLMemoryLocation m = stmt.getLeftHandSide();
				NumberElement abstractAddress = abstractEval(m.getAddress());
				// if the address cannot be determined, set all store memory to TOP
				if (abstractAddress.isTop()) {
					logger.verbose(stmt.getLabel() + ": Cannot resolve memory write to " + m + ". Defaulting all memory to " + Characters.TOP);
					post.clearMemory();
				}
				// if it's a constant address, store the assigned value
				else {
					RTLNumber constantAddress = abstractAddress.getNumber();
					m = ExpressionFactory.createMemoryLocation(m.getSegmentRegister(), constantAddress, m.getBitWidth());
					post.setValue(m, evaledRhs);
				}
				if (post.aVarVal.isEmpty() && post.aMemVal.isEmpty() && post.dataIsTop) return TOP;
				return post;
			}
			
			@Override
			public NumberValuation visit(RTLHavoc stmt) {
				NumberValuation post = new NumberValuation(NumberValuation.this);
				RTLVariable v = stmt.getVariable();
				post.setValue(v, NumberElement.getTop(v.getBitWidth()));
				if (post.aVarVal.isEmpty() && post.aMemVal.isEmpty() && post.dataIsTop) return TOP;
				return post;
			}
			
			@Override
			public NumberValuation visit(RTLAssume stmt) {
				NumberElement truthValue = abstractEval(stmt.getAssumption());
				if (truthValue.equals(NumberElement.FALSE)) {
					logger.info(getIdentifier() + ": Transformer " + stmt + " is infeasible.");
					return null;
				} else if (truthValue.equals(NumberElement.TRUE)){
					return fallThroughState();
				} else {
					// Modify state so that it respects the assumption
					// Currently works only for simple assumptions assume(var = value)
					if (stmt.getAssumption() instanceof RTLOperation) {
						RTLOperation operation = (RTLOperation)stmt.getAssumption();
						if (operation.getOperator() == Operator.EQUAL) {
							if (operation.getOperands()[0] instanceof RTLVariable) {
								RTLVariable var = (RTLVariable)operation.getOperands()[0];
								if (operation.getOperands()[1] instanceof RTLNumber) {
									RTLNumber value = (RTLNumber)operation.getOperands()[1];
									logger.debug("Restricting state to " + var + " = " + value);
									NumberValuation post = new NumberValuation(NumberValuation.this);
									post.setValue(var, new NumberElement(value));
									return post;
								}
							}
						}
					}
					return fallThroughState();
				}
			}

			@Override
			public NumberValuation visit(RTLAlloc stmt) {
				NumberValuation post = new NumberValuation(NumberValuation.this);
				// Clobber value in pointer, overwritten by allocated address
				post.setValue(stmt.getPointer(), NumberElement.getTop(stmt.getPointer().getBitWidth()));
				if (post.aVarVal.isEmpty() && post.aMemVal.isEmpty() && post.dataIsTop) return TOP;
				return post;
			}

			@Override
			public NumberValuation visit(RTLUnknownProcedureCall stmt) {
				
				// Generate an unsound successor for an unknown procedure call				
				NumberValuation post = new NumberValuation(NumberValuation.this);
				for (RTLVariable var : stmt.getDefinedVariables()) {
					post.setValue(var, NumberElement.getTop(var.getBitWidth()));
				}
				post.clearMemory();
				return post;
			}

			@Override
			public NumberValuation visitDefault(RTLStatement stmt) {
				return fallThroughState();
			}

		});
	}

	@Override
	public boolean isTop() {
		return this == TOP || (aVarVal.isEmpty() && aMemVal.isEmpty());
	}

	@Override
	public boolean isBot() {
		return false;
	}
	
	private void setValue(RTLMemoryLocation m, NumberElement v) {
		if (v.isTop()) aMemVal.remove(m);
		else aMemVal.put(m, v);
	}
	
	private void setValue(RTLVariable var, NumberElement v) {
		if (v.isTop()) aVarVal.remove(var);
		else aVarVal.put(var, v);
	}
	
	private void setValue(Writable w, NumberElement v) {
		if (w instanceof RTLVariable)
			setValue((RTLVariable)w, v);
		else 
			setValue((RTLMemoryLocation)w, v);
	}
	
	public Location getProgramCounter() {
		return null;
	}

	/**
	 * Sets all abstract memory values to TOP.
	 */
	private void clearMemory() {
		dataIsTop = true;
		aMemVal.clear();
	}

	public NumberElement getValue(RTLVariable v) {
		if (isTop()) return NumberElement.getTop(v.getBitWidth());
		
		if (aVarVal.containsKey(v)) return aVarVal.get(v);
		else return NumberElement.getTop(v.getBitWidth());
	}
	
	public NumberElement getValue(RTLMemoryLocation m) {
		if (isTop()) return NumberElement.getTop(m.getBitWidth());
		
		if (aMemVal.containsKey(m)) return aMemVal.get(m);
		else {
			// Check if the memory location references the program's data area or imports
			if (m.getAddress() instanceof RTLNumber) {
				AbsoluteAddress a = new AbsoluteAddress((RTLNumber)m.getAddress());
				ExecutableImage module = Program.getProgram().getModule(a);
				if (module == null) return NumberElement.getTop(m.getBitWidth());
				// only read memory from image if we havn't overapproximated yet or it's a read only section
				if (!dataIsTop || module.isReadOnly(a)) {
					try {
						RTLNumber mValue = module.readMemoryLocation(m);
						// Memory outside the program area is implicitly initialized to top 
						if (mValue != null) 
							return new NumberElement(mValue);
					} catch (IOException e) {
						// Fall through and return TOP
					}
				}
			}
			return NumberElement.getTop(m.getBitWidth());
		}
	}
	
	private String getCString(long offset) {
		StringBuilder res = new StringBuilder();
		int length = 0;
		while (true) {
			NumberElement v = getValue((ExpressionFactory.createMemoryLocation(
					ExpressionFactory.createNumber(offset + length), 8)));
			if (v.isBot() || v.isTop()) return null;
			int newChar = v.getNumber().intValue();
			if (newChar == 0) break;
			length++;
			res.append((char)newChar);
		}
		return res.toString();
	}
	
	/**
	 * Just a hack, not really a unicode implementation.
	 */
	private String getWString(long offset) {
		StringBuilder res = new StringBuilder();
		int length = 0;
		boolean firstByte = true;
		while (true) {
			NumberElement v = getValue((ExpressionFactory.createMemoryLocation(
					ExpressionFactory.createNumber(offset + length), 8)));
			length++;
			if (v.isBot() || v.isTop()) return null;
			int newChar = v.getNumber().intValue();
			if (firstByte) {
				if (newChar == 0) break;
				res.append((char)newChar);
				firstByte = false;
			} else {
				firstByte = true;
			}
		}
		return res.toString();
	}

	/*
	 * @see org.jakstab.analysis.AbstractState#join(org.jakstab.analysis.AbstractState)
	 */
	@Override
	public NumberValuation join(LatticeElement l) {
		NumberValuation other = (NumberValuation)l;

		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;
		
		NumberValuation result = new NumberValuation();
		result.dataIsTop = dataIsTop || other.dataIsTop;
		
		// Join variable valuations
		for (Map.Entry<RTLVariable,NumberElement> entry : aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			NumberElement v = entry.getValue();
			result.setValue(var, v.join(other.getValue(var)));
		}
		// Join memory valuations. We need to do both directions, because
		// constant image data is not present in aMemVal, but only visible
		// through calls to getValue().
		for (Map.Entry<RTLMemoryLocation,NumberElement> entry : aMemVal.entrySet()) {
			RTLMemoryLocation m = entry.getKey();
			NumberElement v = entry.getValue();
			result.setValue(m, v.join(other.getValue(m)));
		}
		for (Map.Entry<RTLMemoryLocation,NumberElement> entry : other.aMemVal.entrySet()) {
			RTLMemoryLocation m = entry.getKey();
			NumberElement v = entry.getValue();
			result.setValue(m, v.join(getValue(m)));
		}
		
		if (result.aVarVal.isEmpty() && result.aMemVal.isEmpty() && dataIsTop) return TOP;
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		NumberValuation other = (NumberValuation)l;

		if (other.isTop() || isBot()) return true;
		// other is not top and this is not bot:
		if (isTop() || other.isBot()) return false;
		
		if (dataIsTop && !other.dataIsTop)
			return false;

		// Check for every element in "other" if its value in "this" is less or equal 
		// than the value in "other". The elements not stored in the valuation maps 
		// of "other" are implicitly TOP and thus every value is less or equal than them.
		for (Map.Entry<RTLVariable,NumberElement> entry : other.aVarVal.entrySet()) {
			RTLVariable var = entry.getKey();
			NumberElement v = entry.getValue();
			if (!getValue(var).lessOrEqual(v)) {
				//logger.info(var + ": " + getValue(var) + " is not less or equal to " + v);
				return false;
			}
		}
		
		for (Map.Entry<RTLMemoryLocation,NumberElement> entry : other.aMemVal.entrySet()) {
			RTLMemoryLocation m = entry.getKey();
			NumberElement v = entry.getValue();
			if (!getValue(m).lessOrEqual(v)) {
				//logger.info(m + ": " + getValue(m) + " is not less or equal to " + v);
				return false;
			}
		}
		return true;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof NumberValuation)) return false;
		NumberValuation other = (NumberValuation)obj;
		if (other == this) return true;

		if (other.isTop()) return isTop();
		if (isTop()) return false;
		
		return dataIsTop == other.dataIsTop && aVarVal.equals(other.aVarVal) && aMemVal.equals(other.aMemVal);
	}

	@Override
	public String getIdentifier() {
		return Long.toString(stateId);
	}

	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		else if (isBot()) return Characters.BOT;
		else return "Var: " + aVarVal.toString() + ", Mem: " + aMemVal.toString();
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			NumberElement aValue = abstractEval(expressions[i]);
			cValues.set(i, aValue.concretize());			
		}

		return Sets.crossProduct(cValues);

	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}
}
