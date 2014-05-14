/*
 * RTLOperation.java - This file is part of the Jakstab project.
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Set;

import org.jakstab.rtl.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class RTLOperation extends AbstractRTLExpression implements RTLExpression {

	private final static Logger logger = Logger.getLogger(RTLOperation.class);

	protected Set<RTLMemoryLocation> usedMemoryLocations = null;

	private final Operator operator;
	private final RTLExpression[] operands;
	private final int operandCount;
	private final int size;
	private final int bitWidth;

	protected RTLOperation(Operator operator, RTLExpression... operands) {
		super();
		this.operator = operator;
		this.operands = operands;
		this.operandCount = operands.length;
		int theSize = 1;
		for (int i = 0; i < operandCount; i++)
			theSize += operands[i].size();
		size = theSize;
		
		bitWidth = calculateBitWidth(operator, operands);
		assert bitWidth == 1 || (bitWidth % 8 == 0) : "Bitwidth not a multiple of 8: " + bitWidth + ". Operation was " + this;
	}

	/**
	 * @return the operation
	 */
	public Operator getOperator() {
		return operator;
	}
	
	/**
	 * @return the operands
	 */
	public RTLExpression[] getOperands() {
		return operands;
	}

	public int getOperandCount() {
		return operandCount;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		
		if (operator == Operator.SIGN_EXTEND || operator == Operator.ZERO_FILL || operator == Operator.FSIZE) {
			res.append(operator + "(");
			res.append(operands[0].toString());
			for (int i = 1; i < operandCount; i++)
				res.append(", " + operands[i].toString());
			res.append(')');
		} else {
			res.append('(');
			switch (operandCount) {
			case 0:
				res.append(operator.toString());
				break;
			case 1:
				res.append(operator.toString() + " " + operands[0].toString());
				break;
			case 2:
				res.append(operands[0] + " " + operator.toString() + " " + operands[1]);
				break;
			default: {
				res.append(operands[0].toString());
				for (int i = 1; i < operandCount; i++) 
					res.append(" " + operator.toString() + " " + operands[i].toString());
			}
			}
			res.append(')');
		}
		return res.toString();
	}
	
	private RTLExpression removeOperand(int opIndex, RTLExpression[] opArray) {
		assert operandCount > 1;
		// If only two operands left, return the other one.
		if (operandCount == 2) {
			return opIndex == 0 ? opArray[1] : opArray[0];
		}
		RTLExpression[] newOperands = new RTLExpression[operandCount - 1];
		for (int i=0; i < opIndex; i++)
			newOperands[i] = opArray[i];
		for (int i=opIndex + 1; i < operandCount; i++)
			newOperands[i - 1] = opArray[i];

		// Bitwidth may only change when it was unknown before 
		assert (bitWidth == RTLVariable.UNKNOWN_BITWIDTH) || 
		(calculateBitWidth(operator, newOperands) == bitWidth) : 
			"Bitwidth of " + this + " changed from " + bitWidth + " to " + calculateBitWidth(operator, newOperands) + " on removal of operand " + opIndex + "!"; 
		
		return ExpressionFactory.createOperation(operator, newOperands);
	}
	
	private final boolean isZero(RTLExpression e) {
		return e instanceof RTLNumber && ((RTLNumber)e).longValue() == 0L;
	}

	private final boolean allBitsOne(RTLExpression e) {
		return e instanceof RTLNumber && ((RTLNumber)e).longValue() == -1L;
	}
	
	private final boolean equalsLaterOperand(int opIndex, RTLExpression[] opArray) {
		for (int j = opIndex + 1; j < opArray.length; j++)
			if (opArray[j].equals(opArray[opIndex]))
				return true;
		return false;
	}

	private final boolean equalsBitWiseNotOfLaterOperand(int opIndex, RTLExpression[] opArray) {
		for (int j = opIndex + 1; j < opArray.length; j++)
			if (opArray[j].equals(ExpressionFactory.createNot(opArray[opIndex])))
				return true;
		return false;
	}

	@Override
	public RTLExpression evaluate(Context context) {

		assert operandCount > 0;
		RTLExpression[] evaledOperands = new RTLExpression[operandCount];

		for(int i=0; i<operandCount; i++) {
			evaledOperands[i] = operands[i].evaluate(context);
		}
		int evaldBitwidth = calculateBitWidth(operator, evaledOperands);
		
		assert evaldBitwidth != 0 : this;
		
		/////////////////////////
		// Special cases for different operators

		switch (operator) {

		case CAST:
			assert operandCount == 2;
			assert evaledOperands[1] instanceof RTLNumber;
			int castWidth = ((RTLNumber)evaledOperands[1]).intValue();
			RTLExpression subExp = evaledOperands[0];
			if (subExp.getBitWidth() == castWidth) {
				//logger.info("Removing unnecessary cast from " + var);
				return subExp;
			} else {
				RTLExpression zfillExp = ExpressionFactory.createZeroFill(
						ExpressionFactory.createNumber(subExp.getBitWidth() + 1, 8), 
						ExpressionFactory.createNumber(castWidth - 1, 8), 
						subExp); 
				logger.warn("Replacing cast: " + this.toString() + " with zero_fill: " + zfillExp);
				return zfillExp;
			}

		case SIGN_EXTEND: case ZERO_FILL:
			assert operandCount == 3;
			if (evaledOperands[0] instanceof RTLNumber &&
					evaledOperands[1] instanceof RTLNumber &&
					evaledOperands[2] instanceof RTLNumber) {
				long op = ((RTLNumber)evaledOperands[2]).longValue();
				int width = evaledOperands[2].getBitWidth();
				int from = ((RTLNumber)evaledOperands[0]).intValue();
				int to = ((RTLNumber)evaledOperands[1]).intValue();
				int targetWidth = Math.max(width, to + 1);
				// check sign bit (MSB)
				if (operator == Operator.SIGN_EXTEND) {
					if ((op & RTLBitRange.bitMask(width - 1,  width - 1)) > 0) {
						long extension = op | RTLBitRange.bitMask(from, to);
						//logger.debug("Sign extension: " + evaledOperands[2] + " => " + extension);
						return ExpressionFactory.createNumber(extension, targetWidth);
					} else {
						return ExpressionFactory.createNumber(op, targetWidth);
					} 
				} else { // ZERO_FILL
					long filled = op & (
							RTLBitRange.bitMask(0, from - 1) |
							RTLBitRange.bitMask(to + 1, targetWidth - 1));
					return ExpressionFactory.createNumber(filled, targetWidth);
				}
			} else {
				return ExpressionFactory.createOperation(operator, evaledOperands[0], evaledOperands[1], evaledOperands[2]);
			}
			// break; Unreachable;
			
		case FSIZE:
			assert operandCount == 3;
			// do nothing for now
			return ExpressionFactory.createOperation(operator, evaledOperands[0], evaledOperands[1], evaledOperands[2]);
		case XOR:
			if (operandCount == 2) {
				if (evaledOperands[0].equals(evaledOperands[1])) 
					return ExpressionFactory.createNumber(0, getBitWidth());
				if (isZero(evaledOperands[0])) return evaledOperands[1];
				if (isZero(evaledOperands[1])) return evaledOperands[0];
				if (allBitsOne(evaledOperands[0])) return ExpressionFactory.createNot(evaledOperands[1]).evaluate(context);
				if (allBitsOne(evaledOperands[1])) return ExpressionFactory.createNot(evaledOperands[0]).evaluate(context);
			}
			break;

		case EQUAL:
			if (operandCount == 2) {
				if (evaledOperands[0].equals(evaledOperands[1])) 
					return ExpressionFactory.TRUE;
				if (ExpressionFactory.TRUE.equals(evaledOperands[0])) 
					return evaledOperands[1];
				if (ExpressionFactory.TRUE.equals(evaledOperands[1])) 
					return evaledOperands[0];
				if (ExpressionFactory.FALSE.equals(evaledOperands[0]))
					return ExpressionFactory.createNot(evaledOperands[1]).evaluate(context);
				if (ExpressionFactory.FALSE.equals(evaledOperands[1]))
					return ExpressionFactory.createNot(evaledOperands[0]).evaluate(context);
			}
			break;

		case AND: case OR: case PLUS: case MUL:
			for (int opIndex = 0; opIndex < operandCount; opIndex++) {
				RTLExpression op = evaledOperands[opIndex];
				switch (operator) {
				case AND:
					if (isZero(op)) return ExpressionFactory.createNumber(0, getBitWidth());
					if (equalsLaterOperand(opIndex, evaledOperands))
						return removeOperand(opIndex, evaledOperands).evaluate(context);
					if (equalsBitWiseNotOfLaterOperand(opIndex, evaledOperands))
						return ExpressionFactory.createNumber(0, getBitWidth());
					if (allBitsOne(op)) return removeOperand(opIndex, evaledOperands).evaluate(context);
					break;
				case OR:
					if (allBitsOne(op)) return ExpressionFactory.createNumber(-1, getBitWidth());
					if (equalsLaterOperand(opIndex, evaledOperands))
						return removeOperand(opIndex, evaledOperands).evaluate(context);
					if (equalsBitWiseNotOfLaterOperand(opIndex, evaledOperands))
						return ExpressionFactory.createNumber(- (2^(getBitWidth() - 1)), getBitWidth());
					if (isZero(op)) return removeOperand(opIndex, evaledOperands).evaluate(context);
					break;
				case PLUS:
					if (isZero(op)) return removeOperand(opIndex, evaledOperands).evaluate(context);
					// Simplify (x + y - x + z) to (y + z)
					if (op instanceof RTLOperation) {
						RTLOperation operation = (RTLOperation)op;
						if (operation.getOperator().equals(Operator.NEG)) {
							for (int j=0; j<evaledOperands.length; j++) {
								if (operation.getOperands()[0].equals(evaledOperands[j])) {
									// x + (-x) == 0
									if (evaledOperands.length == 2)
										return ExpressionFactory.createNumber(0, evaldBitwidth);
									// Remove both from sum but leave the rest 
									RTLExpression[] newOperands = new RTLExpression[evaledOperands.length - 2];
									int newIdx = 0;
									for (int idx = 0; idx < evaledOperands.length; idx++) {
										if (idx != opIndex && idx != j)
											newOperands[newIdx++] = evaledOperands[idx];
									}
									if (newOperands.length == 1)
										return newOperands[0];
									else
										return ExpressionFactory.createOperation(operator, newOperands).evaluate(context);
								}
							}
						}
					}
					
					break;
				case MUL:
					if (isZero(op)) return ExpressionFactory.createNumber(0, getBitWidth());
					break;
				default:
				}
			}
			break;
			
		case NOT:
			// Implements !(!a && !b) == a || b and !(!a || !b) == a && b
			if (evaledOperands[0] instanceof RTLOperation) {
				RTLOperation child = (RTLOperation)evaledOperands[0];
				andOrCheck: switch (child.operator) {
				case AND: case OR:
					for (int opIndex = 0; opIndex < child.operandCount; opIndex++) {
						RTLExpression subOp = child.operands[opIndex];
						if (!(subOp instanceof RTLOperation) || !(((RTLOperation)subOp).operator == Operator.NOT)) {
							break andOrCheck;
						}
					}
					// The current NOTs child is an AND or OR with only NOTed children.
					RTLExpression[] strippedSubOps = new RTLExpression[child.getOperandCount()];
					for (int opIndex = 0; opIndex < child.operandCount; opIndex++)
						strippedSubOps[opIndex] = ((RTLOperation)child.operands[opIndex]).operands[0];
					
					if (child.operator == Operator.AND)
						return ExpressionFactory.createOperation(Operator.OR, strippedSubOps);
					else
						return ExpressionFactory.createOperation(Operator.AND, strippedSubOps);
				}
			}
			break;
			
		}
		
		/////////////////////////
		// Simplify comparison operators (aims at simplifying conditional jump expressions)
		
		// (x < y) | (x = y)   <->   x <= y   (in integer bitvectors)
		// If the operator is an OR, has 2 operands, which are both again operations
		if (operator == Operator.OR && operandCount == 2 && 
				evaledOperands[0] instanceof RTLOperation && evaledOperands[1] instanceof RTLOperation) {
			RTLOperation op0 = (RTLOperation)evaledOperands[0];
			RTLOperation op1 = (RTLOperation)evaledOperands[1];
			// If each operation has 2 operands which are equal to the ones of the other operation
			if (op0.getOperandCount() == 2 && op1.getOperandCount() == 2 && 
					op0.operands[0].equals(op1.operands[0]) && op0.operands[1].equals(op1.operands[1])) {
				// If one operation is u< and the other =, return u<=
				if ((op0.operator == Operator.UNSIGNED_LESS && op1.operator == Operator.EQUAL) ||
						(op1.operator == Operator.UNSIGNED_LESS && op0.operator == Operator.EQUAL))
					return ExpressionFactory.createUnsignedLessOrEqual(op0.operands[0], op0.operands[1]);
				// If one operation is < and the other =, return <=
				if ((op0.operator == Operator.LESS && op1.operator == Operator.EQUAL) ||
						(op1.operator == Operator.LESS && op0.operator == Operator.EQUAL))
					return ExpressionFactory.createLessOrEqual(op0.operands[0], op0.operands[1]);
			}
		}
		
		/////////////////////////
		// Combine numeric operands
		
		ArrayList<RTLExpression> exprOps = new ArrayList<RTLExpression>(operandCount);
		ArrayList<Long> numericOps = new ArrayList<Long>(operandCount);
		for(int i=0; i<operandCount; i++) {
			// Numeric operand?
			if (evaledOperands[i] instanceof RTLNumber) { 
				numericOps.add(((RTLNumber)evaledOperands[i]).longValue());
			} else {
				exprOps.add(evaledOperands[i]);
			}
		}

		if (numericOps.size() > 0 && (numericOps.size() > 1 || operandCount == 1)) {
			long result;
			
			if (operandCount == 1) {
				long op = numericOps.get(0);
				switch (this.operator) {
				case NEG:
					result = -op;
					break;
				case NOT:
					result = ~op;
					break;
				default:
					logger.info("Missing operand handler for \"" + this.operator + 
					"\"! Cannot determine numeric result in evaluation.");
				return ExpressionFactory.createOperation(this.operator, evaledOperands);
				}
			} else {
				long op1 = numericOps.get(0);
				long op2 = numericOps.get(1);

				switch (this.operator) {
				case MUL:
					result = 1;
					for (long x : numericOps) {
						result *= x;
					}
					break;
				case PLUS:
					result = 0;
					for (long x : numericOps) {
						result += x;
					}
					break;
				case AND:
					result = -1L;
					for (long x : numericOps) {
						result &= x;
					}
					break;
				case OR:
					result = 0;
					for (long x : numericOps) {
						result |= x;
					}
					break;
				case EQUAL:
					result = op1 == op2 ? ExpressionFactory.TRUE.longValue() : ExpressionFactory.FALSE.longValue();
					break;
				case LESS:
					result = op1 < op2 ?  ExpressionFactory.TRUE.longValue() : ExpressionFactory.FALSE.longValue();
					break;
				case LESS_OR_EQUAL:
					result = op1 <= op2 ?  ExpressionFactory.TRUE.longValue() : ExpressionFactory.FALSE.longValue();
					break;
				case UNSIGNED_LESS:
					if (op1 < 0 && op2 >= 0) result = ExpressionFactory.FALSE.longValue(); 
					else if (op2 < 0 && op1 >= 0) result = ExpressionFactory.TRUE.longValue(); 
					else result = op1 < op2 ?  ExpressionFactory.TRUE.longValue() : ExpressionFactory.FALSE.longValue();
					break;
				case UNSIGNED_LESS_OR_EQUAL:
					if (op1 < 0 && op2 >= 0) result = ExpressionFactory.FALSE.longValue(); 
					else if (op2 < 0 && op1 >= 0) result = ExpressionFactory.TRUE.longValue(); 
					else result = op1 <= op2 ?  ExpressionFactory.TRUE.longValue() : ExpressionFactory.FALSE.longValue();
					break;
				case SHL:
					result = op1 << op2;
					//logger.debug("Shift left result: " + op1 + " SHL " + op2 + " = " + result);
					break;
				case SHR:
					result = (0xFFFFFFFFL & op1) >>> op2;
					//logger.debug("Shift right result: " + op1 + " SHR " + op2 + " = " + result);
					break;
				case SAR:
					result = op1 >> op2;
					//logger.debug("Shift arithmetic right result: " + op1 + " SAR " + op2 + " = " + result);
					break;
				case XOR:
					result = op1 ^ op2;
					break;
				default:
					logger.info("Missing operand handler for \"" + this.operator + 
					"\"! Cannot determine numeric result in evaluation.");
				return ExpressionFactory.createOperation(this.operator, evaledOperands);
				}
			}
			
			RTLExpression numericOperand;
			// Check if result is pseudo-boolean
			if (evaldBitwidth == 1) {
				numericOperand = result != 0 ? ExpressionFactory.TRUE : ExpressionFactory.FALSE; 
			} else {			
				numericOperand = ExpressionFactory.createNumber(result, evaldBitwidth);
			}
			// Combine with remaining non-numeric operands if necessary
			if (exprOps.size() == 0) { 
				return numericOperand;
			} else {
				evaledOperands = new RTLExpression[exprOps.size() + 1];
				exprOps.toArray(evaledOperands);
				evaledOperands[evaledOperands.length - 1] = numericOperand;
			}
		} 

		return ExpressionFactory.createOperation(this.operator, evaledOperands);
	}

	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			for(int i=0; i<operandCount; i++) {
				usedVariables.addAll(operands[i].getUsedVariables());
			}
		}
		return usedVariables;
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		if (usedMemoryLocations == null) {
			usedMemoryLocations = new FastSet<RTLMemoryLocation>();
			for(int i=0; i<operandCount; i++) {
				usedMemoryLocations.addAll(operands[i].getUsedMemoryLocations());
			}
		}
		return usedMemoryLocations;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) return false;
		RTLOperation other = (RTLOperation)obj;
		return this.operator.equals(other.operator) && Arrays.equals(this.operands, other.operands);
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 43 + operator.hashCode() + Arrays.hashCode(operands);
	}

	@Override
	public int size() {
		return size;
	}

	private static int calculateBitWidth(Operator operation, RTLExpression[] operands) {
		switch(operation) {
		// Testers
		case EQUAL: case LESS: case LESS_OR_EQUAL: case UNSIGNED_LESS: case UNSIGNED_LESS_OR_EQUAL: 
			return 1;
		// Division
		case MOD: case DIV:
			// Division always has bitwidth of divisor (at least on intel)
			return operands[1].getBitWidth();
		// Unary
		case NEG: case NOT:
			return operands[0].getBitWidth();
		// n-ary arithmetic and bitvector operations of same-type operands
		case PLUS: case MUL: case FMUL: case FDIV: case AND: case OR: case XOR:
			int bw = operands[0].getBitWidth();
			if (bw <= 0) return RTLVariable.UNKNOWN_BITWIDTH;
			for (int i=1; i<operands.length; i++) {
				if (operands[i].getBitWidth() <= 0) return RTLVariable.UNKNOWN_BITWIDTH;
				//assert operands[i].getBitWidth() == bw :
				if (operands[i].getBitWidth() != bw) {
					logger.warn(
					"Different bitwidths in operands: " + bw + " and " + operands[i].getBitWidth() + 
					" for " + operation + Arrays.toString(operands) );
					bw = Math.max(bw, operands[i].getBitWidth());
				}
			}
			// Multiply always doubles the bitwidth (at least in pentium.ssl)
			if (operation == Operator.MUL) {
				bw = bw * 2;
			}
			return bw;
		// Power
		case POWER_OF:
			return operands[0].getBitWidth();
		// Shifts
		case SHR: case SAR: case SHL: case ROL: case ROLC: case ROR: case RORC:
			return operands[0].getBitWidth();
/*			int largest = Integer.MIN_VALUE;
			for (int i=0; i<operands.length; i++)
				if (operands[i].getBitWidth() > largest) {
					largest = operands[i].getBitWidth();
					assert largest <= 128: "Operand length " + largest + " exceeds max bit width!" + operands[i].toString();
				}
			return largest;*/
		// Special
		case CAST: 
			return ((RTLNumber)operands[1]).intValue();
		case FSIZE: 
			return ((RTLNumber)operands[1]).intValue();
		case SIGN_EXTEND: case ZERO_FILL:
			return Math.max(((RTLNumber)operands[1]).intValue() + 1, operands[2].getBitWidth());
			

		default:
			throw new RuntimeException("Unhandled bitwidth case: " + operation);
		}
	}

	@Override
	public int getBitWidth() {
		return bitWidth;
	}
	
	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		RTLExpression[] typedOperands = new RTLExpression[operandCount];
		
		switch (operator) {
		// Testers
		case EQUAL: case LESS: case LESS_OR_EQUAL: case UNSIGNED_LESS: case UNSIGNED_LESS_OR_EQUAL:
			if (expectedBitWidth != 1) throw new TypeInferenceException();

			// Make sure all operands are of same bit width
			int bw = Integer.MIN_VALUE;
			for (int i=0; i<operandCount; i++) {
				bw = operands[i].getBitWidth();
				if (bw > 0) break;
			}
			if (bw <= 0) throw new TypeInferenceException(
					"Cannot infer type for " + toString() + "!");
			for (int i=0; i<operandCount; i++)
				typedOperands[i] = operands[i].inferBitWidth(arch, bw);
			
			return ExpressionFactory.createOperation(operator, typedOperands);

		case PLUS: case AND: case OR: case XOR: case NEG: case NOT: case FMUL: case FDIV:  
			for (int i=0; i<operandCount; i++)
				typedOperands[i] = operands[i].inferBitWidth(arch, expectedBitWidth);
			return ExpressionFactory.createOperation(operator, typedOperands);
		
		// Shifting
		case SHR: case SAR: case SHL: case ROL: case ROLC: case ROR: case RORC:
			typedOperands[0] = operands[0].inferBitWidth(arch, expectedBitWidth);
			// is this always 8? no, e.g. not in bts modrm, eax. 
			try {
				typedOperands[1] = operands[1].inferBitWidth(arch, 8);
			} catch (TypeInferenceException e) {
				logger.warn("Exception on inferring type of shift distance " + operands[1]);
				// If there is another type already, leave it
				typedOperands[1] = operands[1];
			}
			
			return ExpressionFactory.createOperation(operator, typedOperands);
			
		// Division
		case MOD: case DIV:
			// Division always has bitwidth of divisor (at least on intel...)
			typedOperands[0] = operands[0];
			typedOperands[1] = operands[1].inferBitWidth(arch, expectedBitWidth);
			return ExpressionFactory.createOperation(operator, typedOperands);
		// Should be something like: sum of all op-bws = expectedbw; not implemented for now.
		case MUL:
			assert operands.length == 2;
			typedOperands[0] = operands[0].inferBitWidth(arch, expectedBitWidth / 2);
			typedOperands[1] = operands[1].inferBitWidth(arch, expectedBitWidth / 2);
			return ExpressionFactory.createOperation(operator, typedOperands);
		case POWER_OF:
			return this;
			
		// Check Cast
		case CAST:
			if (expectedBitWidth != ((RTLNumber)operands[1]).intValue())
				throw new TypeInferenceException();
			else return this;
		
		// Bit extension
		case SIGN_EXTEND: case ZERO_FILL:
			int from = ((RTLNumber)operands[0]).intValue();
			typedOperands[0] = operands[0].inferBitWidth(arch, 8);
			int to = ((RTLNumber)operands[1]).intValue();
			int targetWidth = to + 1;
			typedOperands[1] = operands[1].inferBitWidth(arch, 8);
			if (targetWidth != expectedBitWidth) 
				throw new TypeInferenceException("Bit extension to " + targetWidth + "bits, expected " + expectedBitWidth);
			typedOperands[2] = operands[2].inferBitWidth(arch, from);
			return ExpressionFactory.createOperation(operator, typedOperands);
			
		case FSIZE:
			from = ((RTLNumber)operands[0]).intValue();
			typedOperands[0] = operands[0].inferBitWidth(arch, 8);
			to = ((RTLNumber)operands[1]).intValue();
			typedOperands[1] = operands[1].inferBitWidth(arch, 8);
			
			if (to != expectedBitWidth) 
				throw new TypeInferenceException("Round to " + to + "bits, expected " + expectedBitWidth);
			typedOperands[2] = operands[2].inferBitWidth(arch, from);
			return ExpressionFactory.createOperation(operator, typedOperands);
			
		default:
			throw new RuntimeException("Unhandled bitwidth case: " + operator);		
		}
		
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
