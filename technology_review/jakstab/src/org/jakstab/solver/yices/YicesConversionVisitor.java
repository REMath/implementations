/*
 * YicesConversionVisitor.java - This file is part of the Jakstab project.
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
package org.jakstab.solver.yices;

import java.util.Set;

import org.jakstab.rtl.expressions.*;
import org.jakstab.solver.UnrepresentableElementException;
import org.jakstab.util.*;

/**
 * @author Johannes Kinder
 */
public class YicesConversionVisitor implements ExpressionVisitor<String> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(YicesConversionVisitor.class);
	
	private SetOfVariables variables = new SetOfVariables();
	private Set<Pair<String, Integer>> nondets = new FastSet<Pair<String, Integer>>();
	private int usedMemoryStates = -1;
	
	public SetOfVariables getVariables() {
		return variables;
	}

	public Set<Pair<String, Integer>> getNondets() {
		return nondets;
	}
	
	public int usedMemoryStates() {
		return usedMemoryStates;
	}

	@Override
	public String visit(RTLBitRange e) {
		return YicesWrapper.makeBVExtract(e.getOperand().accept(this), 
				((RTLNumber)e.getFirstBitIndex()).intValue(), 
				((RTLNumber)e.getLastBitIndex()).intValue());
	}

	@Override
	public String visit(RTLConditionalExpression e) {
		return YicesWrapper.makeITE(
				YicesWrapper.makeEquality(e.getCondition().accept(this), YicesSolver.yTrue), 
				e.getTrueExpression().accept(this), e.getFalseExpression().accept(this));
	}
	
	private String addOffset(String address, int offset) {
		return YicesWrapper.makeBVAdd(address, YicesWrapper.makeBVConstant(32, offset));
	}

	@Override
	public String visit(RTLMemoryLocation e) {
		usedMemoryStates = Math.max(usedMemoryStates, e.getMemoryState());
		String mem = "m" + e.getMemoryState();
		if (e.getSegmentRegister() == null) {
			String address = e.getAddress().accept(this);
			String result = null;
			String curCase;
			switch (e.getBitWidth()) {
			case 32:
				curCase = YicesWrapper.makeOperation(mem, addOffset(address, 3));
				result = result != null ? YicesWrapper.makeBVConcat(result, curCase) : curCase;
			case 24:
				curCase = YicesWrapper.makeOperation(mem, addOffset(address, 2));
				result = result != null ? YicesWrapper.makeBVConcat(result, curCase) : curCase;
			case 16:
				curCase = YicesWrapper.makeOperation(mem, addOffset(address, 1));
				result = result != null ? YicesWrapper.makeBVConcat(result, curCase) : curCase;
			case 8:
				curCase = YicesWrapper.makeOperation(mem, address);
				result = result != null ? YicesWrapper.makeBVConcat(result, curCase) : curCase;
				return result;

				/*
			case 8:
				return YicesWrapper.makeOperation(mem, address);
			case 16:
				return YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 1)),
						YicesWrapper.makeOperation(mem, address) 
						);
			case 32:
				return YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 3)), 
						YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 2)),
						 YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 1)),
						  YicesWrapper.makeOperation(mem, address) 
								)));
			case 64:
				return YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 7)),
						YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 6)),
						 YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 5)),
						  YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 4)),
						   YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 3)),
					        YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 2)),
						     YicesWrapper.makeBVConcat(YicesWrapper.makeOperation(mem, addOffset(address, 1)),
						      YicesWrapper.makeOperation(mem, address) 
								)))))));
								*/
			default:
				throw new UnrepresentableElementException("Unsupported memory access width: " + e.getBitWidth());
			}
			
		} else {
			throw new UnrepresentableElementException("Segments not yet supported");
		}
	}

	@Override
	public String visit(RTLNondet e) {
		String n = e.toString() + "_" + nondets.size();
		nondets.add(Pair.create(n, e.getBitWidth()));
		return n;
	}

	@Override
	public String visit(RTLNumber e) {
		if (e.longValue() < 0) {
			return YicesWrapper.makeBVNeg(YicesWrapper.makeBVConstant(e.getBitWidth(), -e.longValue()));
		} else {
			return YicesWrapper.makeBVConstant(e.getBitWidth(), e.longValue());
		}
	}
	
	private String yicesOperator(Operator op) {
		switch(op) {
		
		case EQUAL:					return "=";
		case LESS:					return "bv-slt";
		case LESS_OR_EQUAL:			return "bv-sle";
		case UNSIGNED_LESS:			return "bv-lt";
		case UNSIGNED_LESS_OR_EQUAL:return "bv-le";
		case NOT:					return "bv-not";
		case NEG:					return "bv-neg";
		case AND:					return "bv-and"; 
		case OR:					return "bv-or"; 
		case XOR:					return "bv-xor";
		case PLUS:					return "bv-add";
		case MUL:					return "bv-mul";
		case SIGN_EXTEND: case ZERO_FILL: case SHR: case SHL:
			return "requires_special_handling";
			
		default: throw new UnrepresentableElementException(op.toString());
		}

	}

	@Override
	public String visit(RTLOperation e) {
		
		String[] yicesOperands = new String[e.getOperandCount()];
		for (int i=0; i<e.getOperandCount(); i++) {
			yicesOperands[i] = e.getOperands()[i].accept(this);
		}
		
		String yicesOp = yicesOperator(e.getOperator());

		switch (e.getOperator()) {
		
		// Operations with non-bitvector operands
		case SIGN_EXTEND:
			int signBits = ((RTLNumber)e.getOperands()[1]).intValue() - ((RTLNumber)e.getOperands()[0]).intValue() + 1; 
			return YicesWrapper.makeBVSignExtend(yicesOperands[2], signBits);

		case ZERO_FILL:
			int zeroes = ((RTLNumber)e.getOperands()[1]).intValue() - ((RTLNumber)e.getOperands()[0]).intValue() + 1; 
			return YicesWrapper.makeBVZeroExtend(yicesOperands[2], zeroes);

		case SHR:
			return YicesWrapper.makeBVShiftRight(e.getOperands()[0].accept(this), 
					((RTLNumber)e.getOperands()[1]).intValue());
		case SHL:
			return YicesWrapper.makeBVShiftLeft(e.getOperands()[0].accept(this), 
					((RTLNumber)e.getOperands()[1]).intValue());			

		// In Jakstab, booleans are represented as 1-bit bitvectors, so here we convert
		// Yices booleans into bitvectors
		case LESS:
		case LESS_OR_EQUAL:
		case UNSIGNED_LESS:
		case UNSIGNED_LESS_OR_EQUAL:
		case EQUAL:
			return YicesWrapper.makeITE(YicesWrapper.makeOperation(yicesOp, yicesOperands), 
					YicesSolver.yTrue, 
					YicesSolver.yFalse);
			
		case AND: case OR: case PLUS: case MUL:
			String result = YicesWrapper.makeOperation(yicesOp, 
					yicesOperands[e.getOperandCount() - 2], 
					yicesOperands[e.getOperandCount() - 1]);
				
			for (int i=e.getOperandCount() - 3; i >= 0; i--) {
				result = YicesWrapper.makeOperation(yicesOp, 
						yicesOperands[i], result);
			}
			return result;			
			
		default:
			return YicesWrapper.makeOperation(yicesOp, yicesOperands);
		}
	}

	@Override
	public String visit(RTLSpecialExpression e) {
		throw new UnrepresentableElementException(e.toString());
	}

	@Override
	public String visit(RTLVariable e) {
		variables.add(e);
		return e.toString();
	}
	


}
