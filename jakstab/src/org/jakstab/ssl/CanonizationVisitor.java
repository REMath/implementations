/*
 * CanonizationVisitor.java - This file is part of the Jakstab project.
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
package org.jakstab.ssl;

import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class CanonizationVisitor implements ExpressionVisitor<RTLExpression> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CanonizationVisitor.class);
	
	public CanonizationVisitor() {
		super();
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLBitRange)
	 */
	@Override
	public RTLExpression visit(RTLBitRange e) {
		return ExpressionFactory.createBitRange(e.getOperand().accept(this), 
				e.getFirstBitIndex().accept(this), 
				e.getLastBitIndex().accept(this));
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLConditionalExpression)
	 */
	@Override
	public RTLExpression visit(RTLConditionalExpression e) {
		RTLExpression cond = e.getCondition().accept(this);
		if (cond instanceof RTLNumber) { /* static evaluation possible */
			if (((RTLNumber)cond).longValue() == 0L) {
				//logger.debug("Collapsing conditional expression to FALSE-branch.");
				return e.getFalseExpression().accept(this);
			}
			else {
				//logger.debug("Collapsing conditional expression to TRUE-branch.");
				return e.getTrueExpression().accept(this); 
			}
		} else return ExpressionFactory.createConditionalExpression(cond, 
				e.getTrueExpression().accept(this), 
				e.getFalseExpression().accept(this));
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLMemoryLocation)
	 */
	@Override
	public RTLExpression visit(RTLMemoryLocation e) {
		return ExpressionFactory.createMemoryLocation(
				e.getSegmentRegister(), e.getAddress().accept(this), e.getBitWidth());
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLNondet)
	 */
	@Override
	public RTLExpression visit(RTLNondet e) {
		return e;
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLNumber)
	 */
	@Override
	public RTLExpression visit(RTLNumber e) {
		return e;
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLOperation)
	 */
	@Override
	public RTLExpression visit(RTLOperation e) {
		// if there is a conditional expression among the parameters, move it to the front
		// and generate a copy of this operation for each branch. Canonize both copies,
		// which ensures that the remaining operands are processed as well.
		RTLExpression[] operands = e.getOperands();
		for(int i=0; i<e.getOperandCount(); i++) {
			if (operands[i] instanceof RTLConditionalExpression) {
				RTLConditionalExpression cExpr = (RTLConditionalExpression)operands[i];
				RTLExpression[] trueOperands = operands.clone();
				RTLExpression[] falseOperands = operands.clone();
				trueOperands[i] = cExpr.getTrueExpression();
				falseOperands[i] = cExpr.getFalseExpression();
				return ExpressionFactory.createConditionalExpression(cExpr.getCondition(),
						ExpressionFactory.createOperation(e.getOperator(), trueOperands).accept(this),
						ExpressionFactory.createOperation(e.getOperator(), falseOperands).accept(this));
			}
		}
		// if no conditionals as operands, just recurse all parameters
		RTLExpression[] evaldOperands = new RTLExpression[e.getOperandCount()];
		for(int i=0; i<e.getOperandCount(); i++) {
			evaldOperands[i] = operands[i].accept(this); 
		}
		return ExpressionFactory.createOperation(e.getOperator(), evaldOperands);
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLSpecialExpression)
	 */
	@Override
	public RTLExpression visit(RTLSpecialExpression e) {
		// if there is a conditional expression among the parameters, move it to the front
		// and generate a copy of this operation for each branch. Canonize both copies,
		// which ensures that the remaining operands are processed as well.
		RTLExpression[] operands = e.getOperands();
		for(int i=0; i<e.getOperandCount(); i++) {
			if (operands[i] instanceof RTLConditionalExpression) {
				RTLConditionalExpression cExpr = (RTLConditionalExpression)operands[i];
				RTLExpression[] trueOperands = operands.clone();
				RTLExpression[] falseOperands = operands.clone();
				trueOperands[i] = cExpr.getTrueExpression();
				falseOperands[i] = cExpr.getFalseExpression();
				return ExpressionFactory.createConditionalExpression(cExpr.getCondition(),
						ExpressionFactory.createSpecialExpression(e.getOperator(), trueOperands).accept(this),
						ExpressionFactory.createSpecialExpression(e.getOperator(), falseOperands).accept(this));
			}
		}
		// if no conditionals as operands, just recurse all parameters
		RTLExpression[] evaldOperands = new RTLExpression[e.getOperandCount()];
		for(int i=0; i<e.getOperandCount(); i++) {
			evaldOperands[i] = operands[i].accept(this); 
		}
		return ExpressionFactory.createSpecialExpression(e.getOperator(), evaldOperands);
	}

	/*
	 * @see org.jakstab.rtl.ExpressionVisitor#visit(org.jakstab.rtl.RTLVariable)
	 */
	@Override
	public RTLExpression visit(RTLVariable e) {
		return e;
	}

}
