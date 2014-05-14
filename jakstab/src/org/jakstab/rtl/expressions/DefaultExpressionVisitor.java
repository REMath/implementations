/*
 * DefaultExpressionVisitor.java - This file is part of the Jakstab project.
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

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class DefaultExpressionVisitor<T extends AbstractValue> implements ExpressionVisitor<T> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(DefaultExpressionVisitor.class);
	
	protected AbstractValueFactory<T> valueFactory;
	
	public DefaultExpressionVisitor(AbstractValueFactory<T> valueFactory) {
		this.valueFactory = valueFactory;
	}

	@Override
	public T visit(RTLBitRange e) {
		return valueFactory.createTop(e.getBitWidth());
	}

	@SuppressWarnings("unchecked")
	@Override
	public T visit(RTLConditionalExpression e) {
		T aCondition = e.getCondition().accept(this);
		if (aCondition.equals(valueFactory.createTrue())) {
			return e.getTrueExpression().accept(this);
		} else if (aCondition.equals(valueFactory.createFalse())) {
			return e.getFalseExpression().accept(this);
		} else { 
			return (T)e.getTrueExpression().accept(this).join(
					e.getFalseExpression().accept(this));
		}
	}

	@Override
	public T visit(RTLMemoryLocation e) {
		return valueFactory.createTop(e.getBitWidth());
	}

	@Override
	public T visit(RTLNondet e) {
		return valueFactory.createTop(e.getBitWidth());
	}

	@Override
	public T visit(RTLNumber e) {
		return valueFactory.createAbstractValue(e);
	}

	@Override
	public T visit(RTLOperation e) {
		return valueFactory.createTop(e.getBitWidth());
	}

	@Override
	public T visit(RTLSpecialExpression e) {
		return valueFactory.createTop(e.getBitWidth());
	}

	@Override
	public T visit(RTLVariable e) {
		return valueFactory.createTop(e.getBitWidth());
	}

}
