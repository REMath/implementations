/*
 * VariableValuationTest.java - This file is part of the Jakstab project.
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

import static org.junit.Assert.*;

import org.jakstab.analysis.explicit.*;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class VariableValuationTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(VariableValuationTest.class);
	
	private static RTLVariable x32;
	private static RTLVariable y16;
	private static RTLVariable z32;
	private static NumberElement n32;
	private static NumberElement n32b;
	private static NumberElement n32c;
	private static NumberElement n16;
	private static RTLVariable eax;
	private static RTLVariable ax;
	private static RTLVariable ah;
	private static RTLVariable al;
	
	
	@Before
	public void setUp() throws Exception {
		x32 = ExpressionFactory.createVariable("x32", 32);
		y16 = ExpressionFactory.createVariable("y16", 16);
		z32 = ExpressionFactory.createVariable("z32", 32);
		n32 = new NumberElement(ExpressionFactory.createNumber(52, 32));
		n32b = new NumberElement(ExpressionFactory.createNumber(13, 32));
		n32c = new NumberElement(ExpressionFactory.createNumber(13, 32));
		n16 = new NumberElement(ExpressionFactory.createNumber(-123, 16));
		eax = ExpressionFactory.createVariable("eax", 32);
		ax = ExpressionFactory.createSharedRegisterVariable("ax", "eax", 0, 15);
		ah = ExpressionFactory.createSharedRegisterVariable("ah", "ax", 8, 15);
		al = ExpressionFactory.createSharedRegisterVariable("al", "ax", 0, 7);
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testSet() {
		VariableValuation<NumberElement> aVarVal = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		aVarVal.set(x32, n32);
		aVarVal.set(y16, n16);
		assertEquals(n16, aVarVal.get(y16));
		assertEquals(n32, aVarVal.get(x32));
	}
	
	@Test
	public void testRegisterMasking() {
		VariableValuation<BasedNumberElement> aVarVal = 
			new VariableValuation<BasedNumberElement>(new BasedNumberElementFactory());
		BasedNumberElement val1 = new BasedNumberElement(ExpressionFactory.createNumber(0xCAFE3344, 32));
		BasedNumberElement val2 = new BasedNumberElement(ExpressionFactory.createNumber(0xBE, 8));
		BasedNumberElement val3 = new BasedNumberElement(ExpressionFactory.createNumber(0xBA, 8));
		aVarVal.set(eax, val1);
		assertEquals(val1, aVarVal.get(eax));
		aVarVal.set(al, val2);
		assertEquals(new BasedNumberElement(ExpressionFactory.createNumber(0xCAFE33BE, 32)), aVarVal.get(eax));
		aVarVal.set(ah, val3);
		assertEquals(new BasedNumberElement(ExpressionFactory.createNumber(0xCAFEBABE, 32)), aVarVal.get(eax));
		assertEquals(new BasedNumberElement(ExpressionFactory.createNumber(0xBABE, 16)), aVarVal.get(ax));
	}

	@Test
	public void testIsTop() {
		VariableValuation<NumberElement> aVarVal = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		assertTrue(aVarVal.isTop());
		aVarVal.set(x32, n32);
		assertFalse(aVarVal.isTop());
		aVarVal.set(x32, NumberElement.getTop(32));
		assertTrue(aVarVal.isTop());
	}

	@Test
	public void testJoin() {
		VariableValuation<NumberElement> aVarVal1 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		VariableValuation<NumberElement> aVarVal2 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		aVarVal1.set(x32, n32);
		aVarVal1.set(y16, n16);
		aVarVal1.set(z32, n32b);
		aVarVal2.set(x32, n32b);
		aVarVal2.set(z32, n32c);
		VariableValuation<NumberElement> join = aVarVal1.join(aVarVal2);
		assertEquals(join, aVarVal2.join(aVarVal1));
		assertTrue(aVarVal1.lessOrEqual(join));
		assertTrue(aVarVal2.lessOrEqual(join));
		assertEquals(NumberElement.getTop(32), join.get(x32));
		assertEquals(NumberElement.getTop(16), join.get(y16));
		assertEquals(n32b, join.get(z32));
		assertEquals(n32c, join.get(z32));
	}

	@Test
	public void testLessOrEqual() {
		VariableValuation<NumberElement> aVarVal1 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		VariableValuation<NumberElement> aVarVal2 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		aVarVal1.set(x32, n32);
		aVarVal1.set(y16, n16);
		aVarVal1.set(z32, n32b);
		assertTrue(aVarVal1.lessOrEqual(aVarVal2));
		aVarVal2.set(z32, n32c);
		assertTrue(aVarVal1.lessOrEqual(aVarVal2));
		aVarVal2.set(z32, n32);
		assertFalse(aVarVal1.lessOrEqual(aVarVal2));
	}

	@Test
	public void testEqualsObject() {
		VariableValuation<NumberElement> aVarVal1 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		VariableValuation<NumberElement> aVarVal2 = 
			new VariableValuation<NumberElement>(new NumberElementFactory());
		assertEquals(aVarVal1, aVarVal2);
		aVarVal1.set(x32, n32b);
		assertFalse(aVarVal1.equals(aVarVal2));
		aVarVal2.set(x32, n32c);
		assertEquals(aVarVal1, aVarVal2);
	}

}
