/*
 * RTLOperationTest.java - This file is part of the Jakstab project.
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

import static org.junit.Assert.*;

import org.jakstab.rtl.*;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Johannes Kinder
 */
public class RTLOperationTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(RTLOperationTest.class);

	private static RTLNumber num1234_32;
	private static RTLNumber num7_32;
	private static RTLNumber num1_32;
	private static RTLNumber num0_32;
	private static RTLExpression opAnd;
	private static RTLNumber num5_8bit;
	private static RTLNumber num5_32bit;
	private static RTLNumber neg125_8;
	private static RTLVariable var8;
	
	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
		num1234_32 = ExpressionFactory.createNumber(1234, 32);
		num7_32 = ExpressionFactory.createNumber(7, 32);
		num1_32 = ExpressionFactory.createNumber(1, 32);
		num0_32 = ExpressionFactory.createNumber(0, 32);
		num5_8bit = ExpressionFactory.createNumber(5, 8);
		num5_32bit = ExpressionFactory.createNumber(5, 32);
		opAnd = ExpressionFactory.createAnd(num1234_32, num7_32); 
		var8 = ExpressionFactory.createVariable("y8", 8);
		neg125_8 = ExpressionFactory.createNumber(-125, 8);
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Test method for {@link org.jakstab.rtl.expressions.RTLOperation#evaluate(org.jakstab.rtl.Context)}.
	 */
	@Test
	public void testEvaluate() throws TypeInferenceException {
		Context emptyContext = new Context();
		RTLExpression result = opAnd.evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(1234 & 7, 32), result);
		RTLExpression opShift = ExpressionFactory.createShiftRight(num1234_32, num1_32);
		result = opShift.evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(1234 >> 1, 32), result);
		
		assertEquals(ExpressionFactory.createNumber(1234 + 7 + 1, 32), ExpressionFactory.createPlus(num1234_32, num7_32, num1_32).evaluate(emptyContext));
		
		
		// removal of 32 bit int changes bitwidth of expression that 
		// includes a lower bit variable or number
		RTLExpression op = ExpressionFactory.createPlus(num0_32, ExpressionFactory.createSignExtend(
				ExpressionFactory.createNumber(8, 8), ExpressionFactory.createNumber(31, 8), var8));
		Context context = new Context();
		context.addAssignment(var8, num5_8bit);
		assertEquals(num5_32bit, op.evaluate(context));
		
		// Used to return !true... 
		op = ExpressionFactory.createEqual(ExpressionFactory.TRUE, ExpressionFactory.FALSE);
		result = op.evaluate(context);
		assertEquals(ExpressionFactory.FALSE, result);
	}
	
	@Test
	public void testBitOperations() {
		Context emptyContext = new Context();
		RTLExpression castedValue = ExpressionFactory.createZeroFill(
				ExpressionFactory.createNumber(8), 
				ExpressionFactory.createNumber(31), 
				num5_8bit);
		RTLExpression result = ExpressionFactory.createOr(num7_32, castedValue).evaluate(emptyContext);
		assertEquals(num7_32, result);
	}
	
	@Test
	public void testZeroFill() {
		Context emptyContext = new Context();
		RTLNumber m5 = ExpressionFactory.createNumber(-5, 8);
		RTLExpression result = ExpressionFactory.createZeroFill(8, 31, m5).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(0xFB, 32), result);
	}
	
	@Test
	public void testSignExtend() {
		Context emptyContext = new Context();
		RTLNumber m5 = ExpressionFactory.createNumber(-5, 8);
		RTLExpression result = ExpressionFactory.createSignExtend(8, 31, m5).evaluate(emptyContext);
		assertEquals(32, result.getBitWidth());
		assertEquals(ExpressionFactory.createNumber(-5, 32), result);
	}
	
	@Test
	public void testShiftRight() {
		Context emptyContext = new Context();
		RTLNumber x = ExpressionFactory.createNumber(0xFF0000000L, 32);
		RTLExpression result = ExpressionFactory.createShiftRight(x, ExpressionFactory.createNumber(30, 8)).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(3, 32), result);
	}
	
	@Test
	public void testMinus() throws TypeInferenceException {
		Context emptyContext = new Context();
		RTLExpression result = ExpressionFactory.createMinus(num1_32, num7_32).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(-6, 32), result);
		
		result = ExpressionFactory.createMinus(num1234_32, num5_32bit).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(1229, 32), result);
		
		result = ExpressionFactory.createMinus(neg125_8, num5_8bit).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(126, 8), result);
		
		result = ExpressionFactory.createPlus(var8, num5_8bit);
		result = ExpressionFactory.createMinus(result, var8).evaluate(emptyContext);
		assertEquals(num5_8bit, result);

		result = ExpressionFactory.createPlus(ExpressionFactory.createNeg(num5_8bit), var8);
		result = ExpressionFactory.createMinus(var8, result).evaluate(emptyContext);
		assertEquals(num5_8bit, result);
}
	
	@Test
	public void testAdd() throws TypeInferenceException {
		Context emptyContext = new Context();
		RTLExpression result = ExpressionFactory.createPlus(
				ExpressionFactory.createNumber(125, 8), 
				num5_8bit).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(-126, 8), result);
		
		result = ExpressionFactory.createPlus(ExpressionFactory.createNumber(120, 8), 
				ExpressionFactory.createNumber(110, 8), 
				ExpressionFactory.createNumber(60, 8), 
				ExpressionFactory.createNumber(95, 8)).evaluate(emptyContext);
		assertEquals(ExpressionFactory.createNumber(-127, 8), result);
	}
	
	@Test
	public void testComparisons() {
		Context emptyContext = new Context();
		assertEquals(ExpressionFactory.TRUE, ExpressionFactory.createLessThan(num5_32bit, num1234_32).evaluate(emptyContext));
		assertEquals(ExpressionFactory.FALSE, ExpressionFactory.createLessThan(num5_8bit, neg125_8).evaluate(emptyContext));
		assertEquals(ExpressionFactory.TRUE, ExpressionFactory.createUnsignedLessThan(num5_8bit, neg125_8).evaluate(emptyContext));
		assertEquals(ExpressionFactory.TRUE, ExpressionFactory.createUnsignedLessOrEqual(num5_8bit, neg125_8).evaluate(emptyContext));
	}

}
