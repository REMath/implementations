/*
 * IntervalElementTest.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.intervals;

import static org.junit.Assert.*;

import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class IntervalElementTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(IntervalElementTest.class);

	private IntervalElement i1, i2, expected, r;

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}
	
	@Test
	public void testNegation() {
		i1 = new IntervalElement(MemoryRegion.GLOBAL, -16, 10, 2, 32);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -10, 16, 2, 32);
		r = i1.negate();
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, Integer.MIN_VALUE, Integer.MIN_VALUE, 0, 32);
		r = i1.negate();
		assertEquals(i1, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, Integer.MIN_VALUE, -10, 1, 32);
		r = i1.negate();
		assertEquals(IntervalElement.getTop(32), r);
	}

	@Test
	public void testPlus() {
		i1 = new IntervalElement(MemoryRegion.GLOBAL, -10, 10, 2, 32);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, -6, 10, 2, 32);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -16, 20, 2, 32);
		r = i1.plus(i2);
		assertEquals(expected, r);
		r = i2.plus(i1);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -100, 100, 10, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, -256, 40, 4 , 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -356, 140, 2, 16);
		r = i1.plus(i2);
		assertEquals(expected, r);
		r = i2.plus(i1);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -100, 100, 10, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, ExpressionFactory.createNumber(43, 16));
		expected = new IntervalElement(MemoryRegion.GLOBAL, -57, 143, 10, 16);
		r = i1.plus(i2);
		assertEquals(expected, r);
		r = i2.plus(i1);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, 0, Integer.MAX_VALUE - 11, 2, 32);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, -5, 15, 2, 32);
		expected = IntervalElement.getTop(32);
		r = i1.plus(i2);
		assertEquals(expected, r);
		r = i2.plus(i1);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -100, 100, 10, 8);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 0, 200, 4 , 8);
		expected = IntervalElement.getTop(8);
		r = i1.plus(i2);
		assertEquals(expected, r);
		r = i2.plus(i1);
		assertEquals(expected, r);
	}
	
	@Test
	public void testMultiply() {
		i1 = new IntervalElement(MemoryRegion.GLOBAL, -100, 100, 10, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 0, 20, 4 , 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -2000, 2000, 40, 32);
		r = i1.multiply(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -100, 100, 10, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 0, 0, 0 , 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, 0, 0, 0, 32);
		r = i1.multiply(i2);
		assertEquals(expected, r);
	}
	
	@Test
	public void testJoin() {
		i1 = new IntervalElement(MemoryRegion.GLOBAL, 0, 100, 10, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 0, 100, 25, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, 0, 100, 5, 16);
		r = i1.join(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -3, 6, 3, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, -2, 7, 3, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -3, 7, 1, 16);
		r = i1.join(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 20, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, -2, 34, 12, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 2, 16);
		r = i1.join(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 20, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 7, 7, 0, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 1, 16);
		r = i1.join(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 20, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 6, 6, 0, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -20, 40, 2, 16);
		r = i1.join(i2);
		assertEquals(expected, r);

		i1 = new IntervalElement(MemoryRegion.GLOBAL, -20, -20, 0, 16);
		i2 = new IntervalElement(MemoryRegion.GLOBAL, 11, 11, 0, 16);
		expected = new IntervalElement(MemoryRegion.GLOBAL, -20, 11, 31, 16);
		r = i1.join(i2);
		assertEquals(expected, r);
	}

}
