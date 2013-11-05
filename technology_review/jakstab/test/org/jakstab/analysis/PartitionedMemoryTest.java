/*
 * PartitionedMemoryTest.java - This file is part of the Jakstab project.
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

import org.jakstab.Options;
import org.jakstab.analysis.explicit.NumberElement;
import org.jakstab.analysis.explicit.NumberElementFactory;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class PartitionedMemoryTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(PartitionedMemoryTest.class);

	private static NumberElement n32;
	private static NumberElement n32b;
	private static NumberElement n32c;
	private static NumberElement n16;
	private static MemoryRegion alloc1;
	private static MemoryRegion alloc2;
	private NumberElementFactory valueFactory;
	
	
	@Before
	public void setUp() throws Exception {
		n32 = new NumberElement(ExpressionFactory.createNumber(52, 32));
		n32b = new NumberElement(ExpressionFactory.createNumber(13, 32));
		n32c = new NumberElement(ExpressionFactory.createNumber(13, 32));
		n16 = new NumberElement(ExpressionFactory.createNumber(-123, 16));
		alloc1 = MemoryRegion.create("PartA");
		alloc2 = MemoryRegion.create("PartB");
		valueFactory = new NumberElementFactory();
		Options.debug.setValue(false);
	}

	@After
	public void tearDown() throws Exception {
		Options.debug.setValue(true);
	}

	@Test
	public void testSetTopMemoryRegion() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		store.set(MemoryRegion.STACK, 120, 32, n32);
		store.set(alloc1, 2, 16, n16);
		store.setTop(MemoryRegion.STACK);
		assertTrue(store.get(MemoryRegion.STACK, 120, 32).isTop());
		assertEquals(n16, store.get(alloc1, 2, 16));
	}

	@Test
	public void testSet() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		store.set(MemoryRegion.GLOBAL, 120, 32, n32);
		store.set(alloc1, 2, 16, n16);
		assertEquals(n32, store.get(MemoryRegion.GLOBAL, 120, 32));
		assertEquals(n16, store.get(alloc1, 2, 16));
		store.set(alloc1, 0, 32, n32);
		assertEquals(n32, store.get(alloc1, 0, 32));
	}

	@Test
	public void testForgetStackBelow() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		store.set(MemoryRegion.STACK, -8, 32, n32);
		store.set(MemoryRegion.STACK, -12, 32, n32);
		store.forgetStackBelow(-8);
		assertEquals(n32, store.get(MemoryRegion.STACK, -8, 32));
		assertEquals(valueFactory.createTop(32), store.get(MemoryRegion.STACK, -12, 32));
	}

	@Test
	public void testJoin() {
		PartitionedMemory<NumberElement> store1 = new PartitionedMemory<NumberElement>(
				valueFactory);
		PartitionedMemory<NumberElement> store2 = new PartitionedMemory<NumberElement>(
				valueFactory);
		store1.set(MemoryRegion.GLOBAL, 120, 32, n32b);
		store1.set(alloc1, 2, 16, n16);
		store1.set(alloc2, -10, 32, n32c);
		store2.set(MemoryRegion.GLOBAL, 120, 32, n32c);
		store2.set(alloc2, -10, 32, n32b);
		PartitionedMemory<NumberElement> join = store1.join(store2);
		assertEquals(join, store2.join(store1));
		assertEquals(n32b, join.get(MemoryRegion.GLOBAL, 120, 32));
		assertEquals(n32b, join.get(alloc2, -10, 32));
		assertEquals(valueFactory.createTop(16), join.get(alloc1, 2, 16));
		assertEquals(join, store2.join(store1));
	}

	@Test
	public void testIsTop() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		store.setTop(MemoryRegion.GLOBAL);
		assertTrue(store.isTop());
		store.set(MemoryRegion.STACK, -8, 32, n32);
		assertFalse(store.isTop());
		store.set(MemoryRegion.STACK, -8, 32, valueFactory.createTop(32));
		assertTrue(store.isTop());
	}

	@Test
	public void testLessOrEqual() {
		PartitionedMemory<NumberElement> store1 = new PartitionedMemory<NumberElement>(
				valueFactory);
		PartitionedMemory<NumberElement> store2 = new PartitionedMemory<NumberElement>(
				valueFactory);
		assertTrue(store1.lessOrEqual(store2));
		assertTrue(store2.lessOrEqual(store1));
		store1.set(alloc1, 2, 16, n16);
		assertTrue(store1.lessOrEqual(store2));
		assertFalse(store2.lessOrEqual(store1));
		store2.set(MemoryRegion.STACK, 120, 32, n32c);
		assertFalse(store1.lessOrEqual(store2));
		store1.set(alloc1, 2, 32, valueFactory.createTop(32));
		assertTrue(store2.lessOrEqual(store1));
	}

	@Test
	public void testEquals() {
		PartitionedMemory<NumberElement> store1 = new PartitionedMemory<NumberElement>(
				valueFactory);
		PartitionedMemory<NumberElement> store2 = new PartitionedMemory<NumberElement>(
				valueFactory);

		store1.set(MemoryRegion.STACK, 120, 32, n32b);
		assertFalse(store1.equals(store2));
		store1.set(MemoryRegion.STACK, 120, 32, valueFactory.createTop(32));
		assertEquals(store1, store2);

		assertEquals(store1, store2);		
		store1.set(alloc1, 120, 32, n32b);
		assertFalse(store1.equals(store2));
		store1.set(alloc1, 120, 32, valueFactory.createTop(32));
		if (!Options.initHeapToBot.getValue())
			assertEquals(store1, store2);
		store1 = new PartitionedMemory<NumberElement>(
				valueFactory);
		
		store1.set(alloc1, 120, 32, n32b);
		store2.set(alloc2, 120, 32, n32b);
		assertFalse(store1.equals(store2));
		store1.set(alloc2, 120, 32, n32c);
		store2.set(alloc1, 120, 32, n32c);
		assertEquals(store1, store2);
		
		store1.set(alloc1, 121, 8, valueFactory.createTop(8));
		store2.set(alloc1, 121, 16, valueFactory.createTop(16));
		if (!Options.initHeapToBot.getValue())
			assertEquals(store1, store2);
	}
	
	@Test
	public void testExtractBytesFromStore() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		NumberElement b2 = new NumberElement(ExpressionFactory.createNumber(2, 8));
		NumberElement b7 = new NumberElement(ExpressionFactory.createNumber(7, 8));
		NumberElement dComb = new NumberElement(ExpressionFactory.createNumber(0x02070202, 32));
		
		store.set(MemoryRegion.STACK, 16, 32, dComb);
		
		assertEquals(b2, store.get(MemoryRegion.STACK, 16, 8));
		assertEquals(b2, store.get(MemoryRegion.STACK, 17, 8));
		assertEquals(b7, store.get(MemoryRegion.STACK, 18, 8));
		assertEquals(b2, store.get(MemoryRegion.STACK, 19, 8));
	}

	@Test
	public void testCombineBytesFromStore() {
		PartitionedMemory<NumberElement> store = new PartitionedMemory<NumberElement>(
				valueFactory);
		NumberElement b2 = new NumberElement(ExpressionFactory.createNumber(2, 8));
		NumberElement b7 = new NumberElement(ExpressionFactory.createNumber(7, 8));
		NumberElement wComb = new NumberElement(ExpressionFactory.createNumber(0x0207, 16));
		NumberElement dComb = new NumberElement(ExpressionFactory.createNumber(0x02070202, 32));
		
		store.set(MemoryRegion.STACK, 16, 8, b2);
		store.set(MemoryRegion.STACK, 17, 8, b2);
		store.set(MemoryRegion.STACK, 18, 8, b7);
		store.set(MemoryRegion.STACK, 19, 8, b2);
		assertEquals(wComb, store.get(MemoryRegion.STACK, 18, 16));
		assertEquals(dComb, store.get(MemoryRegion.STACK, 16, 32));
	}

}
