/*
 * LazyHashMapMapTest.java - This file is part of the Jakstab project.
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
package org.jakstab.util;

import static org.junit.Assert.*;

import java.util.Iterator;
import java.util.Map;

import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class LazyHashMapMapTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(LazyHashMapMapTest.class);

	LazyHashMapMap<Integer, Integer, Integer> map1;
	LazyHashMapMap<Integer, Integer, Integer> map2;
	LazyHashMapMap<Integer, Integer, Integer> map3;
	
	@Before
	public void setUp() throws Exception {
		map1 = new LazyHashMapMap<Integer, Integer, Integer>();
		map1.put(-2, 6, -18);
		map1.put(12, -36, 108);
		map1.put(12, 14, 50);
		map1.put(12, 0, 493);
		map1.put(4, -12, 36);
		map1.put(4, 22, 33);
		map2 = new LazyHashMapMap<Integer, Integer, Integer>(map1);
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testLazyHashMapMapLazyHashMapMapOfKLV() {
		map3 = new LazyHashMapMap<Integer, Integer, Integer>(map2);
		assertEquals(map1, map3);
	}

	@Test
	public void testClear() {
		map2.clear();
		assertEquals(108, map1.get(12, -36).intValue());
	}

	@Test
	public void testGetSubMap() {
		Map<Integer, Integer> twelve = map1.getSubMap(12);
		assertEquals(50, twelve.get(14).intValue());
		/*
		twelve.put(5, 3);
		assertEquals(3, map1.get(12, 5).intValue());
		assertFalse(map2.containsKey(12, 5));
		*/
	}
	
	@Test
	public void testSubMapIterator() {
		for (Iterator<Map.Entry<Integer,Integer>> it = map1.subMapIterator(12); 
		it.hasNext();) {
			Map.Entry<Integer,Integer> entry = it.next();
			if (entry.getKey() < 0)
				it.remove();
		}
		assertTrue(map1.containsKey(12, 14));
		assertTrue(map1.containsKey(12, 0));
		assertFalse(map1.containsKey(12, -36));
		assertTrue(map2.containsKey(12, 14));
		assertTrue(map2.containsKey(12, 0));
		assertTrue(map2.containsKey(12, -36));

	}

}
