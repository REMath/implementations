/*
 * LazyTreeMapTest.java - This file is part of the Jakstab project.
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

import com.google.common.collect.Maps;

public class LazyTreeMapTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(LazyTreeMapTest.class);

	private LazyTreeMap<Integer, Integer> map1;
	private LazyTreeMap<Integer, Integer> map2;
	private LazyTreeMap<Integer, Integer> map3;
	
	@Before
	public void setUp() throws Exception {
		map1 = new LazyTreeMap<Integer, Integer>();
		map1.put(5, -15);
		map1.put(10, -30);
		map1.put(-2, 6);
		map2 = new LazyTreeMap<Integer, Integer>(map1);
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testClear() {
		map2.clear();
		assertEquals(-15, map1.get(5).intValue());
		assertEquals(null, map2.get(5));
	}

	@Test
	public void testLazyTreeMapLazyTreeMapOfKV() {
		map3 = new LazyTreeMap<Integer, Integer>(map2);
		assertEquals(map3, map1);
	}

	@Test
	public void testPutKV() {
		map1.put(2, -6);
		assertEquals(-6, map1.get(2).intValue());
		assertEquals(null, map2.get(2));
	}
	
	@Test
	public void testEntrySet() {
		assertEquals(3, map2.entrySet().size());
		map2.entrySet().remove(Maps.immutableEntry(5, -15));
		assertFalse(map2.containsKey(5));
		assertTrue(map1.containsKey(5));
		assertTrue(map2.containsKey(-2));
		assertTrue(map2.containsKey(10));
	}
	
	@Test
	public void testEntrySetIterator() {
		
		for (Iterator<Map.Entry<Integer,Integer>> it = map1.entrySet().iterator(); 
		it.hasNext();) {
			Map.Entry<Integer,Integer> entry = it.next();
			if (entry.getKey() < 0)
				it.remove();
		}
		assertFalse(map1.containsKey(-2));
		assertTrue(map2.containsKey(-2));
		assertTrue(map1.containsKey(5));
		assertTrue(map1.containsKey(10));
	}

}
