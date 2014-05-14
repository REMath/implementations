/*
 * HashMapMapTest.java - This file is part of the Jakstab project.
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

import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Johannes Kinder
 */
public class HashMapMapTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(HashMapMapTest.class);

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Test method for {@link org.jakstab.util.HashMapMap#HashMapMap(org.jakstab.util.MapMap)}.
	 */
	@Test
	public void testHashMapMapCopyConstructor() {
		MapMap<Integer, Integer, Integer> map1 = new HashMapMap<Integer, Integer, Integer>();
		map1.put(4, 3, 8);
		map1.put(4, 3, 8);
		map1.put(2, 3, 8);
		map1.getSubMap(4).clear();
		MapMap<Integer, Integer, Integer> map2 = 
			new HashMapMap<Integer, Integer, Integer>(map1);
		assertEquals(map1, map2);
	}

}
