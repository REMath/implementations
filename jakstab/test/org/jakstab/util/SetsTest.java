/*
 * SetsTest.java - This file is part of the Jakstab project.
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.jakstab.util.Logger;
import org.junit.Test;

public class SetsTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SetsTest.class);

	@Test
	public void testCrossProduct() {
		Set<Integer> set1 = new HashSet<Integer>(Arrays.asList(new Integer[]{1, 2, 3}));
		Set<Integer> set2 = new HashSet<Integer>(Arrays.asList(new Integer[]{5, 6, 7}));
		Tuple<Set<Integer>> tuple = new Tuple<Set<Integer>>(2);
		tuple.set(0, set1);
		tuple.set(1, set2);
		Set<Tuple<Integer>> result = Sets.crossProduct(tuple);
		Set<Tuple<Integer>> expected = new HashSet<Tuple<Integer>>();
		expected.add(Tuple.create(1, 5));
		expected.add(Tuple.create(2, 5));
		expected.add(Tuple.create(3, 5));
		expected.add(Tuple.create(1, 6));
		expected.add(Tuple.create(2, 6));
		expected.add(Tuple.create(3, 6));
		expected.add(Tuple.create(1, 7));
		expected.add(Tuple.create(2, 7));
		expected.add(Tuple.create(3, 7));
		
		assertEquals(expected, result);
	}

}
