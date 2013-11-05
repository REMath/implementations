/*
 * FastSetTest.java - This file is part of the Jakstab project.
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
import org.junit.Test;

public class FastSetTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(FastSetTest.class);

	@Test
	public void testAddContains() {
		FastSet<Integer> set = new FastSet<Integer>();
		set.add(5);
		assertTrue(set.contains(5));
		assertFalse(set.add(5));
		assertTrue(set.contains(5));
		assertFalse(set.contains(3));
		set.add(3);
		assertTrue(set.contains(5));
	}

}
