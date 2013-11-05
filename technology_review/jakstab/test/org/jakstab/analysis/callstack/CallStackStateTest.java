/*
 * CallStackStateTest.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.callstack;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.LinkedList;

import org.jakstab.Program;
import org.jakstab.analysis.callstack.CallStackState;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.Location;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class CallStackStateTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CallStackStateTest.class);

	private static CallStackState s1;
	private static CallStackState s2;
	private static CallStackState s3;
	private static CallStackState s4;
	private static Location l1;
	private static Location l2;
	private static Location l3;
	private static Location l4;

	
	@Before
	public void setUp() throws Exception {
		Program.createProgram(new Architecture("ssl/pentium.ssl"));

		l1 = new Location(new AbsoluteAddress(0x12345678));
		l2 = new Location(new AbsoluteAddress(0xFF241111));
		l3 = new Location(new AbsoluteAddress(0xEE345678));
		l4 = new Location(new AbsoluteAddress(0xDD345678));
		
		s1 = new CallStackState(new LinkedList<Location>(Arrays.asList(l1, l2, l3, l4)));
		s2 = new CallStackState(new LinkedList<Location>(Arrays.asList(l1, l2, l3, l4)));
		s3 = new CallStackState(new LinkedList<Location>(Arrays.asList(l3, l2)));
		s4 = new CallStackState(new LinkedList<Location>());
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testJoin() {
		assertEquals(s3, CallStackState.BOT.join(s3));
		assertEquals(CallStackState.TOP, s1.join(s3)); 
		assertEquals(CallStackState.TOP, s1.join(s4)); 
		assertEquals(s2, s1.join(s2)); 
		assertNotSame(s2, s1.join(s2)); 
		assertSame(s1, s1.join(s2)); 
		assertSame(CallStackState.TOP, CallStackState.TOP.join(s3));
	}

	@Test
	public void testLessOrEqual() {
		assertTrue(s1.lessOrEqual(s2));
		assertTrue(s1.lessOrEqual(CallStackState.TOP));
		assertTrue(s2.lessOrEqual(CallStackState.TOP));
		assertTrue(s3.lessOrEqual(CallStackState.TOP));
		assertTrue(s4.lessOrEqual(CallStackState.TOP));
		assertFalse(CallStackState.TOP.lessOrEqual(s2));
		assertFalse(s3.lessOrEqual(s2));
		assertFalse(s3.lessOrEqual(s4));
		assertFalse(s4.lessOrEqual(s3));
		assertFalse(s2.lessOrEqual(s3));
	}

	@Test
	public void testEqualsObject() {
		assertEquals(s1, s2);
		assertFalse(s1.equals(s3));
	}

}
