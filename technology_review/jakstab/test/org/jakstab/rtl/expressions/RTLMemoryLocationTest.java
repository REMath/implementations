/*
 * RTLMemoryLocationTest.java - This file is part of the Jakstab project.
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

import org.jakstab.rtl.Context;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class RTLMemoryLocationTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLMemoryLocationTest.class);
	
	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testEvaluate() {
		RTLExpression addrExp = ExpressionFactory.createPlus(
				ExpressionFactory.createNumber(4), 
				ExpressionFactory.createVariable("x", 32), 
				ExpressionFactory.createNumber(8));
		RTLMemoryLocation memLoc32 = ExpressionFactory.createMemoryLocation(addrExp, 32);
		RTLMemoryLocation evaldMemLoc32 = (RTLMemoryLocation)memLoc32.evaluate(new Context());
		assertTrue(evaldMemLoc32.getAddress() instanceof RTLOperation);
		RTLOperation newAddrExp = (RTLOperation)evaldMemLoc32.getAddress();
		assertEquals(2, newAddrExp.getOperandCount());
	}

}
