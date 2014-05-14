/*
 * YicesSolverTest.java - This file is part of the Jakstab project.
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
package org.jakstab.solver;

import static org.junit.Assert.*;

import org.jakstab.rtl.expressions.*;
import org.jakstab.solver.yices.YicesSolver;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * Tests for the basic Yices support in Jakstab. If your architecture is not supported,
 * the tests will fail.
 * 
 * @author Johannes Kinder
 */
public class YicesSolverTest {
	
	private YicesSolver solver;
	private RTLMemoryLocation m1;
	private RTLMemoryLocation m2;
	private RTLMemoryLocation m3;
	private RTLVariable esp;

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
		solver = new YicesSolver();
		esp = ExpressionFactory.createVariable("esp", 32);
		m1 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(esp, ExpressionFactory.createNumber(4, 32)), 32);
		m2 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(esp, ExpressionFactory.createNumber(8, 32)), 32);
		m3 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(esp, ExpressionFactory.createNumber(4, 32)), 32);
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Test method for {@link org.jakstab.solver.yices.YicesSolver#isSatisfiable()}.
	 */
	@Test
	public void testMemoryLocations() {
		solver.push();
		RTLExpression f = ExpressionFactory.createEqual(m1, ExpressionFactory.createNumber(254823, 32));
		solver.addAssertion(f);
		f = ExpressionFactory.createEqual(m2, ExpressionFactory.createNumber(53223, 32));
		solver.addAssertion(f);
		assertTrue(solver.isSatisfiable());
		f = ExpressionFactory.createEqual(m3, ExpressionFactory.createNumber(53223, 32));
		solver.addAssertion(f);
		assertFalse(solver.isSatisfiable());
		solver.pop();
		solver.push();
		f = ExpressionFactory.createNotEqual(m1, m2);
		solver.addAssertion(f);
		assertTrue(solver.isSatisfiable());
		f = ExpressionFactory.createEqual(m1, m2);
		solver.addAssertion(f);
		assertFalse(solver.isSatisfiable());
		solver.pop();
	}
	
	@Test
	public void testConditionals() {

		RTLExpression c = ExpressionFactory.createConditionalExpression(ExpressionFactory.createGreaterThan(esp, ExpressionFactory.createNumber(10, 32)), 
				ExpressionFactory.createNumber(10, 32), 
				ExpressionFactory.createNumber(5, 32));
		RTLExpression f = ExpressionFactory.createEqual(ExpressionFactory.createVariable("x", 32), c);
		solver.addAssertion(f);
		assertTrue(solver.isSatisfiable());
	}
	
	@Test
	public void testContextCreation() {
		for (int i = 0; i < 1000; i++) {
			Solver solver = Solver.createSolver();
			solver.isSatisfiable();
		}
	}

}
