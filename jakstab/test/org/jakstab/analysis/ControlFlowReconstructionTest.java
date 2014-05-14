/*
 * ControlFlowReconstructionTest.java - This file is part of the Jakstab project.
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

import java.io.File;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.analysis.ControlFlowReconstruction;
import org.jakstab.loader.DefaultHarness;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Johannes Kinder
 */
public class ControlFlowReconstructionTest {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ControlFlowReconstructionTest.class);

	private static Architecture arch;

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
		arch = new Architecture("ssl/pentium.ssl");
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
	}
	
	private void checkProgram(String file, int numEdges, int numInstructions, int numStatements, boolean checkCompleteness) throws Exception {
		checkProgram(file, numEdges, numInstructions, numStatements, checkCompleteness, "x");
	}

	private void checkProgram(String file, int numEdges, int numInstructions, int numStatements, boolean checkCompleteness, String cpa) throws Exception {
		
		Options.cpas.setValue(cpa);
		
		File peFile = new File(Options.jakstabHome + "/input/bin/" + file);
		logger.info("----------");
		logger.info("Testing " + peFile);
		
		Program program = Program.createProgram(arch);
		program.loadMainModule(peFile);
		program.installHarness(new DefaultHarness());
		ControlFlowReconstruction cfr = new ControlFlowReconstruction(program);
		cfr.run();

		assertEquals(numInstructions, program.getAssemblyMap().size());
		assertEquals(numStatements, program.getStatements().size());
		assertTrue("Not enough edges!", numEdges <= program.getCFA().size());
		if (checkCompleteness) 
			assertTrue("Analysis timed out when it should not!", cfr.isCompleted());
	}

	@Test
	public void test_helloworld() throws Exception {
		checkProgram("helloworld.exe", 154, 52, 155, true);
	}

	@Test
	public void test_hw_KSets_ContextSensitive() throws Exception {
		checkProgram("helloworld.exe", 154, 52, 155, true, "ks");
	}

	@Test
	public void test_interproc() throws Exception {
		checkProgram("interproc.exe", 21, 8, 27, true);
	}

	@Test
	public void test_memory() throws Exception {
		checkProgram("memory.exe", 141, 49, 142, true);
	}
	
	@Test
	public void test_overlap() throws Exception {
		checkProgram("overlap.exe", 130, 46, 130, true);
	}

	@Test
	public void test_pointer_arithmetic() throws Exception {
		checkProgram("pointer_arithmetic.exe", 146, 48, 147, true);
	}

	@Test
	public void test_vmcai_demo() throws Exception {
		checkProgram("vmcai_demo.exe", 33, 9, 32, true);
	}

	@Test
	public void test_vmcai_demo_KSets() throws Exception {
		checkProgram("vmcai_demo.exe", 33, 9, 32, true, "k");
	}

	@Test
	public void test_loop() throws Exception {
		checkProgram("loop.exe", 24, 5, 24, true);
	}

	@Test
	public void test_localPrecision() throws Exception {
		checkProgram("localprecision.exe", 26, 9, 33, true);
	}
	
	@Test
	public void test_regionPrecision() throws Exception {
		checkProgram("regionprecision.exe", 137, 51, 134, true, "x");
	}

	@Test
	public void test_jumptable_intervals() throws Exception {
		checkProgram("jumptable.exe", 136, 53, 130, true, "xfi");
	}
}
