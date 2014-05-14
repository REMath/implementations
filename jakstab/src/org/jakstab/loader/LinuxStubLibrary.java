/*
 * LinuxStubLibrary.java - This file is part of the Jakstab project.
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
package org.jakstab.loader;

import java.util.HashMap;
import java.util.Map;

import org.jakstab.Program;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.DummySymbolFinder;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLSpecialExpression;
import org.jakstab.rtl.statements.*;
import org.jakstab.rtl.statements.RTLGoto.Type;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class LinuxStubLibrary implements StubProvider {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(LinuxStubLibrary.class);
	
	private Map<String,AbsoluteAddress> activeStubs;
	private int impId;
	private Architecture arch;
	private RTLExpression arg0;
	//private RTLExpression arg1;

	public LinuxStubLibrary(Architecture arch) {
		this.arch = arch;
		activeStubs = new HashMap<String, AbsoluteAddress>();
		impId = 0;
		arg0 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(arch.stackPointer(), ExpressionFactory.createNumber(4, 32)), 32);
		//arg1 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(arch.stackPointer(), ExpressionFactory.createNumber(8, 32)), 32);
	}
	
	private AbsoluteAddress createStubInstance(String library, String function) {
		int stackIncrement = 0;
		boolean returns = true;
		if (function.equals("exit")) {
			returns = false;
		}
		
		impId += 0x10;
		AbsoluteAddress address = new AbsoluteAddress(STUB_BASE + impId);
		
		// pop PC
		stackIncrement += arch.programCounter().getBitWidth() / 8;
		
		StatementSequence seq = new StatementSequence();
		
		// start_main is special
		if (function.equals("__libc_start_main")) {
			seq.addLast(new RTLGoto(arg0, Type.CALL));
		} else if (function.equals("printf")) {
			seq.addLast(new RTLDebugPrint("Call to printf, format @ %esp =", 
					ExpressionFactory.createSpecialExpression(RTLSpecialExpression.DBG_PRINTF, 
							ExpressionFactory.createPlus(arch.stackPointer(),
									ExpressionFactory.createNumber(4, arch.getAddressBitWidth())))));
		} else {
			seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), ExpressionFactory.nondet(32)));
			seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%ecx"), ExpressionFactory.nondet(32)));
			seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%edx"), ExpressionFactory.nondet(32)));
		}
		
		// store return address in retaddr
		if (returns) {
			seq.addLast(new RTLVariableAssignment(32, arch.returnAddressVariable(), 
					ExpressionFactory.createMemoryLocation(arch.stackPointer(), 
							arch.stackPointer().getBitWidth())
			));
		}

		
		// adjust stack pointer
		seq.addLast(new RTLVariableAssignment(arch.stackPointer().getBitWidth(), 
				arch.stackPointer(), 
				ExpressionFactory.createPlus( 
						arch.stackPointer(), 
						ExpressionFactory.createNumber(stackIncrement, arch.stackPointer().getBitWidth())
				)
		));

		if (returns) {
			// Read return address from temporary variable
			seq.addLast(new RTLGoto(Program.getProgram().getArchitecture().returnAddressVariable(), RTLGoto.Type.RETURN));
		} else {
			// artificial termination statement
			seq.addLast(new RTLHalt());
		}
		
		int rtlId = 0;
		for (RTLStatement stmt : seq) {
			stmt.setLabel(address, rtlId++);
			stmt.setNextLabel(new Location(address, rtlId));
		}
		seq.getLast().setNextLabel(null);

		// add stub statements to program
		for (RTLStatement s : seq)
			Program.getProgram().putStatement(s);

		return address;
	}


	/*
	 * @see org.jakstab.loader.StubProvider#resolveSymbol(java.lang.String, java.lang.String)
	 */
	@Override
	public AbsoluteAddress resolveSymbol(String library, String symbol) {
		if (library == null) return null;
		AbsoluteAddress functionAddress;
		if (activeStubs.containsKey(symbol))
			functionAddress = activeStubs.get(symbol);
		else {
			// create a new stub instance
			functionAddress = createStubInstance(library, symbol);
			activeStubs.put(symbol, functionAddress);
			logger.debug("Created new stub for " + symbol + "@" + library);
		}
		return functionAddress;
	}

	@Override
	public SymbolFinder getSymbolFinder() {
		return new DummySymbolFinder();
	}

}
