/*
 * HeuristicHarness.java - This file is part of the Jakstab project.
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

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.jakstab.Program;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.loader.pe.AbstractCOFFModule;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;

public class HeuristicHarness implements Harness {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(HeuristicHarness.class);
	
	private static int CALL_INSTR_DISTANCE = 1;
	
	private static byte[][] procedureHeads = new byte[][] {
		// mov edi, edi; push ebp; mov ebp, esp;
		{ -0x75, -0x01, 0x55, -0x75, -0x14},
		// push ebp; mov ebp, esp;
		{ 0x55, -0x75, -0x14 }
	};
	
	private long PROLOGUE_BASE = 0xface0000L;
	private long EPILOGUE_BASE = 0xfee70000L;
	private AbsoluteAddress prologueAddress = new AbsoluteAddress(PROLOGUE_BASE);
	private AbsoluteAddress epilogueAddress = new AbsoluteAddress(EPILOGUE_BASE);
	private AbsoluteAddress lastAddress;


	private RTLVariable esp = Program.getProgram().getArchitecture().stackPointer();
	
	private List<AbsoluteAddress> entryPoints;
	
	public HeuristicHarness() {
		entryPoints = new LinkedList<AbsoluteAddress>();
		
		Program program = Program.getProgram();
		
		if (program.getMainModule() instanceof AbstractCOFFModule) {
		byte[] data = ((AbstractCOFFModule)program.getMainModule()).getByteArray();
		for (int filePtr=0; filePtr<data.length; filePtr++) {
			patternLoop: for (int patternIdx = 0; patternIdx < procedureHeads.length; patternIdx++) {
				for (int i = 0; i < procedureHeads[patternIdx].length; i++) {
					if (data[filePtr + i] != procedureHeads[patternIdx][i])
						continue patternLoop;
				}
				// Pattern matched!
				AbsoluteAddress newEntryPoint = program.getMainModule().getVirtualAddress(filePtr);
				entryPoints.add(newEntryPoint);
				logger.verbose("Found possible procedure entry at " + newEntryPoint); 
				filePtr += procedureHeads[patternIdx].length;
				break;
			}
		}
		}
	}
	
	@Override
	public void install(Program program) {

		StatementSequence seq = new StatementSequence();
		seq.addLast(new RTLVariableAssignment(1, ExpressionFactory.createVariable("%DF", 1), ExpressionFactory.FALSE));

		AbsoluteAddress currentAddress = prologueAddress;
		AbsoluteAddress fallthroughAddress = new AbsoluteAddress(currentAddress.getValue() + CALL_INSTR_DISTANCE);
		
		// Call the entry point of the executable
		push32(seq, ExpressionFactory.createNumber(fallthroughAddress.getValue(), 32));
		seq.addLast(new RTLGoto(ExpressionFactory.createNumber(program.getStart().getAddress().getValue(), 32), RTLGoto.Type.CALL));
		putSequence(program, seq, currentAddress);
		program.setEntryAddress(currentAddress);
		
		// Now call all procedures that were heuristically detected

		for (Iterator<AbsoluteAddress> iter = entryPoints.iterator(); iter.hasNext();) {
			AbsoluteAddress entryPoint = iter.next();
			currentAddress = fallthroughAddress;
			fallthroughAddress = iter.hasNext() ? new AbsoluteAddress(currentAddress.getValue() + 1) : prologueAddress;
			seq = new StatementSequence();

			for (RTLVariable v : program.getArchitecture().getRegisters()) {
				if (!v.equals(esp))
					clearReg(seq, v);
			}
			push32(seq, ExpressionFactory.createNumber(fallthroughAddress.getValue(), 32));
			seq.addLast(new RTLGoto(ExpressionFactory.createNumber(entryPoint.getValue(), 32), RTLGoto.Type.CALL));
			putSequence(program, seq, currentAddress);
		}
		
		lastAddress = currentAddress;

		// epilogue with halt statement
		seq = new StatementSequence();
		//seq.addLast(new RTLSkip());
		seq.addLast(new RTLHalt());
		putSequence(program, seq, epilogueAddress);
	}
	
	private void push32(StatementSequence seq, RTLExpression value) {
		seq.addLast(new RTLVariableAssignment(esp.getBitWidth(), esp, 
				ExpressionFactory.createPlus(esp, ExpressionFactory.createNumber(-4, esp.getBitWidth()))
		));
		if (value != null) {
			seq.addLast(new RTLMemoryAssignment(ExpressionFactory.createMemoryLocation(esp, 32), value));
		}
	}
	
	private void clearReg(StatementSequence seq, RTLVariable v) {
		seq.addLast(new RTLVariableAssignment(v.getBitWidth(), v, ExpressionFactory.nondet(v.getBitWidth())));
	}
	
	private void putSequence(Program program, StatementSequence seq, AbsoluteAddress address) {
		int rtlId = 0;
		for (RTLStatement stmt : seq) {
			stmt.setLabel(address, rtlId++);
			stmt.setNextLabel(new Location(address, rtlId));
		}
		seq.getLast().setNextLabel(null);

		// add stub statements to program
		for (RTLStatement s : seq)
			program.putStatement(s);
	}

	@Override
	public boolean contains(AbsoluteAddress a) {
		return a.getValue() >= PROLOGUE_BASE && a.getValue() <= lastAddress.getValue();
	}

	@Override
	public AbsoluteAddress getFallthroughAddress(AbsoluteAddress a) {
		if (a.getValue() >= PROLOGUE_BASE && a.getValue() < lastAddress.getValue())
			return new AbsoluteAddress(a.getValue() + CALL_INSTR_DISTANCE);
		else if (a.equals(lastAddress))
			return epilogueAddress;
		else 
			return null;
	}

}
