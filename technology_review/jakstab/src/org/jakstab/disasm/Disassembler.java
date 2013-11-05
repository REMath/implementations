/*
 * Disassembler.java - This file is part of the Jakstab project.
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
package org.jakstab.disasm;

import org.jakstab.asm.Instruction;

/**
 * @author Johannes Kinder
 */
public interface Disassembler {

	/**
	 * Disassembles one instruction at the given index in the code array. 
	 * 
	 * @return instr The disassembled instruction, null on failure.
	 */
	public Instruction decodeInstruction(long fp);
}
