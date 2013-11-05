/*
 * RelocationEntry.java - This file is part of the Jakstab project.
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
package org.jakstab.loader.pe;

import java.io.IOException;

import org.jakstab.util.BinaryInputBuffer;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
@SuppressWarnings("unused")
class RelocationEntry {

	private static final Logger logger = Logger.getLogger(RelocationEntry.class);
	
	private static final int IMAGE_REL_I386_ABSOLUTE = 0x0000; // The relocation is ignored.
	private static final int IMAGE_REL_I386_DIR16 = 0x0001;    // Not supported.
	private static final int IMAGE_REL_I386_REL16 = 0x0002;    // Not supported.
	private static final int IMAGE_REL_I386_DIR32 = 0x0006;    // The target's 32 bit VA.
	private static final int IMAGE_REL_I386_DIR32NB = 0x0007;  // The target's 32 bit RVA.
	private static final int IMAGE_REL_I386_SEG12 = 0x0009;    // Not supported.
	private static final int IMAGE_REL_I386_SECTION = 0x000A;  // The 16 bit section index of the section that contains the target. This is used to support debugging information.
	private static final int IMAGE_REL_I386_SECREL = 0x000B;   // The 32 bit offset of the target from the beginning of its section. This is used to support debugging information and static thread local storage.
	private static final int IMAGE_REL_I386_TOKEN = 0x000C;    // The CLR token.
	private static final int IMAGE_REL_I386_SECREL7 = 0x000D;  // A 7 bit offset from the base of the section that contains the target.
	private static final int IMAGE_REL_I386_REL32 = 0x0014;    // The 32 bit relative displacement to the target. This supports the x86 relative branch and call instructions.
	
	private final long rva;
	private final int tableIndex;
	private final int type;
	
	public RelocationEntry(BinaryInputBuffer inBuf) throws IOException {
		rva = inBuf.readDWORD();
		tableIndex = inBuf.readINT32();
		type = inBuf.readINT16();
	}

	@Override
	public String toString() {
		return "RVA = " + rva + " tableIndex = " + tableIndex + " type " + type;
	}

	public long getRVA() {
		return rva;
	}

	public int getTableIndex() {
		return tableIndex;
	}
	
	public boolean isRelativeDisplacement() {
		return type == IMAGE_REL_I386_REL32;
	}
	
	public boolean isDirectVirtualAddress() {
		return type == IMAGE_REL_I386_DIR32;
	}
	
}
