/*
 * RawModule.java - This file is part of the Jakstab project.
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

import java.io.*;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.DummySymbolFinder;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.disasm.Disassembler;
import org.jakstab.disasm.x86.X86Disassembler;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.BinaryFileInputBuffer;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class RawModule implements ExecutableImage {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RawModule.class);
	
	private final BinaryFileInputBuffer inBuf;
	private final AbsoluteAddress baseAddress;
	private Disassembler disassembler;

	public RawModule(File file, Architecture architecture) throws IOException {
		logger.info("Loading image as raw binary...");
		InputStream inStream = new FileInputStream(file);
		inBuf = new BinaryFileInputBuffer(inStream);
		baseAddress = new AbsoluteAddress(0x0);
	}

	@Override
	public Disassembler getDisassembler() {
		if (disassembler == null) {
			disassembler = new X86Disassembler(inBuf);
		}
		return disassembler;
	}

	@Override
	public AbsoluteAddress getEntryPoint() {
		return baseAddress;
	}

	@Override
	public Set<ExportedSymbol> getExportedSymbols() {
		return Collections.emptySet();
	}

	@Override
	public long getFilePointer(AbsoluteAddress va) {
		return va.getValue() - baseAddress.getValue();
	}

	@Override
	public AbsoluteAddress getMaxAddress() {
		return new AbsoluteAddress(baseAddress.getValue() + inBuf.getSize());
	}

	@Override
	public AbsoluteAddress getMinAddress() {
		return baseAddress;
	}

	@Override
	public SymbolFinder getSymbolFinder() {
		return new DummySymbolFinder();
	}

	@Override
	public Set<UnresolvedSymbol> getUnresolvedSymbols() {
		return Collections.emptySet();
	}

	@Override
	public AbsoluteAddress getVirtualAddress(long fp) {
		return new AbsoluteAddress(baseAddress.getValue() + fp);
	}

	@Override
	public boolean isCodeArea(AbsoluteAddress va) {
		return true;
	}

	@Override
	public boolean isReadOnly(AbsoluteAddress a) {
		return false;
	}

	@Override
	public RTLNumber readMemoryLocation(RTLMemoryLocation m) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterator<AbsoluteAddress> codeBytesIterator() {
		throw new UnsupportedOperationException("Code iteration not yet implemented for " + this.getClass().getSimpleName() + "!");
	}

	@Override
	public byte[] getByteArray() {
		return inBuf.getByteArray();
	}

}
