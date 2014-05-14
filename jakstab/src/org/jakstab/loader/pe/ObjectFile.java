/*
 * ObjectFile.java - This file is part of the Jakstab project.
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

import java.io.*;
import java.util.*;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.DummySymbolFinder;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.loader.BinaryParseException;
import org.jakstab.loader.ExportedSymbol;
import org.jakstab.loader.UnresolvedSymbol;
import org.jakstab.loader.UnresolvedSymbol.AddressingType;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.BinaryFileInputBuffer;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ObjectFile extends AbstractCOFFModule {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ObjectFile.class);
	private static final int SYMBOL_LENGTH = 18;
	private static final String MAIN_FUNCTION = "_main";
	
	private final long imageBase;
	private int codeSection;
	private final SymbolEntry[] symbolTable;
	private final RelocationEntry[] relocations;
	private long addressOfMain;
	private final AbsoluteAddress entryPoint;
	private Set<UnresolvedSymbol> unresolvedSymbols;
	
	
	public ObjectFile(File peFile, Architecture arch) throws java.io.IOException, BinaryParseException {
		this(new FileInputStream(peFile), arch);
	}

	
	public ObjectFile(InputStream inStream, Architecture arch) throws java.io.IOException, BinaryParseException {

		imageBase = 0x1000;
		inBuf = new BinaryFileInputBuffer(inStream);

		coff_header = new COFF_Header(inBuf);
		logger.debug("Reading " + coff_header.getNumberOfSections() + " sections.");

		///// Parse Section Headers and sections /////////////////////////
		section_headers = new SectionHeader[coff_header.getNumberOfSections()];
		codeSection = -1;
		
		// Allocate section RVAs in sequence
		long currentRVA = 0;
		
		// Section indices are 1-based in the COFF specification - here we have
		// a 0-based array!
		for (int i=0;i<coff_header.getNumberOfSections();i++){
			SectionHeader sectionHeader = new SectionHeader(inBuf);
			section_headers[i] = sectionHeader;
			if (sectionHeader.getName().equals(".text") && !sectionHeader.hasComdat())
				codeSection = i;
			logger.debug("  Read section " + (i+1) + ": " + sectionHeader.getName());
			
			// Allocate virtual address for section
			if (!sectionHeader.isRemovedByLinker() && !sectionHeader.isDiscardable()) {
				sectionHeader.VirtualAddress = currentRVA;
				sectionHeader.VirtualSize = sectionHeader.SizeOfRawData;
				currentRVA += sectionHeader.VirtualSize;
				logger.debug("Allocated section " + sectionHeader.getName() + " at RVA 0x" + 
						Integer.toHexString((int)sectionHeader.VirtualAddress));
			}
		}
		/////////////////////////////////////////////////////////////////
		if (codeSection < 0) {
			throw new BinaryParseException("No code section found in object file!");
		}
		
		/////////////////////////////////////////////////////////////////
		// Read string table for symbols
		Map<Integer,String> stringTable = new HashMap<Integer, String>();
		if (coff_header.getNumberOfSymbols() > 0) {
			long stringTableOffset = coff_header.getPointerToSymbolTable() + coff_header.getNumberOfSymbols() * SYMBOL_LENGTH;
			inBuf.seek(stringTableOffset);
			int stringTableSize = inBuf.readINT32();
			while (inBuf.getCurrent() < stringTableOffset + stringTableSize) {
				int stringOffset = (int)(inBuf.getCurrent() - stringTableOffset);
				String string = inBuf.readASCII();
				stringTable.put(stringOffset, string);
			}
		}
		
		/////////////////////////////////////////////////////////////////
		// Parse symbols
		logger.debug("Parsing symbol table");
		addressOfMain = -1;
		symbolTable = new SymbolEntry[coff_header.getNumberOfSymbols()];
		if (coff_header.getNumberOfSymbols() > 0) {
			inBuf.seek(coff_header.getPointerToSymbolTable());
			for (int i = 0; i < coff_header.getNumberOfSymbols(); i++) {
				symbolTable[i] = new SymbolEntry(inBuf, stringTable);
				
				if (symbolTable[i].getName().equals(MAIN_FUNCTION)) {
					// The value field contains the offset from the section start
					addressOfMain = symbolTable[i].getValue() + 
					section_headers[symbolTable[i].getSectionNumber() - 1].VirtualAddress;
				}
				//logger.debug("  Symbol entry: " + symbolTable[i]);
			}
			if (addressOfMain < 0) logger.warn("No main function found in object file!");

		}
		entryPoint = new AbsoluteAddress(imageBase + addressOfMain);
		logger.debug("Main function at " + entryPoint);
		
		/////////////////////////////////////////////////////////////////
		// Parse and perform relocations
		SectionHeader csHead = getSectionHeader(codeSection);
		relocations = new RelocationEntry[csHead.NumberOfRelocations];
		unresolvedSymbols = new FastSet<UnresolvedSymbol>();
		if (csHead.NumberOfRelocations > 0) {
			logger.debug("Relocations: ");
			inBuf.seek(csHead.PointerToRelocations);
			for (int i = 0; i < csHead.NumberOfRelocations; i++) {
				relocations[i] = new RelocationEntry(inBuf);
				
				SymbolEntry symbolEntry = symbolTable[relocations[i].getTableIndex()];
				
				logger.debug("  RVA 0x" + Integer.toHexString((int)(relocations[i].getRVA() + csHead.VirtualAddress)) + ": make " + 
						(relocations[i].isDirectVirtualAddress() ? "direct" : "relative") + 
						" to " + symbolEntry);
				
				// Mark relocation entries to external symbols as unresolved, so
				// the resolution mechanism in the Program class takes care of them
				UnresolvedSymbol.AddressingType mode;
				if (relocations[i].isDirectVirtualAddress()) mode = AddressingType.ABSOLUTE;
				else if (relocations[i].isRelativeDisplacement()) mode = AddressingType.PC_RELATIVE;
				else throw new RuntimeException("Unknown addressing type for unresolved symbol " + relocations[i].toString());

				String name = symbolEntry.getName();
				name = stripSymbolName(name);

				UnresolvedSymbol unresolvedSymbol = new UnresolvedSymbol(
						this, 
						name,
						(int)(getFilePointerFromRVA(relocations[i].getRVA() + csHead.VirtualAddress)),
						mode
				);
				// If it's an external symbol, rely on the Program class to resolve it
				if (symbolEntry.isExternal()) {
					logger.debug("  -- Marking as external reference");
					unresolvedSymbols.add(unresolvedSymbol); 
				} else {
					// Otherwise, perform relocation now
					logger.debug("  -- Relocating " + symbolEntry.getName());
					AbsoluteAddress relocatedAddress = new AbsoluteAddress(
							symbolEntry.getValue() + imageBase + 
							section_headers[symbolEntry.getSectionNumber() - 1].VirtualAddress
							);
					logger.debug("  New address: " + relocatedAddress);
					unresolvedSymbol.resolve(relocatedAddress);
				}
			}
		}

		inBuf = null;

	}
	
	/*
	 * @see org.jakstab.loader.ExecutableImage#getEntryPoint()
	 */
	@Override
	public AbsoluteAddress getEntryPoint() {
		return entryPoint;
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#isReadOnly(org.jakstab.asm.AbsoluteAddress)
	 */
	@Override
	public boolean isReadOnly(AbsoluteAddress a) {
		return false;
		//throw new UnsupportedOperationException();
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#readMemoryLocation(org.jakstab.rtl.expressions.RTLMemoryLocation)
	 */
	@Override
	public RTLNumber readMemoryLocation(RTLMemoryLocation m) throws IOException {
		if (!(m.getAddress() instanceof RTLNumber)) return null;
		
		// AbsoluteAddress va = new AbsoluteAddress((RTLNumber)m.getAddress());

		// Do some symbol magic and possibly return something

		return super.readMemoryLocation(m);
	}


	@Override
	public SymbolFinder getSymbolFinder() {
		return new DummySymbolFinder();
	}


	@Override
	protected final long getBaseAddress() {
		return imageBase;
	}
	
	@Override
	protected final int getSectionNumberByRVA(long rva) {
		if (rva < 0) return -1;
		for (int i=0; i < getNumberOfSections(); i++) {
			SectionHeader sh = getSectionHeader(i);
			// Only look for sections that are actually loaded
			if (sh.isDiscardable() || sh.isRemovedByLinker())
				continue;
			if (sh.VirtualAddress <= rva && 
					(sh.VirtualAddress + sh.VirtualSize) > rva) {
				return i;
			}
		}
		return -1;
	}


	@Override
	public Set<UnresolvedSymbol> getUnresolvedSymbols() {
		return unresolvedSymbols;
	}
	
	@Override
	public Set<ExportedSymbol> getExportedSymbols() {
		Set<ExportedSymbol> exportedSymbols = new FastSet<ExportedSymbol>();
		
		for (int i = 0; i < coff_header.getNumberOfSymbols(); i++) {
			if (symbolTable[i].isExternal()	&& symbolTable[i].getSectionNumber() > 0) {
				String name = symbolTable[i].getName();
				// section number is 1-based in symbol table
				int section = symbolTable[i].getSectionNumber() - 1;

				//logger.debug("Locating symbol " + name);
				
				name = stripSymbolName(name);
				long fp = getSectionHeader(section).PointerToRawData + symbolTable[i].getValue();
				
				AbsoluteAddress address = getVirtualAddress(fp);
				exportedSymbols.add(new ExportedSymbol(this, name, address));
				logger.debug("Exporting " + name + " at file offset " + fp + ", section offset " + 
						symbolTable[i].getValue() + " in " + section_headers[section].getName() + ", which evaluates to VA " + address);

			}
			i += symbolTable[i].getNumberOfAuxSymbols();
		}		
		
		return exportedSymbols;
	}


	private String stripSymbolName(String symbolName) {
		String name = symbolName;
		
		// Strip calling convention prefix
		if (name.startsWith("@")) name = name.substring(1);
		// Strip a leading underscore generated by some compilers
		if (name.startsWith("_")) name = name.substring(1);
		// Strip trailing stack increment
		int lastAt = name.lastIndexOf('@');
		if (name.substring(lastAt + 1).matches("\\d+")) {
			name = name.substring(0, lastAt);
		}
		return name;
	}

}
