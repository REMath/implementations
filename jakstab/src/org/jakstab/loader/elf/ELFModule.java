/*
 * ELFModule.java - This file is part of the Jakstab project.
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
package org.jakstab.loader.elf;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.*;

import org.jakstab.asm.*;
import org.jakstab.asm.x86.X86Instruction;
import org.jakstab.asm.x86.X86JmpInstruction;
import org.jakstab.asm.x86.X86MemoryOperand;
import org.jakstab.disasm.Disassembler;
import org.jakstab.disasm.x86.X86Disassembler;
import org.jakstab.loader.*;
import org.jakstab.loader.UnresolvedSymbol.AddressingType;
import org.jakstab.loader.elf.Elf.Dynamic;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.BinaryFileInputBuffer;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ELFModule implements ExecutableImage {
	
	public static final long ELF_LOAD_ADDRESS = 0x8048000L;

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ELFModule.class);

	private Elf elf;
	private BinaryFileInputBuffer inBuf;
	private Disassembler disassembler;
	private long pltStart;
	private long pltSize;
	
	private Set<UnresolvedSymbol> imports;
	private Set<String> requiredLibraries;
	private Map<AbsoluteAddress, String> symbolMap;
	private Set<ExportedSymbol> functionSymbols;

	public ELFModule(File moduleFile, Architecture architecture) throws IOException, BinaryParseException {
		
		inBuf = new BinaryFileInputBuffer(new FileInputStream(moduleFile));
		byte[] data = inBuf.getByteArray();
		elf = new Elf(moduleFile.getAbsolutePath());
		elf.loadSymbols();
		
		requiredLibraries = new FastSet<String>();
		Elf.Dynamic[] dynamics = elf.getDynamicSections(elf.getSectionByName(".dynamic"));
		for (Elf.Dynamic dyn : dynamics) {
			if (dyn.d_tag == Dynamic.DT_NEEDED) {
				requiredLibraries.add(dyn.toString());
			}
		}
		
		symbolMap = new HashMap<AbsoluteAddress, String>();
		functionSymbols = new HashSet<ExportedSymbol>();

		for (int i=0; i<elf.getSymtabSymbols().length; i++) {
			Elf.Symbol s = elf.getSymtabSymbols()[i];
			if (s.st_type() == Elf.Symbol.STT_FUNC) {
				//logger.info(i + ":\t" + s +	"\tshndx: " + s.st_shndx + "\tbind: " + s.st_bind() + "\tSize: " + s.st_size + "\tInfo: " + s.st_info +
				//		"\tType: " + s.st_type() + "\tValue: 0x" + Long.toHexString(s.st_value.getValue().longValue()));
				if (s.st_shndx > 0) {
					//logger.info(s + " " + "\t Addr: " + s.st_value.toHexAddressString() + "\t to " + s.st_value.add(s.st_size).toHexAddressString());
					AbsoluteAddress fAddr = new AbsoluteAddress(s.st_value.getValue().longValue());
					symbolMap.put(fAddr, s.toString());
					functionSymbols.add(new ExportedSymbol(this, s.toString(), fAddr));
				}
			}
		}
				
		//////////////////////////////////
		// Parse the PLT and generate imports
		
		imports = new HashSet<UnresolvedSymbol>();
		
		Elf.Section pltSection = elf.getSectionByName(".plt");
		
		// Get relocations for PLT
		
		byte[] pltRelocs = null;
		for (Elf.Section section : elf.getSections()) {
			if (section.sh_type == Elf.Section.SHT_REL || 
					section.sh_type == Elf.Section.SHT_RELA) {
				// sh_info holds the section number to which the relocation
				// info applies
				if (pltSection == elf.getSections()[(int)section.sh_info])
					pltRelocs = section.loadSectionData();
			}
		}
		assert (pltRelocs != null);
		
		int pltIdx = (int)(pltSection.sh_offset);
		pltStart = getVirtualAddress(pltIdx).getValue();
		pltSize = pltSection.sh_size;
		logger.debug("Reading PLT from " + getVirtualAddress(pltIdx));

		X86Disassembler disasm = new X86Disassembler(inBuf);
		// push GOT + 4
		Instruction instr = disasm.decodeInstruction(pltIdx);
		assert instr.getName().equals("pushl");
		pltIdx += instr.getSize();
		// jmp *(GOT + 8) 
		instr = disasm.decodeInstruction(pltIdx);
		assert instr instanceof X86JmpInstruction;
		pltIdx += instr.getSize();

		while (true) {
			if (data[pltIdx] == 0) {
				pltIdx++;
			} else {
				instr = disasm.decodeInstruction(pltIdx);
				pltIdx += instr.getSize();
				if (!instr.getName().equals("nop")) break;
			}
		}
		// now we should be at the first PLT jump
		while (true) {
			AbsoluteAddress jmpLocation = getVirtualAddress(pltIdx);
			X86JmpInstruction jmpToFunction = (X86JmpInstruction)instr;

			// Where the function pointer is to be stored
			AbsoluteAddress pltSlot = new AbsoluteAddress((((X86MemoryOperand)jmpToFunction.getBranchDestination())).getDisplacement());
			//logger.debug("Address of memory trampoline is " + pltSlot + 
			//		", file offset 0x" + Long.toHexString(getFilePointer(pltSlot)));
			// Before loading, there's a trampoline pointer back to the following push instruction stored in this slot
			inBuf.seek(getFilePointer(pltSlot));
			AbsoluteAddress trampolineDest = new AbsoluteAddress(inBuf.readDWORD());
			//logger.debug("Trampoline destination is " + trampolineDest);
			pltIdx = (int)getFilePointer(trampolineDest);
			// Read the push instruction
			instr = disasm.decodeInstruction(pltIdx);
			X86Instruction pushSTOff = (X86Instruction)instr;
			// The push instruction's parameter is an index into the symbol table
			int symbolTableOff = ((Immediate)pushSTOff.getOperand1()).getNumber().intValue();
			// Read function name from symbol table
			//String functionName = elf.getSymbols()[symbolTableOff].toString();
			
			// r_offset is at 0, r_info at 4. r_info is an integer containing the symbol index
			int ri = symbolTableOff + 4;
			// little endian only
			int r_info = ((pltRelocs[ri + 3] << 24) + (pltRelocs[ri + 2] << 16) + (pltRelocs[ri + 1] << 8) + pltRelocs[ri]);
			int type = (byte)r_info;
			int symIdx = r_info >> 8;
			// type must be R_386_JMP_SLOT
			assert (type == 7);

			//String functionName = elf.getDynamicSymbols()[(symbolTableOff / 8)].toString();
			String functionName = elf.getDynamicSymbols()[symIdx].toString();

			
			UnresolvedSymbol importSymbol = new UnresolvedSymbol(this, "ELF", functionName, (int)getFilePointer(pltSlot), AddressingType.ABSOLUTE);
			imports.add(importSymbol);
			symbolMap.put(jmpLocation, functionName);
			symbolMap.put(pltSlot, "__imp_" + functionName);
			// Now skip the following jump to PLT0 (a call to the dynamic loader)
			pltIdx += instr.getSize();
			instr = disasm.decodeInstruction(pltIdx);
			assert instr instanceof X86JmpInstruction : "Expected jmp to PLT[0] in PLT at this offset!";
			pltIdx += instr.getSize();
			// And now pltIdx points to the next PLT entry

			// Check if there are more plt entries.
			if (data[pltIdx] == 0) {
				break;
			}
			instr = disasm.decodeInstruction(pltIdx);
			if (!(instr instanceof X86JmpInstruction)) {
				break;
			}
		}
		
	}
	
	public boolean isInPlt(AbsoluteAddress a) {
		return (a.getValue() >= pltStart && a.getValue() < pltStart + pltSize);
	}
	
	public Set<String> getRequiredLibraries() {
		return requiredLibraries;
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getDisassembler()
	 */
	@Override
	public Disassembler getDisassembler() {
		if (disassembler == null) {
			disassembler = new X86Disassembler(inBuf);
		}
		return disassembler;
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getEntryPoint()
	 */
	@Override
	public AbsoluteAddress getEntryPoint() {
		try {
			return new AbsoluteAddress(elf.getELFhdr().e_entry.getValue().longValue());
		} catch (IOException e) {
			e.printStackTrace();
			throw new RuntimeException("Cannot read entry point from elf");
		}
	}
	
	@Override
	public AbsoluteAddress getMaxAddress() {
		long highAddress = Long.MIN_VALUE;
		for (Elf.Section section : elf.sections) {
			highAddress = Math.max(section.sh_addr.getValue().longValue() + 
					section.sh_size, highAddress);
		}
		//highAddress += getBaseAddress();
		return new AbsoluteAddress(highAddress);
	}

	@Override
	public AbsoluteAddress getMinAddress() {
		long lowAddress = Long.MAX_VALUE;
		for (Elf.Section section : elf.sections) {
			lowAddress = Math.min(section.sh_addr.getValue().longValue(), 
					lowAddress);
		}
		//highAddress += getBaseAddress();
		return new AbsoluteAddress(lowAddress);
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getExportedSymbols()
	 */
	@Override
	public Set<ExportedSymbol> getExportedSymbols() {
		return functionSymbols;
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getFilePointer(org.jakstab.asm.AbsoluteAddress)
	 */
	@Override
	public long getFilePointer(AbsoluteAddress va) {
		long a = va.getValue();
		for (Elf.Section section : elf.sections) {
			if (a >= section.sh_addr.getValue().longValue() && 
					a <= section.sh_addr.getValue().longValue() + section.sh_size) {

				if (section.sh_type == Elf.Section.SHT_NOBITS) { 
					// || (section.toString().equals(".bss"))) {
					//logger.info("Getting file pointer for uninitialized section?");
					return -1;
				}
				return a - section.sh_addr.getValue().longValue() + section.sh_offset;
			}
		}
		return -1;
		//throw new RuntimeException("Virtual address " + va + " matches no section?"); 
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getSymbolFinder()
	 */
	@Override
	public SymbolFinder getSymbolFinder() {
		return new ELFSymbolFinder(this);
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getUnresolvedSymbols()
	 */
	@Override
	public Set<UnresolvedSymbol> getUnresolvedSymbols() {
		return imports;
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#getVirtualAddress(long)
	 */
	@Override
	public AbsoluteAddress getVirtualAddress(long fp) {
		for (Elf.Section section : elf.sections) {
			if (fp >= section.sh_offset && fp <= section.sh_offset + section.sh_size) {
				return new AbsoluteAddress(fp - section.sh_offset + 
						section.sh_addr.getValue().longValue());
			}
		}
		throw new RuntimeException("Filepointer " + fp + " matches no section?"); 
	}

	/*
	 * @see org.jakstab.loader.ExecutableImage#isCodeArea(org.jakstab.asm.AbsoluteAddress)
	 */
	@Override
	public boolean isCodeArea(AbsoluteAddress va) {
		long a = va.getValue();
		for (Elf.Section section : elf.sections) {
			if (a >= section.sh_addr.getValue().longValue() && 
					a <= section.sh_addr.getValue().longValue() + section.sh_size) {
				return (section.sh_type == Elf.Section.SHT_PROGBITS); 
			}
		}
		// Section not found
		return false;
	}
	
	public Map<AbsoluteAddress, String> getSymbolMap() {
		return symbolMap;
	}

	@Override
	public boolean isReadOnly(AbsoluteAddress a) {
		// TODO: Implement
		return false;
	}

	@Override
	public RTLNumber readMemoryLocation(RTLMemoryLocation m) throws IOException {
		
		if (!(m.getAddress() instanceof RTLNumber)) return null;
		
		AbsoluteAddress va = new AbsoluteAddress((RTLNumber)m.getAddress());

		long fp = getFilePointer(va);
		if (fp > 0) {
			assert m.getBitWidth() % 8 == 0 : "Non-byte-aligned memory reference!";
			long val = 0;
			int bytes = m.getBitWidth()/8;
			
			inBuf.seek(fp);
			// OR together the least significant bytes 
			for (int i=0; i<bytes - 1; i++) {
				val = val | ((long)inBuf.readBYTE()) << (i*8);
			}
			// do not mask the MSB with 0xFF, so we get sign extension for free
			val = val | (((long)inBuf.readINT8()) << (bytes - 1) * 8);
			//logger.debug("Read constant value " + val + " from address " + m + " (file offset: " + Long.toHexString(fp) + ") in image.");
			return ExpressionFactory.createNumber(val, m.getBitWidth());

		} 

		logger.debug("No value can be read from image for address " + m);
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
