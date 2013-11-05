/*
 * COFF_Header.java - This file is part of the Jakstab project.
 * 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright (C) 2003 The University of Arizona
 *
 * The original code for this class was taken from "MBEL: The Microsoft 
 * Bytecode Engineering Library" and modified for use with Jakstab.
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

import org.jakstab.loader.BinaryParseException;
import org.jakstab.util.BinaryInputBuffer;
import org.jakstab.util.Logger;

/** 
 * This class holds the data from the COFF Header in a PE/COFF file.
 * The COFF header comes right after the PE signature, and right before the PE header.
 * 
 * @author Michael Stepp
 * @author Johannes Kinder
 */
@SuppressWarnings("unused")
class COFF_Header {
	private final static Logger logger = Logger.getLogger(COFF_Header.class);

	// Constants for 'Machine' field /////////////////////////
	private static final int IMAGE_FILE_MACHINE_UNKNOWN = 0x0;     // The contents of this field are assumed to be applicable to any machine type
	private static final int IMAGE_FILE_MACHINE_AM33 = 0x1d3;      // Matsushita AM33
	private static final int IMAGE_FILE_MACHINE_AMD64 = 0x8664;    // x64
	private static final int IMAGE_FILE_MACHINE_ARM = 0x1c0;       // ARM little endian
	private static final int IMAGE_FILE_MACHINE_EBC = 0xebc;       // EFI byte code
	private static final int IMAGE_FILE_MACHINE_I386 = 0x14c;      // Intel 386 or later processors and compatible processors
	private static final int IMAGE_FILE_MACHINE_IA64 = 0x200;      // Intel Itanium processor family
	private static final int IMAGE_FILE_MACHINE_M32R = 0x9041;     // Mitsubishi M32R little endian
	private static final int IMAGE_FILE_MACHINE_MIPS16 = 0x266;    // MIPS16
	private static final int IMAGE_FILE_MACHINE_MIPSFPU = 0x366;   // MIPS with FPU
	private static final int IMAGE_FILE_MACHINE_MIPSFPU16 = 0x466; // MIPS16 with FPU
	private static final int IMAGE_FILE_MACHINE_POWERPC = 0x1f0;   // Power PC little endian
	private static final int IMAGE_FILE_MACHINE_POWERPCFP = 0x1f1; // Power PC with floating point support
	private static final int IMAGE_FILE_MACHINE_R4000 = 0x166;     // MIPS little endian
	private static final int IMAGE_FILE_MACHINE_SH3 = 0x1a2;       // Hitachi SH3
	private static final int IMAGE_FILE_MACHINE_SH3DSP = 0x1a3;    // Hitachi SH3 DSP
	private static final int IMAGE_FILE_MACHINE_SH4 = 0x1a6;       // Hitachi SH4
	private static final int IMAGE_FILE_MACHINE_SH5 = 0x1a8;       // Hitachi SH5
	private static final int IMAGE_FILE_MACHINE_THUMB = 0x1c2;     // Thumb
	private static final int IMAGE_FILE_MACHINE_WCEMIPSV2 = 0x169; // MIPS little endian WCE v2

	// Constants for 'Characteristics' field ///////////////////
	private static final int IMAGE_FILE_RELOCS_STRIPPED          = 0x0001;
	private static final int IMAGE_FILE_EXECUTABLE_IMAGE         = 0x0002;
	private static final int IMAGE_FILE_LINE_NUMS_STRIPPED       = 0x0004;
	private static final int IMAGE_FILE_LOCAL_SYMS_STRIPPED      = 0x0008;
	private static final int IMAGE_FILE_AGGRESIVE_WS_TRIM        = 0x0010;
	private static final int IMAGE_FILE_LARGE_ADDRESS_AWARE      = 0x0020;
	private static final int IMAGE_FILE_BYTES_REVERSED_LO        = 0x0080;
	private static final int IMAGE_FILE_32BIT_MACHINE            = 0x0100;
	private static final int IMAGE_FILE_DEBUG_STRIPPED           = 0x0200;
	private static final int IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP  = 0x0400;
	private static final int IMAGE_FILE_NET_RUN_FROM_SWAP        = 0x0800;
	private static final int IMAGE_FILE_SYSTEM                   = 0x1000;
	private static final int IMAGE_FILE_DLL                      = 0x2000;
	private static final int IMAGE_FILE_UP_SYSTEM_ONLY           = 0x4000;
	private static final int IMAGE_FILE_BYTES_REVERSED_HI        = 0x8000;

	private final int Machine;                 // 2bytes
	private final int NumberOfSections;        // 2bytes
	private final long TimeDateStamp;          // 4bytes
	private final long PointerToSymbolTable;   // 4bytes (==0) (file pointer)
	private final int NumberOfSymbols;        // 4bytes (==0)
	private final int SizeOfOptionalHeader;    // 2bytes
	private final int Characteristics;         // 2bytes

	/** Parses a COFF_Header from an input stream
	 */
	public COFF_Header(BinaryInputBuffer in) throws java.io.IOException, BinaryParseException{
		Machine              = in.readWORD();
		NumberOfSections     = in.readWORD();
		TimeDateStamp        = in.readDWORD();
		PointerToSymbolTable = in.readDWORD();
		NumberOfSymbols      = (int)in.readDWORD();
		SizeOfOptionalHeader = in.readWORD();
		Characteristics      = in.readWORD();

		if (!isX86()) throw new BinaryParseException("Non-x86 COFF files currently not supported!");

		//		logger.debug("COFF Header: {");
		//		logger.debug("  Machine = " + "0x" + Integer.toHexString(Machine));
		//		logger.debug("  NumberOfSections = " + getNumberOfSections());
		//		logger.debug("  TimeDateStamp = " + "0x" + Long.toHexString(TimeDateStamp));
		//		logger.debug("  PointerToSymbolTable = " + "0x" + Long.toHexString(PointerToSymbolTable));
		//		logger.debug("  NumberOfSymbols = " + NumberOfSymbols);
		//		logger.debug("  SizeOfOptionalHeader = " + SizeOfOptionalHeader);
		//		logger.debug("  Characteristics = " + Integer.toBinaryString(Characteristics));
		//		logger.debug("}");
	}

	/**
	 * @return the numberOfSections
	 */
	public int getNumberOfSections() {
		return NumberOfSections;
	}

	/** 
	 * Returns true iff this is a DLL file (according to the flags)
	 */
	public boolean isDLLFile(){
		return ((Characteristics & COFF_Header.IMAGE_FILE_DLL) != 0);
	}

	public boolean isX86() {
		return Machine == IMAGE_FILE_MACHINE_I386;
	}

	public long getPointerToSymbolTable() {
		return PointerToSymbolTable;
	}

	public int getNumberOfSymbols() {
		return NumberOfSymbols;
	}

}


