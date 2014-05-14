/*
 * SectionHeader.java - This file is part of the Jakstab project.
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

import org.jakstab.util.BinaryInputBuffer;
import org.jakstab.util.Logger;

/** 
 * This is the structure used to parse a PE/COFF Section Header.
 * Sections must appear in ascending order of virtual address,
 * and must be consecutive in the virtual address space.
 * Their virtual addresses must be multiples of SectionAlignment
 * in the PE header.

 * Also, the PointerToRawData and SizeOfRawData fields must be multiples of 
 * FileAlignment in the PE header.
 * If (SectionAlignment < PageSize) then
 *    PointerToRawData == VirtualAddress
 * @author Michael Stepp
 */
class SectionHeader {
	private final static Logger logger = Logger.getLogger(SectionHeader.class);
	public static final int STRUCT_SIZE = 40;

	///// Flags for 'Characteristics' field //////////////////////////////
	public static final int IMAGE_SCN_SCALE_INDEX            = 0x00000001;
	public static final int IMAGE_SCN_CNT_CODE               = 0x00000020;
	public static final int IMAGE_SCN_CNT_INITIALIZED_DATA   = 0x00000040;
	public static final int IMAGE_SCN_CNT_UNINITIALIZED_DATA = 0x00000080;
	public static final int IMAGE_SCN_LNK_INFO               = 0x00000200;
	public static final int IMAGE_SCN_LNK_REMOVE             = 0x00000800;
	public static final int IMAGE_SCN_LNK_COMDAT             = 0x00001000;
	public static final int IMAGE_SCN_GPREL                  = 0x00008000;
	public static final int IMAGE_SCN_NO_DEFER_SPEC_EXC      = 0x00004000;
	public static final int IMAGE_SCN_LNK_NRELOC_OVFL        = 0x01000000;
	public static final int IMAGE_SCN_MEM_DISCARDABLE        = 0x02000000;
	public static final int IMAGE_SCN_MEM_NOT_CACHED         = 0x04000000;
	public static final int IMAGE_SCN_MEM_NOT_PAGED          = 0x08000000;
	public static final int IMAGE_SCN_MEM_SHARED             = 0x10000000;
	public static final int IMAGE_SCN_MEM_EXECUTE            = 0x20000000;
	public static final int IMAGE_SCN_MEM_READ               = 0x40000000;
	public static final int IMAGE_SCN_MEM_WRITE              = 0x80000000;
	//////////////////////////////////////////////////////////////////////

	private final byte NameArray[];                 // 8bytes
	private final String name;
	// Virtual size and address are not final to allow relocation of sections in objs
	public long VirtualSize;            // 4bytes
	public long VirtualAddress;         // 4bytes (really an RVA)
	public final long SizeOfRawData;          // 4bytes
	public final long PointerToRawData;       // 4bytes
	public final long PointerToRelocations;   // 4bytes (file pointer) (object only)
	public final long PointerToLinenumbers;   // 4bytes (file pointer)
	public final int NumberOfRelocations;     // 2bytes
	public final int NumberOfLinenumbers;     // 2bytes
	public final long Characteristics;        // 4bytes
	public final long startFP;

	/** 
	 * Parses a Section Header from an input stream
	 */
	public SectionHeader(BinaryInputBuffer in) throws java.io.IOException{
		startFP = in.getCurrent();

		NameArray = new byte[8];
		in.read(NameArray);
		
		StringBuilder nBuilder = new StringBuilder();
		for (int i=0;i<8;i++){
			if ((NameArray[i]&0xFF)>32 && (NameArray[i]&0xFF)<128)
				nBuilder.append((char)(NameArray[i]&0xFF));
		}
		name = nBuilder.toString();

		VirtualSize                   = in.readDWORD();
		VirtualAddress                = in.readDWORD();
		SizeOfRawData                 = in.readDWORD();
		PointerToRawData              = in.readDWORD();
		PointerToRelocations          = in.readDWORD();
		PointerToLinenumbers          = in.readDWORD();
		NumberOfRelocations           = in.readWORD();
		NumberOfLinenumbers           = in.readWORD();
		Characteristics               = in.readDWORD();
		//output();
	}

	public boolean isCodeSection() {
		return (Characteristics & (IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_CNT_CODE)) > 0;
	}
	
	public boolean isReadOnlySection() {
		return (Characteristics & IMAGE_SCN_MEM_READ) > 0 && (Characteristics & IMAGE_SCN_MEM_WRITE) == 0; 
	}
	
	public boolean hasComdat() {
		return (Characteristics & IMAGE_SCN_LNK_COMDAT) > 0;
	}
	
	public boolean isRemovedByLinker() {
		return (Characteristics & IMAGE_SCN_LNK_REMOVE) > 0;
	}
	
	public boolean isDiscardable() {
		return (Characteristics & IMAGE_SCN_MEM_DISCARDABLE) > 0;
	}
	
	public String getName() {
		return name;
	}

	public void output(){
		logger.debug("SectionHeader: {");
		logger.debug("  Name = '" + getName() + "'");
		logger.debug("  VirtualSize = " + "0x" + Long.toHexString(VirtualSize));
		logger.debug("  VirtualAddress = 0x" + Long.toHexString(VirtualAddress));
		logger.debug("  SizeOfRawData = 0x" + Long.toHexString(SizeOfRawData));
		logger.debug("  PointerToRawData = " + "0x" + Long.toHexString(PointerToRawData));
		logger.debug("  PointerToRelocations = " + "0x" + Long.toHexString(PointerToRelocations));
		logger.debug("  PointerToLinenumbers = " + "0x" + Long.toHexString(PointerToLinenumbers));
		logger.debug("  NumberOfRelocations = " + NumberOfRelocations);
		logger.debug("  NumberOfLinenumbers = " + NumberOfLinenumbers);
		logger.debug("  Characteristics = 0x" + Long.toHexString(Characteristics));
		logger.debug("}");
	}
}
