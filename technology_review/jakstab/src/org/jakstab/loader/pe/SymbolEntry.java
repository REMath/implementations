/*
 * SymbolEntry.java - This file is part of the Jakstab project.
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
import java.util.Map;

import org.jakstab.util.BinaryInputBuffer;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
@SuppressWarnings("unused") 
class SymbolEntry {

	private static final Logger logger = Logger.getLogger(SymbolEntry.class);
	
	// Storage classes used by MS compilers
	private static final int IMAGE_SYM_CLASS_EXTERNAL = 2;
	private static final int IMAGE_SYM_CLASS_STATIC = 3;
	private static final int IMAGE_SYM_CLASS_LABEL = 6;
	private static final int IMAGE_SYM_CLASS_FUNCTION = 101;
	private static final int IMAGE_SYM_CLASS_FILE = 103;
 
	private final String Name;
	private final long Value;
	private final int SectionNumber;
	private final int Type;
	private final int StorageClass;
	private final int NumberOfAuxSymbols;

	public SymbolEntry(BinaryInputBuffer inBuf, Map<Integer, String> stringTable) throws IOException {
		// Parse name
		byte[] nameArray = new byte[8];
		inBuf.read(nameArray);
		// If first 4 bytes are 0, the next 4 are an offset into the string table
		if ((nameArray[0] == 0) && (nameArray[1] == 0) && (nameArray[2] == 0) && (nameArray[3] == 0)) {
			int stringOffset = ((nameArray[7] & 0xFF) << 24) 
							 | ((nameArray[6] & 0xFF) << 16) 
							 | ((nameArray[5] & 0xFF) <<  8) 
							 |  (nameArray[4] & 0xFF);
			String nameString = stringTable.get(stringOffset);
			if (nameString != null) {
				Name = nameString;
			} else {
				logger.warn("No name in string table for symbol at specified offset " + stringOffset);
				Name = "Anonymous(" + stringOffset + ")";
			}
		} else {
			StringBuilder nBuilder = new StringBuilder();
			for (int i=0;i<8;i++){
				if ((nameArray[i]&0xFF)>32 && (nameArray[i]&0xFF)<128)
					nBuilder.append((char)(nameArray[i]&0xFF));
			}
			Name = nBuilder.toString();
		}

		Value = inBuf.readDWORD();
		int section = inBuf.readWORD();
		if (section >= 32768) 
			SectionNumber = section - 65536;
		else 
			SectionNumber = section;
		Type = inBuf.readWORD();
		StorageClass = inBuf.readBYTE();
		NumberOfAuxSymbols = inBuf.readBYTE();

	}
	
	public String getName() {
		return Name;
	}

	public long getValue() {
		return Value;
	}

	public int getNumberOfAuxSymbols() {
		return NumberOfAuxSymbols;
	}
	
	public int getStorageClass() {
		return StorageClass;
	}

	/**
	 * Does the symbol refer to a global variable or external function?
	 * 
	 * @return true if the symbol is a global variable or external 
	 * function, false otherwise. 
	 */
	public boolean isExternal() {
		return StorageClass == IMAGE_SYM_CLASS_EXTERNAL;
	}
	
	/**
	 * Does the symbol refer to a static value, i.e. a string literal or 
	 * a jump table?
	 * @return true, if the value field refers to the offset of the value relative 
	 * to it's section start, false if it is something else.
	 */
	public boolean isStatic() {
		return StorageClass == IMAGE_SYM_CLASS_STATIC;
	}
	
	/**
	 * Does the symbol refer to a jump label? If true, the value field contains
	 * the offset of the jump target relative to the section.
	 * @return true if the symbol points to a jump label, false otherwise.
	 */
	public boolean isLabel() {
		return StorageClass == IMAGE_SYM_CLASS_LABEL;
	}
	
	public int getSectionNumber() {
		return SectionNumber;
	}

	@Override
	public String toString() {
		return "Name: " + Name + " Storage class: " + StorageClass + " Section number: " + SectionNumber + " Value: " + Long.toHexString(Value);
	}
	
	

}
