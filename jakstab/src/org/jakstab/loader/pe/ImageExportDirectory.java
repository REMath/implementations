/*
 * ImageExportDirectory.java - This file is part of the Jakstab project.
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

import org.jakstab.util.BinaryInputBuffer;

/**
 * @author Johannes Kinder
 */
class ImageExportDirectory {
	public long Characteristics; 	// Not used.
	public long TimeDateStamp; 		// Number of seconds since 1/1/1970 GMT.
	int MajorVersion; 				// Not used.
	int MinorVersion; 				// Not used.
	long Name; 						// RVA of DLL name string
	long Base; 						// Starting ordinal of exports, usually 1
									// RVA(ord) = EAT[ord - Base];
	long NumberOfFunctions; // The number of entries in the EAT. Some entries may be 0.
	long NumberOfNames; 	// The number of entries in the Export Names Table (ENT). This 
		// value will always be less than or equal to the NumberOf-Functions field. 
		// It will be less when there are symbols exported by ordinal only. It can also 
		// be less if there are numeric gaps in the assigned ordinals. This field is 
		// also the size of the export ordinal table (below).
	long AddressOfFunctions;	// RVA of EAT. 
	long AddressOfNames; 		// RVA of ENT. 
	long AddressOfNameOrdinals; // RVA of export ordinal table. 

	public ImageExportDirectory(BinaryInputBuffer in) throws java.io.IOException {
		Characteristics = in.readDWORD();
		TimeDateStamp = in.readDWORD();
		MajorVersion = in.readWORD();
		MinorVersion = in.readWORD();
		Name = in.readDWORD();
		Base = in.readDWORD();
		NumberOfFunctions = in.readDWORD();
		NumberOfNames = in.readDWORD();
		AddressOfFunctions = in.readDWORD();
		AddressOfNames = in.readDWORD();
		AddressOfNameOrdinals = in.readDWORD();
	}
	
	public void output() {
		System.out.println("Characteristics: 0x" + Long.toHexString(Characteristics));
		System.out.println("TimeDateStamp: 0x" + Long.toHexString(TimeDateStamp));
		System.out.println("MajorVersion: 0x" + Long.toHexString(MajorVersion));
		System.out.println("MinorVersion: 0x" + Long.toHexString(MinorVersion));
		System.out.println("Name: 0x" + Long.toHexString(Name));
		System.out.println("Base: 0x" + Long.toHexString(Base));
		System.out.println("NumberOfFunctions: 0x" + Long.toHexString(NumberOfFunctions));
		System.out.println("NumberOfNames: 0x" + Long.toHexString(NumberOfNames));
		System.out.println("AddressOfFunctions: 0x" + Long.toHexString(AddressOfFunctions));
		System.out.println("AddressOfNames: 0x" + Long.toHexString(AddressOfNames));
		System.out.println("AddressOfNameOrdinals: 0x" + Long.toHexString(AddressOfNameOrdinals));
	}
}
