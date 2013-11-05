/*
 * MSDOS_Stub.java - This file is part of the Jakstab project.
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

/** 
 * Ths MS-DOS stub starts a PE/COFF file. The only relevant field in this structure
 * is the NewFileHeaderAddress, which will be at offset 0x3C romt he start of the file.
 * The value here will be the file offset to the PE signature, which is followed by the PE header.
 * 
 * Changed to throw a BinaryParseException for MSDOS-executables
 * 
 * @author Michael Stepp
 * @author Johannes Kinder
 */
class MSDOS_Stub {
	private static final int MAGIC = 0x5A4D;  // == 'MZ'

	private int Magic;                  // 2 bytes
	private byte[] data1;               // 58 bytes
	private long NewFileHeaderAddress;  // 4 bytes
	private byte[] data2;               // (NewFileHeaderAddress-64) bytes

	/**
	 *  Parses an MSDOS_Stub from an input stream
	 */
	public MSDOS_Stub(BinaryInputBuffer in) throws java.io.IOException, BinaryParseException {
		Magic = in.readWORD();
		if (Magic != MAGIC)
			throw new BinaryParseException("MSDOS_Stub: File does not start with magic number 0x4D5A");

		data1 = new byte[58];
		in.read(data1);
		NewFileHeaderAddress = in.readDWORD();
		try {
			data2 = new byte[(int)(NewFileHeaderAddress - 64)];
			in.read(data2);
		} catch (Exception e) {
			throw new BinaryParseException("No PE header found. MS-DOS executables are not supported.");
		}
	}

	/** 
	 * @return Returns the file offset of the PE signature
	 */
	public long getHeaderAddress(){
		return NewFileHeaderAddress;
	}

	public void output(){
		System.out.print("MSDOS_Stub:{");
		System.out.print("\n  Magic = 0x" + Integer.toHexString(Magic));
		System.out.print("\n  <data1>");
		System.out.print("\n  NewFileHeaderAddress = 0x" + Long.toHexString(NewFileHeaderAddress));
		System.out.print("\n  <data2>");
		System.out.print("\n}\n");
	}
}
