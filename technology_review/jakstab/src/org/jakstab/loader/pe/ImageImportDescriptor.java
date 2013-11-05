/*
 * ImageImportDescriptor.java - This file is part of the Jakstab project.
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
public class ImageImportDescriptor {
	public long OriginalFirstThunk;
	public long TimeDateStamp;
	public long ForwarderChain;
	public long Name;
	public long FirstThunk;


	/**
	 * Parses an ImageImportDescriptor from an input stream.
	 * @param in
	 * @throws java.io.IOException
	 */
	public ImageImportDescriptor(BinaryInputBuffer in) throws java.io.IOException{
		OriginalFirstThunk = in.readDWORD(); // RVA of the Import Name Table (INT)
		TimeDateStamp = in.readDWORD();
		ForwarderChain = in.readDWORD();
		Name = in.readDWORD();
		FirstThunk = in.readDWORD(); // RVA of the Import Address Table (IAT).
	}

	/** 
	 * Indicates whether this is the final structure in the array of descriptors.
	 * @return true if the OriginalFirstThunk field is zero, false otherwise.
	 */
	public boolean isZero() {
		return OriginalFirstThunk == 0;
	}

	public void output() {
		System.out.println("OriginalFirstThunk: 0x" + Long.toHexString(OriginalFirstThunk));
		System.out.println("TimeDateStamp: 0x" + Long.toHexString(TimeDateStamp));
		System.out.println("ForwarderChain: 0x" + Long.toHexString(ForwarderChain));
		System.out.println("Name: 0x" + Long.toHexString(Name));
		System.out.println("FirstThunk: 0x" + Long.toHexString(FirstThunk));
	}

}
