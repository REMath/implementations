/*
 * BinaryInputBuffer.java - This file is part of the Jakstab project.
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

package org.jakstab.util;

/** 
 * This is an input stream that buffers an entire binary file in advance. 
 * All multi-byte integers are read little-endian.
 * 
 * @author Michael Stepp
 * @author Johannes Kinder
 */
public abstract class BinaryInputBuffer {

	protected int current;

	/** 
	 * Moves the file pointer to the given location.
	 */
	public void seek(long pos) throws java.io.IOException {
		// skips to absolute location 'point' in the file
		if (pos<0 || pos>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.seek: Seek position outside of file bounds: "+pos);

		current = (int)pos;
	}

	/** 
	 * Reads a null-terminated ASCII string from the file starting 
	 * at the current location and ending at the next 0x00 ('\0') byte.
	 */
	public String readASCII() throws java.io.IOException {
		String result = "";
		int BYTE;
		while((BYTE=readBYTE()) != 0)
			result += (char)BYTE;
		return result;
	}

	/** 
	 * Returns the current file position of this input stream
	 */
	public long getCurrent() {
		return current;
	}

	/** 
	 * Asserts that the next bytes to be read from the input stream equal the 
	 * byte array given. If sucessful, returns true and advances the file pointer by
	 * bytes.length. If unsuccessful, will either throw an exception (if premature EOF)
	 * or will returns false. The file position after an unsuccessful match is undefined, 
	 * but will be somewhere between start and (start+bytes.length).
	 */
	public boolean match(byte[] bytes) throws java.io.IOException {
		if ((current + bytes.length) > getSize())
			return false;
		for (int i=0;i<bytes.length;i++){
			//if (bytes[i] != data[current++])
			if (bytes[i] != (byte)readBYTE())
				return false;
		}
		return true;
	}

	/** 
	 * Advances the file pointer by 'amount'.
	 * @param amount the amount to skip, may be negative.
	 * @return true iff the skip was successful
	 */
	public boolean skip(int amount) {
		if ((current + amount) > getSize() || (current + amount) < 0)
			return false;
		current += amount;
		return true;
	}

	/** 
	 * Moves the file pointer to the next higher multiple of 'a'.
	 * @param a the value to align to, must be positive
	 * @return true iff the align was successful
	 */
	public boolean align(int a) {
		// skips to the next multiple of 'a' bytes
		if (a<=0)
			return false;
		if (a==1)
			return true;
		int temp = current + (a-(current%a))%a;
		if (temp>getSize())
			return false;
		current = temp;
		return true;
	}

	/** 
	 * Reads from the current file pointer into the given array.
	 * @param bytes the array to read into. this will attempt to read bytes.length bytes from the file
	 */
	public void read(byte[] bytes) throws java.io.IOException {
		if (bytes==null)
			return;
		if ((current+bytes.length) > getSize())
			throw new java.io.IOException("BinaryInputBuffer.read: Premature EOF");

		for (int i=0; i<bytes.length; i++)
			//bytes[i] = data[current++];
			bytes[i] = (byte)readBYTE();
	}

	/** 
	 * Reads an unsigned byte from the file, returned in the lower 8 bits of an int.
	 * Advances the file pointer by 1.
	 */
	public abstract int readBYTE() throws java.io.IOException;
	
	/**
	 * Reads a single signed byte from the file without changing the file pointer.
	 * 
	 * @param fp Address to read from
	 * @return a signed byte value
	 */
	public abstract byte getByteAt(int fp);

		/**
	 *  Reads an unsigned 2-byte integer from the file, returned in the lower 2 bytes of an int
	 * Advances the file pointer by 2.
	 */
	public int readWORD() throws java.io.IOException {
		if (current+1>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readWORD: Premature EOF");

		int b1 = readBYTE();
		int b2 = readBYTE();
		int result = ((b1 & 0xFF) | ((b2 & 0xFF) << 8));
		return result;
	}

	/**
	 *  Reads an unsigned 4-byte integer from the file and returns it the lower 4 bytes of a long.
	 * Advances the file pointer by 4.
	 */
	public long readDWORD() throws java.io.IOException {
		if (current+3>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readDWORD: Premature EOF");
		int b1 = readBYTE();
		int b2 = readBYTE();
		int b3 = readBYTE();
		int b4 = readBYTE();

		long result = ((b1 & 0xFFL) | ((b2 & 0xFFL) << 8) 
				| ((b3 & 0xFFL) << 16) | ((b4 & 0xFFL) << 24));
		return result;
	}

	/** 
	 * Reads an 8-byte (signed) quantity and returns it in a long.
	 * Advances the file pointer by 8.
	 */
	public long readDDWORD() throws java.io.IOException {
		// throws java.io.IOException if EOF
		if (current+7>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readDWORD: Premature EOF");
		int b1 = readBYTE();
		int b2 = readBYTE();
		int b3 = readBYTE();
		int b4 = readBYTE();
		int b5 = readBYTE();
		int b6 = readBYTE();
		int b7 = readBYTE();
		int b8 = readBYTE();

		long result = ((b1 & 0xFFl) | ((b2 & 0xFFl) << 8) 
				| ((b3 & 0xFFl) << 16) | ((b4 & 0xFFl) << 24) 
				| ((b5 & 0xFFl) << 32) | ((b6 & 0xFFl) << 40) 
				| ((b7 & 0xFFl) << 48) | ((b8 & 0xFFl) << 56));
		return result;
	}

	/** 
	 * Reads an int64 (signed) from the file and returns it in a long.
	 * Advances the file pointer by 8.
	 */
	public long readINT64() throws java.io.IOException {
		return readDDWORD();
	}

	/** 
	 * Reads an int32 (signed) from the file and returns it in an int.
	 * Advances the file pointer by 4.
	 */
	public int readINT32() throws java.io.IOException {
		if (current+3>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readINT32: Premature EOF");

		int b1 = readBYTE();
		int b2 = readBYTE();
		int b3 = readBYTE();
		int b4 = readBYTE();

		int temp =  (b1 & 0xFF) | ((b2 & 0xFF)<<8) | 
		((b3 & 0xFF)<<16) | ((b4 & 0xFF)<<24);
		return temp;
	}

	/** 
	 * Reads an int16 (signed) from the file and returns it in an int.
	 * Advances the file pointer by 2.
	 */
	public int readINT16() throws java.io.IOException {
		short shorty=0;
		if (current+1>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readINT16: Premature EOF");
		int b1 = readBYTE();
		int b2 = readBYTE();

		shorty = (short)(((b1 & 0xFF) | (b2 & 0xFF)<<8) & 0xFFFF);
		return shorty;
	}

	/**
	 * Reads an int8 (signed) from the file and returns it in an int.
	 * Advances the file pointer by 1.
	 */
	public int readINT8() throws java.io.IOException {
		if (current>=getSize())
			throw new java.io.IOException("BinaryInputBuffer.readINT8: Premature EOF");
		return ((byte)readBYTE());
	}

	/**
	 * Reads an r4 from the file and returns it in a float.
	 * Advances the file pointer by 4.
	 */
	public float readR4() throws java.io.IOException {
		return Float.intBitsToFloat((int)readDWORD());
	}

	/** 
	 * Reads an r8 from the file and returns it in a double.
	 * Advances the file pointer by 8.
	 */
	public double readR8() throws java.io.IOException {
		return Double.longBitsToDouble(readDDWORD());
	}

	public abstract long getSize();

}
