/*
 * BinaryFileInputBuffer.java - This file is part of the Jakstab project.
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
package org.jakstab.util;


/**
 * @author Johannes Kinder
 */
public class BinaryFileInputBuffer extends BinaryInputBuffer {

	private byte[] data;
	private int size;

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BinaryFileInputBuffer.class);

	/** 
	 * Creates a BinaryInputBuffer from the given InputStream and buffers all the available data.
	 * Note: if input is a network stream, this constructor will only buffer the 
	 * data that is available at the time the constructor is called (i.e. as much as is reported by 
	 * InputStream.available()).
	 */
	public BinaryFileInputBuffer(java.io.InputStream input) throws java.io.IOException {
		// reads in an entire input stream and buffers it
		current = 0;
		data = new byte[input.available()];
		size = input.read(data);
		input.close();
	}

	@Override
	public int readBYTE() throws java.io.IOException {
		// throws java.io.IOException if EOF
		return (data[current++]&0xFF)&0xFF;
	}
	
	@Override
	public byte getByteAt(int fp) {
		return data[fp];
	}

	@Override
	public long getSize() {
		return size;
	}

	public byte[] getByteArray() {
		return data;
	}

}
