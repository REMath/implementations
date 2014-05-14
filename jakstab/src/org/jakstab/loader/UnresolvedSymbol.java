/*
 * UnresolvedSymbol.java - This file is part of the Jakstab project.
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
package org.jakstab.loader;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.util.Logger;

public class UnresolvedSymbol {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(UnresolvedSymbol.class);
	
	private final ExecutableImage module;
	private final String fromLibrary;
	private final String name;
	private final int fp;
	public enum AddressingType { ABSOLUTE, PC_RELATIVE }
	private final AddressingType addressingType;
	
	
	public UnresolvedSymbol(ExecutableImage module, String fromLibrary, 
			String name, int filepointer, AddressingType addressingType) {
		this.fromLibrary = fromLibrary;
		this.module = module;
		this.name = name;
		this.fp = filepointer;
		this.addressingType = addressingType;
	}
	
	public UnresolvedSymbol(ExecutableImage module, String name, int filepointer, AddressingType addressingType) {
		this(module, null, name, filepointer, addressingType);
	}	

	public void resolve(AbsoluteAddress virtualAddress) {
		byte[] data = module.getByteArray();
		long address = Integer.MIN_VALUE;
		if (addressingType == AddressingType.ABSOLUTE) {
			address = virtualAddress.getValue();
		} else if (addressingType == AddressingType.PC_RELATIVE) {
			// offset = absolute address - PC value (PC holds address of _next_ instruction, which is 4 bytes (address size) from file pointer)
			address = virtualAddress.getValue() - module.getVirtualAddress(fp + 4).getValue();
		}
		logger.debug("Patching bytes at VA " + module.getVirtualAddress(fp) + ", offset 0x" + Integer.toHexString(fp) + " in byte array, " +
				"which were " + Integer.toHexString(data[fp]) + " " + Integer.toHexString(data[fp+1]) + " " + Integer.toHexString(data[fp+2]) + " " + Integer.toHexString(data[fp+3])); 
		data[fp]     = (byte)( address        & 0xFFL);  
		data[fp + 1] = (byte)((address >>  8) & 0xFFL);  
		data[fp + 2] = (byte)((address >> 16) & 0xFFL);  
		data[fp + 3] = (byte)((address >> 24) & 0xFFL);
	}

	public String getName() {
		return name;
	}

	public String getFromLibrary() {
		return fromLibrary;
	}

	@Override
	public String toString() {
		return name + "(0x" + Long.toHexString(fp) + ")";
	}

	public ExecutableImage getModule() {
		return module;
	}
	
}
