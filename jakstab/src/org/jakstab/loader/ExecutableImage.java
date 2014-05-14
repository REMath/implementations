/*
 * ExecutableImage.java - This file is part of the Jakstab project.
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

import java.io.IOException;
import java.util.Iterator;
import java.util.Set;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.disasm.Disassembler;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;

/**
 * {@code ExecutableImage} provides an interface to information about the logical structure
 * of a binary executable file. Virtual addresses are represented as objects of type
 * {@code AbsoluteAddress} and calculated using the default base address defined by the 
 * image. If the image does not define a base address, a value of zero is used.
 * 
 * Implementations usually assume that multiple executable images do not overlap and perform
 * no relocation.
 */
public interface ExecutableImage {
	
	/**
	 * Returns the virtual address that corresponds to a given file pointer
	 * 
	 * @param fp the file pointer
	 * @return the virtual address
	 */
	public AbsoluteAddress getVirtualAddress(long fp);

	/**
	 * Converts a virtual address into a file pointer into this image.
	 * 
	 * @param va a virtual address that lies within the values of {@code getMinAddress()} 
	 * and {@code getMaxAddress()}.
	 * @return A file pointer, which is an offset into the byte array returned by 
	 * {@code getByteArray()}.
	 */
	public long getFilePointer(AbsoluteAddress va);
	
	/**
	 * Retrieves the entry point of the executable, i.e., the address to which the operating
	 * system loader first transfers control. This might not be the {@code main} function, but
	 * initializer code by the runtime libraries. 
	 * 
	 * @return the virtual address of the executable's entry point.
	 */
	public AbsoluteAddress getEntryPoint();
	
	/**
	 * Get the maximum virtual address mapped to this module. 
	 * 
	 * @return the maximal virtual address.
	 */
	public AbsoluteAddress getMaxAddress();
	
	/**
	 * Get the minimal virtual address mapped to this module.
	 * 
	 * @return the minimal virtual address.
	 */
	public AbsoluteAddress getMinAddress();
	
	/**
	 * Get an iterator that iterates over all bytes that can possibly be 
	 * code in this module.
	 * 
	 * @return an iterator for all code bytes.
	 */
	public Iterator<AbsoluteAddress> codeBytesIterator();
	
	/**
	 * Checks whether the specified virtual address is inside a code area of this executable.  
	 * 
	 * @param va The virtual address to check.
	 * @return True if the address points to a code area, false otherwise.
	 */
	public boolean isCodeArea(AbsoluteAddress va);
	
	/**
	 * Read a static memory location, i.e., the initial value of a global variable or a constant.
	 *   
	 * @param m The absolute virtual address in IL syntax as an {@code RTLMemoryLocation} object. 
	 * @return The result of the memory read as a number object of the requested bit length.
	 */
	public RTLNumber readMemoryLocation(RTLMemoryLocation m) throws IOException;
	
	/**
	 * Determines whether the given address references read only memory. This is
	 * used for limiting conservative approximation of memory to actually modifiable
	 * parts.
	 * 
	 * @param a a virtual address pointing inside the image's address space
	 * @return True if the address references read only memory, false otherwise 
	 */
	public boolean isReadOnly(AbsoluteAddress a);

	/**
	 * Returns the symbol finder for this module.
	 * 
	 * @return a symbol finder
	 */
	public SymbolFinder getSymbolFinder();
	
	/**
	 * Returns a disassembler object for this module, which can be used for disassembling individual
	 * instructions.
	 * 
	 * @return a disassembler object, or {@code null} if no disassembler is available.
	 */
	public Disassembler getDisassembler();
	
	/**
	 * Returns the set of unresolved symbols referenced from this module. Used for resolving
	 * dependencies between multiple modules.  
	 * 
	 * @return a set of unresolved symbols, or an empty set if it does not contain any.
	 */
	public Set<UnresolvedSymbol> getUnresolvedSymbols();
	
	/**
	 * Returns the set of symbols exported by this module. Used for resolving dependencies 
	 * between multiple modules.  
	 * 
	 * @return a set of exported symbols, or an empty set if it does not contain any.
	 */
	public Set<ExportedSymbol> getExportedSymbols();
	
	/**
	 * Returns the file contents as an array of bytes.
	 *  
	 * @return the byte array.
	 */
	public byte[] getByteArray();
}