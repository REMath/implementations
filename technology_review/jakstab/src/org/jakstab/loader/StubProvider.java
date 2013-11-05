/*
 * StubProvider.java - This file is part of the Jakstab project.
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
import org.jakstab.asm.SymbolFinder;

/**
 * @author Johannes Kinder
 */
public interface StubProvider {
	
	public static final long STUB_BASE = 0xFF000000L;
	
	// Stack is not cleared
	public static final int CDECL = 0;
	// All parameters on the stack, stack is cleared
	public static final int STDCALL = 1;
	// Two parameters in registers, remaining on stack, stack is cleared
	public static final int FASTCALL = 2;
	// No function, but a variable
	public static final int EXTERNAL_VARIABLE = 3;

	
	/**
	 * Resolves a reference to an external symbol to a concrete address. The 
	 * StubProvider needs to ensure that the address is properly initialized
	 * with statements or values.
	 *  
	 * @param library the referenced library
	 * @param symbol the referenced symbol, a function or variable name
	 * @return the virtual address of the referenced symbol
	 */
	public AbsoluteAddress resolveSymbol(String library, String symbol);
	
	public SymbolFinder getSymbolFinder();

}
