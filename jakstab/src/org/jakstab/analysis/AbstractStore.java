/*
 * AbstractStore.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis;

/**
 * An abstraction of the memory (the store).
 * 
 * @author Johannes Kinder
 */
public interface AbstractStore extends LatticeElement {
	
	/**
	 * Read an abstract value of the given bitwidth at the provided 
	 * symbolic address.
	 *  
	 * @param address a symbolic address to read from
	 * @param bitWidth the bitwidth of the memory access 
	 * @return the abstract value associated with the symbolic address in this store
	 */
	public AbstractValue get(AbstractValue address, int bitWidth);
	
	/**
	 * Write an abstract value with the given bitwidth to the provided 
	 * symbolic address.
	 *  
	 * @param address a symbolic address to write to
	 * @param value the abstract value to write
	 * @param bitWidth the bitwidth of the memory access 
	 */
	public void set(AbstractValue address, AbstractValue value, int bitWidth);

	@Override
	public AbstractStore join(LatticeElement l);

}
