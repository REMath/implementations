/*
 * AbstractDomainElement.java - This file is part of the Jakstab project.
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

import java.util.Collection;

/**
 * This interface defines the methods required by the abstract evaluation function
 * of the generic ValuationState.
 * 
 * @author Johannes Kinder
 */
public interface AbstractDomainElement extends AbstractValue {

	/**
	 * Reads abstract values from a partitioned memory at the address 
	 * pointed to by this abstract value. If more than one value is read, they
	 * are not joined but returned as a collection.
	 *  
	 * @param bitWidth The bit width of the memory read
	 * @param store The abstract memory to be read from 
	 * @return a collection of abstract values that were read from the address 
	 * pointed to by this element
	 */
	public Collection<? extends AbstractDomainElement> readStorePowerSet(int bitWidth, PartitionedMemory<? extends AbstractDomainElement> store);
	
	/**
	 * Reads an abstract value from a partitioned memory at the address 
	 * pointed to by this abstract value. If more than one value is read,
	 * their join is returned.
	 *  
	 * @param bitWidth The bit width of the memory read
	 * @param store The abstract memory to be read from 
	 * @return The abstract value that was read
	 */
	public AbstractDomainElement readStore(int bitWidth, PartitionedMemory<? extends AbstractDomainElement> store);

	/**
	 * Writes an abstract value to the given memory.
	 * 
	 * @param <A> The type of abstract value written
	 * @param bitWidth the bit width of the memory write
	 * @param store The abstract memory to be written to
	 * @param value The abstract value to be written
	 */
	public <A extends AbstractDomainElement> void writeStore(int bitWidth, PartitionedMemory<A> store, A value);

	/**
	 * Abstract plus.
	 * @param op
	 * @return
	 */
	public AbstractDomainElement plus(AbstractDomainElement op);

	/**
	 * Abstract arithmetic negation.
	 * @return
	 */
	public AbstractDomainElement negate();
	
	/**
	 * Abstract multiplication.
	 * @param op
	 * @return
	 */
	public AbstractDomainElement multiply(AbstractDomainElement op);
	
	/**
	 * Abstract bit extraction.
	 * @param first
	 * @param last
	 * @return
	 */
	public AbstractDomainElement bitExtract(int first, int last);
	
	/**
	 * Abstract sign extension.
	 * @param first
	 * @param last
	 * @return
	 */
	public AbstractDomainElement signExtend(int first, int last);
	
	/**
	 * Abstract filling with zeros.
	 * @param first
	 * @param last
	 * @return
	 */
	public AbstractDomainElement zeroFill(int first, int last);
	
	@Override
	public AbstractDomainElement join(LatticeElement l);
	
}
