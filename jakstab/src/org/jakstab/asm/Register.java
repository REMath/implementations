/*
 * Copyright 2000-2002 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
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
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 *  
 */

/* 
 * Original code for this class taken from the Java HotSpot VM. 
 * Modified for use with the Jakstab project. All modifications 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 */

package org.jakstab.asm;

/**
 * Top level class for all registers. Provides a number of common methods.
 */
public abstract class Register extends ImmediateOrRegister {
	protected int number;

	/**
	 * Creates a new invalid register.
	 */
	public Register() {
		number = -1;
	}

	/**
	 * Creates a new register given its code number.
	 */
	public Register(int number) {
		this.number = number;
	}

	/** 
	 * Returns the total number of available registers on this platform
	 */
	public abstract int getNumberOfRegisters();

	/**
	 * Returns whether this register has a valid code number.
	 */
	public boolean isValid() {
		return ((0 <= number) && (number <= getNumberOfRegisters()));
	}

	/**
	 * Returns the code of this register as it appears in instructions.
	 * -1 indicates an invalid register. 
	 */
	public int getNumber() {
		return number;
	}

	public boolean equals(Object obj) {
		if (obj == null || !getClass().equals(obj.getClass())) 
			return false;

		return (((Register)obj).getNumber() == getNumber());
	}

	public int hashCode() {
		return number;
	}

	public abstract boolean isStackPointer();
	public abstract boolean isFramePointer();
	public abstract boolean isFloat();
}
