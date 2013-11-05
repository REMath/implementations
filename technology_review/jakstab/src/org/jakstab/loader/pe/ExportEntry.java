/*
 * ExportEntry.java - This file is part of the Jakstab project.
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

import org.jakstab.asm.AbsoluteAddress;

/**
 * @author Johannes Kinder
 */
class ExportEntry {
	private int ordinal;
	private String name;
	private AbsoluteAddress address;

	/**
	 * @param ordinal
	 * @param name
	 * @param address
	 */
	public ExportEntry(int ordinal, String name, AbsoluteAddress address) {
		this.ordinal = ordinal;
		this.address = address;
		this.name = name;
	}

	/**
	 * @param ordinal
	 * @param address
	 */
	public ExportEntry(int ordinal, AbsoluteAddress address) {
		this.ordinal = ordinal;
		this.address = address;
		this.name = null;
	}

	/**
	 * @return the ordinal
	 */
	public int getOrdinal() {
		return ordinal;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * @param name the name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * @return the address
	 */
	public AbsoluteAddress getAddress() {
		return address;
	}

	@Override
	public String toString() {
		if (name == null) return "Ord(" + ordinal + ")";
		else return name;
	}
	
}
