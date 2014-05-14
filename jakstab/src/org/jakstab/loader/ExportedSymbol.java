/*
 * ExportedSymbol.java - This file is part of the Jakstab project.
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

/**
 * @author Johannes Kinder
 */
public class ExportedSymbol {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ExportedSymbol.class);
	
	private final ExecutableImage module;
	private final String name;
	private final AbsoluteAddress address;
	
	public ExportedSymbol(ExecutableImage module, String name, AbsoluteAddress address) {
		this.module = module;
		this.name = name;
		this.address = address;
	}

	public ExecutableImage getModule() {
		return module;
	}

	public String getName() {
		return name;
	}

	public AbsoluteAddress getAddress() {
		return address;
	}

	@Override
	public String toString() {
		return name + "(" + address + ")";
	}

}
