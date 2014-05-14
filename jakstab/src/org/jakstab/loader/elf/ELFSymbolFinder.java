/*
 * ELFSymbolFinder.java - This file is part of the Jakstab project.
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
package org.jakstab.loader.elf;

import java.util.HashMap;
import java.util.Map;

import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ELFSymbolFinder implements SymbolFinder {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ELFSymbolFinder.class);
	
	private ELFModule module;
	Map<AbsoluteAddress, String> symbols;
	
	public ELFSymbolFinder(ELFModule module) {
		super();
		this.module = module;
		symbols = new HashMap<AbsoluteAddress, String>();

		symbols.putAll(module.getSymbolMap());

		symbols.put(this.module.getEntryPoint(), "start");
	}

	@Override
	public String getSymbolFor(long address) {
		return getSymbolFor(new AbsoluteAddress(address));
	}
	
	@Override
	public String getSymbolFor(AbsoluteAddress va) {
		String symbol = symbols.get(va);
		if (symbol != null) return symbol;
		else return va.toString();
	}

	@Override
	public boolean hasSymbolFor(AbsoluteAddress va) {
		return symbols.containsKey(va);
	}
}
