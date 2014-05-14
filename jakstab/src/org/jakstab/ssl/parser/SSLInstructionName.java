/*
 * SSLInstructionName.java - This file is part of the Jakstab project.
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

package org.jakstab.ssl.parser;

import java.util.Locale;
import java.util.Map;
import antlr.collections.AST;

/**
 * This class is used only during parsing the SSL specifications.
 * It holds variable mappings for expansion of subinstructions.
 */
public class SSLInstructionName {
	private Map<String,AST> varMap;
	private String name;
	
	
	public SSLInstructionName(String name, Map<String, AST> varMap) {
		super();
		this.varMap = varMap;
		this.name = name.toUpperCase(Locale.ENGLISH);
	}
	
	public SSLInstructionName(String name) {
		this(name, null);
	}

	public String getName() {
		return name;
	}

	public Map<String, AST> getVarMap() {
		return varMap;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (varMap != null)
			return this.name + "<" + varMap.toString() + ">";
		else return this.name;
	}
	
}
