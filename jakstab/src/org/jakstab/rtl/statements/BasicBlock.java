/*
 * BasicBlock.java - This file is part of the Jakstab project.
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
package org.jakstab.rtl.statements;

import java.util.LinkedList;

import org.jakstab.Program;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Characters;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class BasicBlock extends LinkedList<RTLStatement> implements StateTransformer {

	private static final long serialVersionUID = -386757961616953550L;

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BasicBlock.class);

	public boolean containsLocation(Location l) {
		for (RTLStatement stmt : this)
			if (stmt.getLabel().equals(l))
				return true;
		return false;
	}
	
	public String toStringUntil(Location l) {
		StringBuilder sb = new StringBuilder();
		
		for (RTLStatement stmt : this) {
			sb.append(Program.getProgram().getSymbolFor(stmt.getLabel()));
			sb.append(": ");
			sb.append(stmt).append(Characters.NEWLINE);
			if (l != null && stmt.getLabel().equals(l))
				break;
		}
		if (sb.length() > Characters.NEWLINE.length())
			sb.delete(sb.length() - Characters.NEWLINE.length(), sb.length());
		return sb.toString();
	}
	
	@Override
	public String toString() {
		return toStringUntil(null);
	}

}
