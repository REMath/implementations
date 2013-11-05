/*
 * CPAOperators.java - This file is part of the Jakstab project.
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

import org.jakstab.util.Lattices;
import org.jakstab.util.Logger;

/**
 * Generic implementations of commonly used CPA operators.
 * 
 * @author Johannes Kinder
 */
public final class CPAOperators {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CPAOperators.class);
	
	public static AbstractState mergeSep(AbstractState s1, AbstractState s2, Precision precision) {
		return s2;
	}

	public static AbstractState mergeJoin(AbstractState s1, AbstractState s2, Precision precision) {
		return s2.join(s1);
	}
	
	public static boolean stopSep(AbstractState s, ReachedSet reached, Precision precision) {
		for (AbstractState a : reached) {
			if (s.lessOrEqual(a)) {
				return true;
			}
		}
		return false;
	}

	public static boolean stopJoin(AbstractState s, ReachedSet reached, Precision precision) {
		if (reached.isEmpty()) return false;
		return s.lessOrEqual(Lattices.joinAll(reached));
	}

}
