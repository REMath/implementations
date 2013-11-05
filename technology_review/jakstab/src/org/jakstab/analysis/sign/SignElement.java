/*
 * SignElement.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.sign;

import org.jakstab.analysis.LatticeElement;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public enum SignElement implements LatticeElement {
	TOP, BOT, POSITIVE, NEGATIVE, ZERO;
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SignElement.class);
	
	@Override
	public SignElement join(LatticeElement l) {
		SignElement other = (SignElement)l;
		if (this == other) return this;
		if (this.isBot()) return other;
		if (other.isBot()) return this;
		return TOP; 
	}

	@Override
	public boolean isBot() {
		return this == BOT;
	}

	@Override
	public boolean isTop() {
		return this == TOP;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (this.isBot()) return true;
		if (this == l) return true;
		if (l.isTop()) return true;
		return false;
	}

	@Override
	public String toString() {
		switch (this) {
		case POSITIVE: 
			return "+";
		case NEGATIVE: 
			return "-";
		case ZERO: 
			return "0";
		case TOP: 
			return "?";
		case BOT: 
			return "<BOT>";
		default: 
			throw new RuntimeException("Unknown sign element");
		}
	}

}
