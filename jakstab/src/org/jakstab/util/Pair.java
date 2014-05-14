/*
 * Pair.java - This file is part of the Jakstab project.
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
package org.jakstab.util;

import org.jakstab.util.Logger;

/**
 * A simple pair class using generics.
 * 
 * @author Johannes Kinder
 */
public class Pair<L,R> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(Pair.class);

	public static <A, B> Pair<A, B> create(A left, B right) {
		return new Pair<A, B>(left, right);
	}

	private final L left;
	private final R right;

	public Pair(final L left, final R right) {
		this.left = left;
		this.right = right;
	}

	public L getLeft() {
		return left;
	}

	public R getRight() {
		return right;
	}
	
	@Override
	public String toString() {
		return "(" + getLeft() + "," + getRight() + ")";
	}

	@Override
	public final boolean equals(Object o) {
		if (!(o instanceof Pair<?, ?>)) return false;
		Pair<?, ?> other = (Pair<?, ?>) o;
		return ((getLeft() == null && other.getLeft() == null) || (getLeft().equals(other.getLeft()))) &&
		((getRight() == null && other.getRight() == null) || (getRight().equals(other.getRight())));
	}
		

	@Override
	public int hashCode() {
		int hLeft = getLeft() == null ? 0 : getLeft().hashCode();
		int hRight = getRight() == null ? 0 : getRight().hashCode();
		return hLeft + (81 * hRight);
	}
}
