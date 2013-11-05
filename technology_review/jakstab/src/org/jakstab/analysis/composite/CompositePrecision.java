/*
 * CompositePrecision.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.composite;

import java.util.Arrays;

import org.jakstab.analysis.Precision;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class CompositePrecision implements Precision {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CompositePrecision.class);
	
	private Precision[] precisions;
	
	public CompositePrecision(Precision[] precisions) {
		this.precisions = precisions;
	}

	public Precision getComponent(int i) {
		return precisions[i];
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return Arrays.toString(precisions);
	}

}
