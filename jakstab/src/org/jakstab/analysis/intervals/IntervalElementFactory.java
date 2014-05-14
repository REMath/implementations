/*
 * IntervalElementFactory.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.intervals;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Lattices;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class IntervalElementFactory implements AbstractValueFactory<IntervalElement> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalElementFactory.class);
	
	public IntervalElementFactory() {
	}

	@Override
	public IntervalElement createAbstractValue(RTLNumber n) {
		return new IntervalElement(MemoryRegion.GLOBAL, n, n);
	}

	@Override
	public IntervalElement createAbstractValue(Collection<RTLNumber> numbers) {
		List<IntervalElement> abstractValues = new LinkedList<IntervalElement>();
		for (RTLNumber n : numbers) {
			abstractValues.add(createAbstractValue(n));
		}
		return Lattices.joinAll(abstractValues);
	}

	@Override
	public IntervalElement createTop(int bitWidth) {
		return IntervalElement.getTop(bitWidth);
	}

	@Override
	public IntervalElement createFalse() {
		return IntervalElement.FALSE;
	}

	@Override
	public IntervalElement createTrue() {
		return IntervalElement.TRUE;
	}
}
