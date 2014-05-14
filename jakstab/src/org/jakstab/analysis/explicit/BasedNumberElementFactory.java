/*
 * BasedNumberElementFactory.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Lattices;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class BasedNumberElementFactory implements
		AbstractValueFactory<BasedNumberElement> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BasedNumberElementFactory.class);

	/*
	 * @see org.jakstab.analysis.AbstractValueFactory#createAbstractValue(org.jakstab.rtl.expressions.RTLNumber)
	 */
	@Override
	public BasedNumberElement createAbstractValue(RTLNumber n) {
		assert n != null;
		return new BasedNumberElement(n);
	}

	/*
	 * @see org.jakstab.analysis.AbstractValueFactory#createAbstractValue(java.util.Collection)
	 */
	@Override
	public BasedNumberElement createAbstractValue(Collection<RTLNumber> numbers) {
		List<BasedNumberElement> abstractValues = new LinkedList<BasedNumberElement>();
		for (RTLNumber n : numbers) {
			abstractValues.add(createAbstractValue(n));
		}
		return Lattices.joinAll(abstractValues);
	}

	/*
	 * @see org.jakstab.analysis.AbstractValueFactory#createTop(int)
	 */
	@Override
	public BasedNumberElement createTop(int bitWidth) {
		return BasedNumberElement.getTop(bitWidth);
	}

	@Override
	public BasedNumberElement createFalse() {
		return BasedNumberElement.FALSE;
	}

	@Override
	public BasedNumberElement createTrue() {
		return BasedNumberElement.TRUE;
	}

}
