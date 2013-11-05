/*
 * KSetFactory.java - This file is part of the Jakstab project.
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
import java.util.Set;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

public class KSetFactory implements AbstractValueFactory<KSet> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(KSetFactory.class);
	
	private int k;
	
	public KSetFactory(int k) {
		this.k = k;
	}

	@Override
	public KSet createAbstractValue(RTLNumber n) {
		return new KSet(k, new BasedNumberElement(n));
	}

	@Override
	public KSet createAbstractValue(Collection<RTLNumber> numbers) {
		if (numbers.size() > k) return createTop(numbers.iterator().next().getBitWidth());
		Set<BasedNumberElement> set = new FastSet<BasedNumberElement>();
		for (RTLNumber c : numbers) {
			set.add(new BasedNumberElement(c));
		}
		return new KSet(k, set);
	}

	@Override
	public KSet createFalse() {
		return new KSet(k, BasedNumberElement.FALSE);
	}

	@Override
	public KSet createTop(int bitWidth) {
		return KSet.getTop();
	}

	@Override
	public KSet createTrue() {
		return new KSet(k, BasedNumberElement.TRUE);
	}

}
