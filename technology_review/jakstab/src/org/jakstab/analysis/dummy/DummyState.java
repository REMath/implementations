/*
 * DummyState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.dummy;

import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Tuple;

public class DummyState implements AbstractState {
	
	DummyState() {
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		return equals(l);
	}

	@Override
	public boolean isTop() {
		return true;
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		
		Tuple<RTLNumber> cVector = new Tuple<RTLNumber>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			if (expressions[i] instanceof RTLNumber) {
				cVector.set(i, (RTLNumber)expressions[i]);
			} else {
				return null; 
			} 
		}
		return Collections.singleton(cVector);
		
		/*
		// This makes the dummy analysis resolve both branches of a conditional jump.

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			if (expressions[i] instanceof RTLNumber) {
				cValues.set(i, Collections.singleton((RTLNumber)expressions[i]));
			} else if (expressions[i].getBitWidth() == 1) {
				ExpressionFactory factory = ExpressionFactory.getInstance();
				Set<RTLNumber> tf = new FastSet<RTLNumber>();
				tf.add(factory.TRUE);
				tf.add(factory.FALSE);
				cValues.set(i, tf);
			} else {
				cValues.set(i, RTLNumber.ALL_NUMBERS);
			}
		}

		return Sets.crossProduct(cValues);
		*/
	}

	@Override
	public AbstractState join(LatticeElement l) {
		return this;
	}

	@Override
	public Location getLocation() {
		return null;
	}

	@Override
	public String getIdentifier() {
		return "DUMMY";
	}

}
