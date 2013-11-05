/*
 * PredicateAbstractionState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.predabs;

import java.util.*;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Characters;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

public class PredicateAbstractionState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(PredicateAbstractionState.class);
	
	final BDD predicates;
	
	PredicateAbstractionState(BDDFactory bf) {
		predicates = bf.one();
	}
	
	PredicateAbstractionState(PredicateAbstractionState proto) {
		predicates = proto.predicates.id();
	}
	
	PredicateAbstractionState(BDD preds) {
		predicates = preds;
	}

	@Override
	public String getIdentifier() {
		return Integer.toString(hashCode());
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public AbstractState join(LatticeElement l) {
		BDD join = predicates.or(((PredicateAbstractionState)l).predicates);
		return new PredicateAbstractionState(join);
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isBot() {
		return predicates == null;
	}

	@Override
	public boolean isTop() {
		return predicates.isOne();
	}
	
	@SuppressWarnings("unchecked")
	RTLExpression getStateFormula(PredicatePrecision prec) {
		
		if (isTop()) return ExpressionFactory.TRUE;
		
		RTLExpression result = null;

		List<byte[]> allsat = predicates.allsat();
		
		for (byte[] assignment : allsat) {
			RTLExpression clause = null;
			for (int i=0; i < assignment.length; i++) {
				RTLExpression p = PredicateMap.getPredicate(i);
				
				if (assignment[i] < 0) continue; 
				if (assignment[i] == 0) p = ExpressionFactory.createNot(p); 
				
				if (clause == null) clause = p;
				else clause = ExpressionFactory.createAnd(clause, p);
			}	
			if (result == null) result = clause;
			else result = ExpressionFactory.createOr(result, clause); 
		}
		assert(result != null);
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (this.equals(l)) return true;
		PredicateAbstractionState other = (PredicateAbstractionState)l;
		return predicates.imp(other.predicates).isOne();
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		if (isBot()) return Characters.BOT;
		return PredicateMap.predicateString(predicates);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((predicates == null) ? 0 : predicates.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PredicateAbstractionState other = (PredicateAbstractionState) obj;
		if (predicates == null) {
			if (other.predicates != null)
				return false;
		} else if (!predicates.equals(other.predicates))
			return false;
		return true;
	}

}
