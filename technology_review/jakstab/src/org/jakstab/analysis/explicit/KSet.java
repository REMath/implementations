/*
 * KSet.java - This file is part of the Jakstab project.
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
import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.*;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class KSet implements AbstractDomainElement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(KSet.class);
	
	private static Set<BasedNumberElement> FULL_SET = Collections.singleton(null);
	private static KSet TOP = new KSet(-1, FULL_SET);
	
	static KSet getTop() {
		return TOP;
	}
	
	private Set<BasedNumberElement> set;
	private final int bound;
	
	public KSet(int bound, BasedNumberElement element) {
		this(bound);
		this.set.add(element);
	}

	public KSet(int bound) {
		this(bound, new FastSet<BasedNumberElement>());
	}
	
	public KSet(int bound, Set<BasedNumberElement> set) {
		this.bound = bound;
		this.set = set;
	}

	@Override
	public Set<RTLNumber> concretize() {
		// If abstract value is top, return full set
		if (isTop()) return RTLNumber.ALL_NUMBERS;

		Set<RTLNumber> result = new FastSet<RTLNumber>();
		for (BasedNumberElement e : set) {
			Set<RTLNumber> ec = e.concretize();
			for (RTLNumber c : ec) {
				if (c == null)
					return RTLNumber.ALL_NUMBERS;
				result.add(c);
			}
		}
		return result;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !isTop() && set.size() == 1 && set.iterator().next().hasUniqueConcretization();
	}

	@Override
	public KSet join(LatticeElement l) {
		KSet other = (KSet)l;
		
		if (other.isTop() || this.isBot()) return other;
		if (this.isTop() || other.isBot()) return this;
		
		KSet result = new KSet(Math.max(bound, other.bound));
		for (BasedNumberElement e : set)
			if (!result.add(e)) return result;

		for (BasedNumberElement e : other.set)
			if (!result.add(e)) return result;

		return result;
		/*
		Set<BasedNumberElement> resultSet = new FastSet<BasedNumberElement>();
		int resultBound = Math.max(bound, other.bound);
		resultSet.addAll(set);
		resultSet.addAll(other.set);
		if (resultSet.size() > resultBound) {
			// Create new top element
			resultSet = FULL_SET;
		}
		
		KSet result = new KSet(resultBound, resultSet);

		return result;*/
	}

	@Override
	public boolean isBot() {
		return set.isEmpty();
	}

	@Override
	public boolean isTop() {
		return set == FULL_SET;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		KSet other = (KSet)l;
		if (other.isTop() || isBot()) return true;
		if (other.isBot() || isTop()) return false;
		return other.set.containsAll(set);
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		Set<BasedNumberElement> resultSet = new FastSet<BasedNumberElement>();
		int k = 0;
		for (BasedNumberElement e : set) {
			KSet memVal = (KSet)store.get(e.getRegion(), e.getNumber().longValue(), bitWidth);
			if (!memVal.isBot() && !memVal.isTop()) {
				resultSet.addAll(memVal.set);
				k = Math.max(k, memVal.bound);				
			}
		}
		return new KSet(k, resultSet);
	}

	@Override
	public Collection<? extends AbstractDomainElement> readStorePowerSet(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		if (isTop()) return Collections.singleton(getTop());
		Set<AbstractDomainElement> result = new FastSet<AbstractDomainElement>();
		for (BasedNumberElement e : set) {
			result.add(store.get(e.getRegion(), e.getNumber().longValue(), bitWidth));
		}
		return result;
	}

	@Override
	public <A extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<A> store, A value) {
		
		if (isTop()) {
			store.setTop();
		} else if (set.size() == 1) {
			// Strong updates
			BasedNumberElement e = set.iterator().next();
			e.writeStore(bitWidth, store, value);
		} else {
		// Weak updates
			for (BasedNumberElement e : set) {
				if (e.isTop()) 
					store.setTop();
				else if (e.isNumberTop()) 
					store.setTop(e.getRegion());
				else 
					store.weakUpdate(e.getRegion(), e.getNumber().longValue(), bitWidth, value);
			}
		}		
	}

	@Override
	public AbstractDomainElement bitExtract(int first, int last) {
		if (isTop() || isBot()) return this;
		KSet resultSet = new KSet(bound);
		for (BasedNumberElement e : set) {
			resultSet.add(e.bitExtract(first, last));
		}
		return resultSet;
	}

	@Override
	public AbstractDomainElement multiply(AbstractDomainElement op) {
		KSet other = (KSet)op;
		if (isTop() || isBot()) return this;
		if (other.isTop() || other.isBot()) return other;

		KSet resultSet = new KSet(Math.max(bound, other.bound));
		for (BasedNumberElement e : set) {
			for (BasedNumberElement ePrime : other.set) {
				// If defaults to TOP return TOP
				if (!resultSet.add(e.multiply(ePrime)))
					return resultSet;
			}
		}
		return resultSet;
	}

	@Override
	public AbstractDomainElement negate() {
		if (isTop() || isBot()) return this;
		KSet resultSet = new KSet(bound);
		for (BasedNumberElement e : set) {
			resultSet.add(e.negate());
		}
		return resultSet;
	}

	@Override
	public AbstractDomainElement plus(AbstractDomainElement op) {
		KSet other = (KSet)op;
		if (isTop() || isBot()) return this;
		if (other.isTop() || other.isBot()) return other;
		KSet resultSet = new KSet(Math.max(bound, other.bound));
		for (BasedNumberElement e : set) {
			for (BasedNumberElement ePrime : other.set) {
				// If defaults to TOP return TOP
				if (!resultSet.add(e.plus(ePrime)))
					return resultSet;
			}
		}
		return resultSet;
	}

	@Override
	public AbstractDomainElement signExtend(int first, int last) {
		if (isTop() || isBot()) return this;
		KSet resultSet = new KSet(bound);
		for (BasedNumberElement e : set) {
			resultSet.add(e.signExtend(first, last));
		}
		return resultSet;
	}

	@Override
	public AbstractDomainElement zeroFill(int first, int last) {
		if (isTop() || isBot()) return this;
		KSet resultSet = new KSet(bound);
		for (BasedNumberElement e : set) {
			resultSet.add(e.zeroFill(first, last));
		}
		return resultSet;
	}
	
	/**
	 * Add an element to this KSet. If it exceeds the bound, set this
	 * set to TOP.
	 * @param e the element to add
	 * @return false if the resulting set is TOP, true otherwise
	 */
	private boolean add(BasedNumberElement e) {
		
		assert e != null;

		// If TOP element, don't add anything
		if (isTop()) 
			return false;
		
		set.add(e);
		// If bound exceeded, set to TOP
		if (set.size() > bound) {
			set = FULL_SET;
			return false;
		} else {
			return true;
		}
	}

	@Override
	public String toString() {
		return set.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + bound;
		result = prime * result + ((set == null) ? 0 : set.hashCode());
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
		KSet other = (KSet) obj;
		if (bound != other.bound)
			return false;
		if (set == null) {
			if (other.set != null)
				return false;
		} else if (!set.equals(other.set))
			return false;
		return true;
	}

}
