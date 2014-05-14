/*
 * ReachedSet.java - This file is part of the Jakstab project.
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

import java.util.*;

import org.jakstab.analysis.composite.CompositeState;
import org.jakstab.analysis.location.LocationState;
import org.jakstab.cfa.Location;
import org.jakstab.util.Logger;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

/**
 * A set of reached states for use in the CPA algorithm. It can generate lightweight views on 
 * parts of its contents much like an SQL database using select(row) and where(row, hasValue).
 * 
 * @author Johannes Kinder
 */
public class ReachedSet extends AbstractSet<AbstractState> implements Collection<AbstractState> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ReachedSet.class);
	
	private final SetMultimap<AbstractState, CompositeState> compositeMap;
	private static final int indexComponent = 0; 
	private final int selectedRow;
	private final int whereRow;
	private final AbstractState whereState;
	
	public ReachedSet() {
		this(-1, -1, null, HashMultimap.<AbstractState, CompositeState>create(1000, 5));
	}
	
	private ReachedSet(int selectedRow, int whereRow, AbstractState whereState, 
			SetMultimap<AbstractState, CompositeState> compositeMap) {
		this.compositeMap = compositeMap;
		this.selectedRow = selectedRow;
		this.whereRow = whereRow;
		this.whereState = whereState;
	}
	
	public ReachedSet select(int component) {
		assert this.selectedRow == -1;
		return new ReachedSet(component, this.whereRow, this.whereState, this.compositeMap);
	}
	
	public ReachedSet where(int row, AbstractState state) {
		assert this.whereRow == -1 && this.whereState == null;
		return new ReachedSet(this.selectedRow, row, state, this.compositeMap);
	}
	
	public ReachedSet where(Location l) {
		assert this.whereRow == -1 && this.whereState == null;
		return where(0, new LocationState(l));
	}

	public boolean add(AbstractState s) {
		if (s instanceof CompositeState) return add((CompositeState)s);
		else throw new UnsupportedOperationException();
	}

	public boolean remove(AbstractState s) {
		if (s instanceof CompositeState) return remove((CompositeState)s);
		else throw new UnsupportedOperationException();
	}

	public boolean add(CompositeState s) {
		assert selectedRow == -1;
		return compositeMap.put(s.getComponent(indexComponent), s);
	}
	
	public boolean remove(CompositeState s) {
		assert selectedRow == -1;
		return compositeMap.remove(s.getComponent(indexComponent), s);
	}
	
	public int size() {
		if (whereRow < 0)
			return compositeMap.size();
		if (whereRow == indexComponent)
			return compositeMap.get(whereState).size();
		throw new UnsupportedOperationException("Cannot determine reached set size for non-index component restrictions!");
	}

	@Override
	public boolean contains(Object o) {
		if (selectedRow < 0) { 
			if (o instanceof CompositeState) 
				return compositeMap.containsEntry(((CompositeState)o).getComponent(indexComponent), o);
			else throw new UnsupportedOperationException();
		} else {
			for (AbstractState as : this) {
				if (as.equals(o)) return true;
			}
			return false;
		}
	}
	
	public void logHighestStateCounts(int count) {
		AbstractState[] stateArray = compositeMap.keySet().toArray(new AbstractState[compositeMap.keySet().size()]);
		Arrays.sort(stateArray, new Comparator<AbstractState>() {
			@Override
			public int compare(AbstractState o1, AbstractState o2) {
				Integer size1 = compositeMap.get(o1).size();
				Integer size2 = compositeMap.get(o2).size();
				return size2.compareTo(size1);
			}
		});
		
		logger.fatal("==========================================");
		logger.fatal("The " + count + " locations with highest state count:");
		logger.fatal("==========================================");
		for (int i=0; i < Math.min(count, stateArray.length); i++) {
			logger.fatal(stateArray[i] + ":\t" + compositeMap.get(stateArray[i]).size());
		}
		logger.fatal("-------------");
		logger.fatal("Top Location:");
		logger.fatal("-------------");
		for (AbstractState s : compositeMap.get(stateArray[0])) {
			logger.fatal(s);
		}
	}
	
	public void logStates(Location loc) {
		for (CompositeState c : compositeMap.get(new LocationState(loc))) {
			logger.fatal(c);
		}
	}

	@Override
	public Iterator<AbstractState> iterator() {
		return new Iterator<AbstractState>() {
			CompositeState next;
			private Iterator<CompositeState> compIter;
			// Select either generic iterator or refine by indexed map
			{
				if (whereRow == indexComponent) {
					compIter = compositeMap.get(whereState).iterator();
				} else {
					compIter = compositeMap.values().iterator();
				}
			}
			
			@Override
			public boolean hasNext() {
				while (next == null) {
					if (!compIter.hasNext()) return false;
					CompositeState c = compIter.next();
					
					// If we're filtering by indexed component (or not at all), no need for an extra comparison
					if (whereRow < 0 || whereRow == indexComponent) {
						next = c;
					} else {
						if (c.getComponent(whereRow).equals(whereState)) {
							next = c;
						}
					}
				}
				return true;
			}

			@Override
			public AbstractState next() {
				AbstractState retVal;
				if (hasNext()) {
					if (selectedRow < 0) {
						retVal = next;
					} else {
						retVal = next.getComponent(selectedRow);
					}
					next = null;
					return retVal;
				}
				else throw new NoSuchElementException();
			}

			@Override
			public void remove() {
				compIter.remove();
			}
		};
	}


}
