/*
 * AbstractReachabilityTree.java - This file is part of the Jakstab project.
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

import org.jakstab.util.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

/**
 * An abstract reachability tree for recording witness traces.
 * 
 * @author Johannes Kinder
 */
public class AbstractReachabilityTree {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(AbstractReachabilityTree.class);
	
	private AbstractState root;
	private SetMultimap<AbstractState, AbstractState> parentChildrenMap;
	private Map<AbstractState, AbstractState> childParentMap;
	private SetMultimap<AbstractState, AbstractState> coveringMap;
	private SetMultimap<AbstractState, AbstractState> coveredMap;
	
	public AbstractReachabilityTree() {
		parentChildrenMap = HashMultimap.create();
		childParentMap = new HashMap<AbstractState, AbstractState>();
		coveringMap = HashMultimap.create();
		coveredMap = HashMultimap.create();
	}
	
	/**
	 * Get the ART root.
	 * 
	 * @return the root of the ART.
	 */
	public AbstractState getRoot() {
		return root;
	}
	
	public void setRoot(AbstractState root) {
		this.root = root;
		addChild(null, root);
	}
	
	public Set<AbstractState> getChildren(AbstractState parent) {
		return parentChildrenMap.get(parent);
	}
	
	public AbstractState getParent(AbstractState child) {
		return childParentMap.get(child);
	}
	
	public void addChild(AbstractState parent, AbstractState child) {
		//logger.debug("Adding child " + child.getIdentifier() + " to " + (parent == null ? "null" : parent.getIdentifier()));
		assert childParentMap.isEmpty() || parent != null;
		
		parentChildrenMap.put(parent, child);
		childParentMap.put(child, parent);
		//assert (isTree()) : "ART lost tree property!";
	}
	
	public void addCovered(AbstractState s, AbstractState coveringState) {
		logger.debug(coveringState.getIdentifier() + " covers state " + s.getIdentifier());
		coveredMap.put(s, coveringState);
		coveringMap.put(coveringState, s);
	}
	
	public void addCovered(AbstractState s, Collection<AbstractState> coveringStates) {
		coveredMap.putAll(s, coveringStates);
		for (AbstractState coveringState : coveringStates)
			coveringMap.put(coveringState, s);
	}
	
	/**
	 * Returns which states are covering the given state.
	 */
	public Set<AbstractState> getCoveringStates(AbstractState s) {
		return coveredMap.get(s);
	}
	
	/**
	 * Return the states which are covered by the given state.
	 */
	public Set<AbstractState> getCoveredStates(AbstractState s) {
		return coveringMap.get(s);
	}

	public void remove(AbstractState s) {
		logger.debug("Removing " + s.getIdentifier());
		
		List<AbstractState> children = new LinkedList<AbstractState>(getChildren(s));
		for (AbstractState child : children) {
			remove(child);
		}
		parentChildrenMap.remove(getParent(s), s);
		childParentMap.remove(s);
		assert (isTree()) : "ART lost tree property!";
	}

	public void replace(AbstractState oldState, AbstractState newState) {
		assert newState != oldState;
		
		// Also the new state can have children already if it has been produced
		// by prec or post before.
		// If it already has children, it's equal to an existing state and will
		// not pass through stop, so we can ignore the new state.
		
		if (!getChildren(newState).isEmpty() || getParent(newState) != null) {
			logger.debug("State " + newState.getIdentifier() + " has been produced before, not adding to ART.");
			return;
		}
		
		// If the old state has children, it means that it has been picked from
		// the worklist even though it has been processed before - it can never
		// have passed stop, though, and not been added to the worklist twice,
		// since the worklist is a set.
		assert (getChildren(oldState).isEmpty());

		logger.debug("Replacing " + oldState.getIdentifier() + " with " + newState.getIdentifier());
		
		// We have to be careful not to introduce loops. Replacing means merging
		// incoming and outgoing edges

		
		/*
		Set<AbstractState> children = new FastSet<AbstractState>(getChildren(oldState));
		for (AbstractState child : children) {
			parentChildrenMap.remove(oldState, child);
			childParentMap.remove(child);
			addChild(newState, child);
		}
		*/
		
		//AbstractState newParent = getParent(newState);
		AbstractState oldParent = getParent(oldState);
		
//		assert newParent != null || newState.equals(getRoot());
		assert oldParent != null || oldState.equals(getRoot());
		
/*		if (newParent != oldParent) {

			if (newParent != null) {
				parentChildrenMap.remove(newParent, newState);
				childParentMap.remove(newState);
			}*/

		childParentMap.remove(oldState);
		parentChildrenMap.remove(oldParent, oldState);
		addChild(oldParent, newState);
//		}

		/*
		Set<AbstractState> coveredStates = new FastSet<AbstractState>(getCoveredStates(oldState));
		Set<AbstractState> coveringStates = new FastSet<AbstractState>(getCoveringStates(oldState));
		for (AbstractState covered : coveredStates) {
			coveringMap.remove(oldState, covered);
			coveredMap.remove(covered, oldState);
			addCovered(covered, newState);
		}
		for (AbstractState covering : coveringStates) {
			coveredMap.remove(oldState, covering);
			coveredMap.put(newState, covering);
			addCovered(newState, covering);
		}
			
		coveringMap.removeAll(oldState);
		*/
		assert (isTree()) : "ART lost tree property!";
	}
	
	public boolean isInChildParentMap(AbstractState a) {
		return childParentMap.containsKey(a);
	}
	
	public boolean isInParentChildrenMap(AbstractState a) {
		return parentChildrenMap.containsKey(a);
	}
	
	private boolean isTree() {
		Deque<AbstractState> worklist = new LinkedList<AbstractState>();
		Set<AbstractState> visited = new HashSet<AbstractState>();
		
		worklist.add(getRoot());
		while (!worklist.isEmpty()) {
			AbstractState a = worklist.pop();
			if (visited.contains(a)) {
				logger.debug("State " + a.getIdentifier() + " has multiple paths in tree!");
				return false;
			}
			visited.add(a);
			worklist.addAll(getChildren(a));
		}
		
		return true;
	}
}
