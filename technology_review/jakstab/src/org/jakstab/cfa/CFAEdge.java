/*
 * CFAEdge.java - This file is part of the Jakstab project.
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
package org.jakstab.cfa;

import org.jakstab.analysis.LatticeElement;
import org.jakstab.util.Logger;

/**
 * An edge in the control flow automaton. All fields are mutable to facilitate
 * easier CFA transformations!
 * 
 * @author Johannes Kinder
 */
public class CFAEdge implements Comparable<CFAEdge> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CFAEdge.class);

	/**
	 * The kind of a CFAEdge, i.e., it's value in a multi-valued logic.
	 */
	public enum Kind implements LatticeElement { 
		
		MAY, MUST;

		@Override
		public LatticeElement join(LatticeElement l) {
			if (l.equals(MAY)) return this;
			else return MUST;
		}

		@Override
		public boolean lessOrEqual(LatticeElement l) {
			return this.equals(MAY) || l.equals(MUST);
		}

		@Override
		public boolean isTop() {
			return equals(MUST);
		}

		@Override
		public boolean isBot() {
			return equals(MAY);
		} 
	}

	private Location source;
	private Location target;
	private StateTransformer transformer;
	private Kind kind;

	public CFAEdge(Location source, Location target, StateTransformer transformer, Kind kind) {
		super();
		assert (source != null && target != null) : "Cannot create edge with dangling edges: " + source + " -> " + target;
		assert transformer != null : "Need to specify transformer for edge " + source + " -> " + target;
		assert kind != null : "Need to specify an edge kind";
		this.source = source;
		this.target = target;
		this.transformer = transformer;
		this.kind = kind;
	}
	
	public CFAEdge(Location source, Location target, StateTransformer transformer) {
		this(source, target, transformer, Kind.MAY);
	}

	/**
	 * @return the source
	 */
	public Location getSource() {
		return source;
	}
	
	/**
	 * @return the target
	 */
	public Location getTarget() {
		return target;
	}

	/**
	 * @return the state transformer
	 */
	public StateTransformer getTransformer() {
		return transformer;
	}
	
	public Kind getKind() {
		return kind;
	}

	public void setKind(Kind kind) {
		this.kind = kind;
	}

	public void setTransformer(StateTransformer t) {
		transformer = t;
		assert transformer != null : "Need to specify transformer for edge " + source + " -> " + target;
	}

	public void setSource(Location source) {
		this.source = source;
	}

	public void setTarget(Location target) {
		this.target = target;
	}

	@Override
	public String toString() {
		return source + " -" + kind + "-> " + target;
	}
	
	@Override
	public int compareTo(CFAEdge o) {
		int c = source.compareTo(o.source);
		if (c != 0) return c;
		c = target.compareTo(o.target);
		if (c != 0) return c;
		if (kind.ordinal() < o.kind.ordinal()) return -1;
		if (kind.ordinal() > o.kind.ordinal()) return 1;
		// Source, target, and kind are the same, so compare transformers somehow 
		if (this.transformer.hashCode() < o.transformer.hashCode()) return -1;
		if (this.transformer.equals(o.transformer)) return 0;
		return 1;
	}
	
}
