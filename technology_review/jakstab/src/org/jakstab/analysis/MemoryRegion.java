/*
 * MemoryRegion.java - This file is part of the Jakstab project.
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

import java.util.HashMap;
import java.util.Map;

import org.jakstab.util.Logger;

public class MemoryRegion implements LatticeElement, Comparable<MemoryRegion> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(MemoryRegion.class);
	private static int maxId = -1;
	
	public static MemoryRegion TOP = new MemoryRegion("TOP_Invalid");
	public static MemoryRegion GLOBAL = new MemoryRegion("Global");
	public static MemoryRegion STACK = new MemoryRegion("Stack");

	private final String name;
	private final int id;
	private boolean summary;
	
	private static Map<String, MemoryRegion> regionMap;
	static {
		regionMap = new HashMap<String, MemoryRegion>();
		regionMap.put(TOP.name, TOP);
		regionMap.put(GLOBAL.name, GLOBAL);
		regionMap.put(STACK.name, STACK);
	}
	
	public static MemoryRegion createAsSummary(String name) {
		MemoryRegion region = create(name);
		region.summary = true;
		return region;
	}

	public static MemoryRegion create(String name) {
		MemoryRegion region = regionMap.get(name);
		if (region == null) {
			region = new MemoryRegion(name);
			regionMap.put(name, region);
			logger.debug("Created new memory region: " + name);
		}
		return region;
	}

	private MemoryRegion(String name) {
		super();
		this.id = ++maxId;
		this.name = name;
		this.summary = false;
	}
	
	public boolean isSummary() {
		return summary;
	}
	
	@Override
	public String toString() {
		return name;
	}

	@Override
	public boolean isBot() {
		return this == GLOBAL;
	}

	@Override
	public boolean isTop() {
		return this == TOP;
	}

	@Override
	public MemoryRegion join(LatticeElement l) {
		MemoryRegion other = (MemoryRegion)l;
		if (isTop() || other.isTop()) return TOP;
		if (isBot()) return other;
		if (other.isBot()) return this;
		if (this == other) return this;
		return TOP;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		MemoryRegion other = (MemoryRegion)l;
		return other.isTop() || isBot();
	}
	
	@Override
	public int compareTo(MemoryRegion o) {
		if (o.id > this.id) return 1;
		if (o.id == this.id) return 0;
		return -1;
	}

}
