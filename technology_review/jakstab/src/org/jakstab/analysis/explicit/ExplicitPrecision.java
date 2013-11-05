/*
 * ExplicitPrecision.java - This file is part of the Jakstab project.
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

import java.util.*;

import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.Precision;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.HashMapMap;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

/**
 * @author Johannes Kinder
 */
public class ExplicitPrecision implements Precision {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ExplicitPrecision.class);
	
	public enum TrackingLevel { NONE, REGION, FULL }
	
	private Map<RTLVariable, Integer> thresholds;
	private final int defaultThreshold;
	private Map<RTLVariable, TrackingLevel> varLevels;
	private MapMap<MemoryRegion, Long, TrackingLevel> memLevels;
	
	final SetMultimap<RTLVariable, BasedNumberElement> varMap;
	final Map<MemoryRegion, SetMultimap<Long, BasedNumberElement>> regionMaps;

	public ExplicitPrecision(int defaultThreshold) {
		this.defaultThreshold = defaultThreshold;
		this.thresholds = new HashMap<RTLVariable, Integer>();
		this.varLevels = new HashMap<RTLVariable, TrackingLevel>();
		this.memLevels = new HashMapMap<MemoryRegion, Long, TrackingLevel>();
		varMap = HashMultimap.create();
		regionMaps = new HashMap<MemoryRegion, SetMultimap<Long,BasedNumberElement>>();
	}
	
	public TrackingLevel getTrackingLevel(RTLVariable v) {
		TrackingLevel level = varLevels.get(v);
		if (level == null) return TrackingLevel.FULL;
		else return level;
	}
	
	public TrackingLevel getTrackingLevel(MemoryRegion r, long offset) {
		TrackingLevel level = memLevels.get(r, offset);
		if (level == null) return TrackingLevel.FULL;
		else return level;
	}
	
	public void stopTracking(RTLVariable v) {
		logger.debug("Stopping tracking of variable " + v);
		varLevels.put(v, TrackingLevel.NONE);
	}
	
	public void trackRegionOnly(RTLVariable v) {
		logger.debug("Only tracking region of " + v);
		varLevels.put(v, TrackingLevel.REGION);
	}
	
	public void stopTracking(MemoryRegion r, long offset) {
		logger.debug("Stopping tracking of memory (" + r + "," + offset + ")");
		memLevels.put(r, offset, TrackingLevel.NONE);
	}
	
	public void trackRegionOnly(MemoryRegion r, long offset) {
		logger.debug("Only tracking region of memory (" + r + "," + offset + ")");
		memLevels.put(r, offset, TrackingLevel.REGION);
	}
	
	public int getStoreThreshold(MemoryRegion region, long offset) {
		if (region.equals(MemoryRegion.GLOBAL) || region.equals(MemoryRegion.STACK))
			return defaultThreshold;
		else
			return BoundedAddressTracking.heapThreshold.getValue();
	}
	
	public int getThreshold(RTLVariable v) {
		Integer t = thresholds.get(v);
		if (t == null) return defaultThreshold;
		else return t;
	}
	
	public void setThreshold(RTLVariable v, int threshold) {
		thresholds.put(v, threshold);
	}
	
	@Override
	public String toString() {
		return "Thresholds: " + thresholds;
	}
	
}
