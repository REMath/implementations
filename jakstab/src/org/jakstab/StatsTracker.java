/*
 * StatsTracker.java - This file is part of the Jakstab project.
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
package org.jakstab;

import java.util.HashMap;
import java.util.Map;

import org.jakstab.rtl.expressions.ExpressionSimplifier;
import org.jakstab.util.Logger;

/**
 * Simple statistics tracker
 */
public class StatsTracker {
	
	private static class SingletonHolder { 
		public static final StatsTracker INSTANCE = new StatsTracker();
	}

	public static StatsTracker getInstance() {
		return SingletonHolder.INSTANCE;
	}

	private StringBuffer statsBuilder;
	private Map<String, String> namedVals;
	private final Logger logger;
	
	private StatsTracker() {
		super();
		logger = Logger.getLogger(ExpressionSimplifier.class);
		statsBuilder = new StringBuffer();
		namedVals = new HashMap<String, String>();
	}
	
	public void record(Object obj) {
		statsBuilder.append(obj);
		statsBuilder.append(',');
	}
	
	public void record(String type, Object obj) {
		namedVals.put(type, obj.toString());
	}
	
	public void print() {
		for (Map.Entry<String, String> entry : namedVals.entrySet()) {
			record(entry.getValue());
		}
		logger.fatal(statsBuilder.toString());
	}

}
