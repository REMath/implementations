/*
 * StatsPlotter.java - This file is part of the Jakstab project.
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
package org.jakstab.util;

import java.io.*;

import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class StatsPlotter {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(StatsPlotter.class);
	
	private static StatsPlotter instance;
	
	private String filename;
	
	public static void create(String filename) {
		instance = new StatsPlotter(filename);
	}
	
	private StatsPlotter(String filename) {
		this.filename = filename;
		(new File(filename)).delete();
	}
	
	public static void plot(String line) {
		if (instance == null)
			return;
		
		try {
			OutputStreamWriter out = new OutputStreamWriter(
					new FileOutputStream(instance.filename, true));
			out.append(line);
			out.append("\n");
			out.close();
		} catch (IOException e) {
			logger.error("Could not write to stats plotting file!");
		}
	}
}
