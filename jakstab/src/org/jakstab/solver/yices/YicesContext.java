/*
 * YicesContext.java - This file is part of the Jakstab project.
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
package org.jakstab.solver.yices;

import java.util.*;

import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class YicesContext {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(YicesContext.class);

	private static ContextPool contextPool = new ContextPool();

	private int maxAssertionId = 0;
	private Map<String, Long> model;
	private Map<Integer,String> retractableAssertions;
	private List<Integer> unsatCore;
	private long yicesContext;

	
	YicesContext() {
		yicesContext = contextPool.acquireContext(); 
		retractableAssertions = new HashMap<Integer, String>();
		//System.out.println("Number of contexts: " + YicesWrapper.numContexts);
	}
	
	public boolean check() {
		String line;
		while ((line = YicesWrapper.getNextOutputLine()) != null) {
			logger.error("Extra yices output: " + line);
			throw new RuntimeException("Extra yices output, check for parse errors!");
		}
		
		if (isInconsistent()) return false;
		readCommand("(check)");
		String result = YicesWrapper.getNextOutputLine();
		if (result == null) return true;

		unsatCore = null;
		model = null;
		if (result.equals("unsat")) {
			unsatCore = new LinkedList<Integer>();
			line = YicesWrapper.getNextOutputLine();
			if (line != null && line.startsWith("unsat core ids: ")) {
				String[] a = line.substring(16).split(" ");
				for (int i=0; i<a.length; i++) {
					unsatCore.add(Integer.parseInt(a[i]));
				}
				logger.debug("Unsatisfiable core:");
				for (Integer clause : unsatCore)
					logger.debug(retractableAssertions.get(clause));
			}
			return false;
		}
		else if (result.equals("sat")) {
			model = new TreeMap<String, Long>();
			while ((line = YicesWrapper.getNextOutputLine()) != null) {
				if (line.length() == 0) continue;
				String[] a = line.substring(3, line.length() - 1).split(" ");
				long value = Long.parseLong(a[1].substring(2), 2);
				model.put(a[0], value);
			}
			
			/*logger.debug("Model:");
			for (Map.Entry<String, Long> entry : model.entrySet())
				logger.debug(entry.getKey() + "\t= 0x" + Long.toHexString(entry.getValue()));
			*/
			
			return true;
		}
		else {
			logger.error("Unknown result: " + result);
			throw new RuntimeException("Yices returned unknown result, check for parse errors!");
			//return false;
		}
	}
	
	public void declareVariable(RTLVariable var) {
		declareVariable(var.getName(), YicesWrapper.makeBVType(var.getBitWidth()));
	}
	
	public void declareVariable(String name, String type) {
		readCommand("(define " + name + "::" + type + ")");
	}

	public boolean isInconsistent() {
		boolean result = YicesWrapper.inconsistent(yicesContext) == 1;
		return result;
	}

	public void pop() {
		readCommand("(pop)");
	}

	public void push() {
		readCommand("(push)");
	}

	public void putAssertion(String expr) {
		readCommand(YicesWrapper.makeOperation("assert", expr));
		// flush possible "unsat" output
		YicesWrapper.getNextOutputLine();
	}

	public int putRetractableAssertion(String expr) {
		readCommand("(assert+ " + expr + ")");
		int id = -1;
		// ids are only output at verbosity > 2
		if (YicesWrapper.getVerbosity() >= 2) {
			try {
				id = Integer.parseInt(YicesWrapper.getNextOutputLine().substring(4));
			} catch (NumberFormatException e) {
				logger.warn("Could not parse assertion ID!");
				throw new RuntimeException("Error parsing Yices output!");
			}
			maxAssertionId = id;
		} else {
			id = ++maxAssertionId;
		}
		retractableAssertions.put(id, expr);
		return id;
	}

	public void readCommand(String cmd) {
		//logger.debug(cmd);
		if (YicesWrapper.read(yicesContext, cmd) == 0) {
			throw new RuntimeException("Yices error: " + YicesWrapper.getLastErrorMessage());
		}
	}

	public void reset() {
		readCommand("(reset)");
		retractableAssertions.clear();
	}
	
	public void retract(int id) {
		readCommand(YicesWrapper.makeOperation("retract", Integer.toString(id)));
	}
	
	

	@Override
	public String toString() {
		return Long.toString(yicesContext);
	}

	@Override
	protected void finalize() throws Throwable {
		try {
			//logger.warn("Finalizing context: " + yicesContext + ", " + YicesWrapper.numContexts + " left");
			contextPool.releaseContext(yicesContext);
		} finally {
			super.finalize();
		}
	}

}
