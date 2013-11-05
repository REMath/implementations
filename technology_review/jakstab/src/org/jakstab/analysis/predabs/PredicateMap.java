/*
 * PredicateMap.java - This file is part of the Jakstab project.
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

import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class PredicateMap {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(PredicateMap.class);
	private static ArrayList<RTLExpression> predicates = new ArrayList<RTLExpression>();
	private static Map<RTLExpression, Integer> idMap = new HashMap<RTLExpression, Integer>();
	
	private PredicateMap() {}
	/*public PredicatePrecision() {
		predicates = new ArrayList<RTLExpression>();
		idMap = new HashMap<RTLExpression, Integer>();
	}*/
	
	static {
		addPredicate(ExpressionFactory.createGreaterOrEqual(
				ExpressionFactory.createVariable("eax", 32),
				ExpressionFactory.createNumber(0, 32)
				));
		addPredicate(ExpressionFactory.createLessThan(
				ExpressionFactory.createVariable("ecx", 32),
				ExpressionFactory.createNumber(0, 32)
				));
		addPredicate(ExpressionFactory.createEqual(
				ExpressionFactory.createVariable("eax", 32),
				ExpressionFactory.createNumber(0, 32)
				));
		addPredicate(ExpressionFactory.createEqual(
				ExpressionFactory.createVariable("ebx", 32),
				ExpressionFactory.createNumber(0, 32)
				));
		addPredicate(ExpressionFactory.createEqual(
				ExpressionFactory.createVariable("eax", 32),
				ExpressionFactory.createVariable("ebx", 32)
				));
		//addPredicate(ExpressionFactory.createEqual(
		//		ExpressionFactory.createMemoryLocation(Program.getProgram().getArchitecture().stackPointer(), 32),
		//		Program.getProgram().getArchitecture().returnAddressVariable()
		//		));
	}
	
	public static void addPredicate(RTLExpression p) {
		idMap.put(p, predicates.size());
		predicates.add(p);
	}
	
	public static RTLExpression getPredicate(int id) {
		return predicates.get(id);
	}
	
	public static Iterator<RTLExpression> predicateIterator() {
		return new Iterator<RTLExpression>() {
			int next = 0;

			public boolean hasNext() {
				return next < predicates.size();
			}

			public RTLExpression next() {
				if (next >= predicates.size()) 
					throw new NoSuchElementException();
				return getPredicate(next++);
			}

			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}
	
	public static int getId(RTLExpression p) {
		return idMap.get(p);
	}
	
	public static int getMaxIndex() {
		return predicates.size() - 1;
	}
	
	@SuppressWarnings("unchecked")
	public static String predicateString(BDD predicates) {
		StringBuilder res = new StringBuilder();
		for (byte[] assignment : (List<byte[]>)predicates.allsat()) {
			res.append("(");
			for (int i = 0; i < assignment.length; i++) {
				if (assignment[i] < 0) continue; // don't care
				if (assignment[i] == 0) res.append('-');
				res.append(PredicateMap.getPredicate(i));
				res.append(" & ");
			}
			res.append(") |");
		}
		
		return res.toString();
	}
	
}
