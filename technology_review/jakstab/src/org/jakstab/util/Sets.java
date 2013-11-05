/*
 * Sets.java - This file is part of the Jakstab project.
 * 
 * Cross product method based on code taken from the MultiJava project.
 * Copyright 1998-2002, Iowa State University
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

import java.util.*;

import org.jakstab.util.Logger;

/**
 * Helper functions for sets.
 * 
 * @author Johannes Kinder
 */
public class Sets {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(Sets.class);
	
	public static final <T> Set<Tuple<T>> crossProduct(Tuple<Set<T>> tupleOfSets) { 
		return crossProductToIndex(tupleOfSets, tupleOfSets.size() - 1);
	}

	/*
	 * This functions deals automatically with RTLNumber.WILDCARD and ALL_NUMBERS, since it
	 * will assign the single element of ALL_NUMBERS, the WILDCARD, to all generated tuples
	 */
	private static final <T> Set<Tuple<T>> crossProductToIndex(Tuple<Set<T>> tupleOfSets, int pos) {
		Set<Tuple<T>> setOfTuples = new FastSet<Tuple<T>>();

		if (pos < 0) {
			// we're generating the cross-product of 1 sets => return
			// the singleton set of the empty tuple
			setOfTuples.add(new Tuple<T>(0));
		} else {
			// first recursively generate the cross-product of all earlier
			// positions
			Set<Tuple<T>> setOfEarlierTuples =
				crossProductToIndex(tupleOfSets, pos-1);

			// then extend each of these for each element at this position
			for (Tuple<T> earlierTuple : setOfEarlierTuples) {
				for (T component : tupleOfSets.get(pos)) {

					Tuple<T> newTuple = new Tuple<T>(pos+1);
					for (int i = 0; i < pos; i++) {
						newTuple.set(i, earlierTuple.get(i));
					}
					newTuple.set(pos, component);

					setOfTuples.add(newTuple);
				}
			}
		}
		return setOfTuples;
	}


}
