/*
 * ConcretizationInputBuffer.java - This file is part of the Jakstab project.
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

import java.io.IOException;
import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.loader.ExecutableImage;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ConcretizationInputBuffer extends BinaryInputBuffer {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ConcretizationInputBuffer.class);
	
	private AbstractState state;
	private ExecutableImage module;
	
	public ConcretizationInputBuffer(ExecutableImage module, AbstractState state) {
		this.module = module;
		this.state = state;
	}

	@Override
	public byte getByteAt(int fp) {
		RTLNumber va = ExpressionFactory.createNumber(module.getVirtualAddress(fp).getValue(), 32);
		RTLMemoryLocation m = ExpressionFactory.createMemoryLocation(va, 8);
		Set<Tuple<RTLNumber>> cValSet = state.projectionFromConcretization(m);
		// Hooray for fragile code
		return (byte)cValSet.iterator().next().get(0).intValue();
	}

	@Override
	public long getSize() {
		return module.getMaxAddress().getValue() - module.getMinAddress().getValue();
	}

	@Override
	public int readBYTE() throws IOException {
		return 0xFF & getByteAt(current++);
	}

}
