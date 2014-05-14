/*
 * AbstractRTLExpression.java - This file is part of the Jakstab project.
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
package org.jakstab.rtl.expressions;

import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * Abstract class to encapsulate behavior common to several RTLExpressions.
 * 
 * @author Johannes Kinder
 */
public abstract class AbstractRTLExpression implements RTLExpression {
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(AbstractRTLExpression.class);

	protected SetOfVariables usedVariables = null;

	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {

		if (getBitWidth() != expectedBitWidth) {
			assert getBitWidth() > 0 : "Bitwidth <= 0!";
			throw new TypeInferenceException("Expected " + this + " to be " + expectedBitWidth + " bit, got " + getBitWidth());
		} else {
			return this;
		}
	}

	@Override
	public String toHexString() {
		return toString();
	}
}
