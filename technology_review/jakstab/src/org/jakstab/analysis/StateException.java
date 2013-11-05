/*
 * StateException.java - This file is part of the Jakstab project.
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

import org.jakstab.util.Logger;

/**
 * An exception that is linked to an abstract state.
 * 
 * @author Johannes Kinder
 */
public abstract class StateException extends RuntimeException {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(StateException.class);
	private static final long serialVersionUID = -8276975101191123334L;
	
	protected AbstractState state;
	
	public StateException(AbstractState s, String msg) {
		super(msg);
		state = s;
	}
	
	public AbstractState getState() {
		return state;
	}

	public void setState(AbstractState state) {
		this.state = state;
	}

}
