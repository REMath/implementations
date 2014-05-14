package org.jakstab.analysis.rd;

import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Logger;

/**
 * Template for a helper class for the reaching definition for an individual variable.
 * Implementing this class is not required, but is probably helpful. 
 */
@SuppressWarnings("unused")
public class RDElement implements LatticeElement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RDElement.class);

	@Override
	public AbstractValue join(LatticeElement l) {
		RDElement other = (RDElement)l;
		// TODO Join two different reaching definitions
		return null;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		RDElement other = (RDElement)l;
		// TODO Check if this value is less or equal to another value with respect to
		// the lattice of RD values.
		return false;
	}

	@Override
	public boolean isBot() {
		// TODO Bottom element?
		return false;
	}

	@Override
	public boolean isTop() {
		// TODO Top element?
		return false;
	}
}
