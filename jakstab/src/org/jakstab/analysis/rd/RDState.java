package org.jakstab.analysis.rd;

import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * A template for an analysis state for reaching definitions. All methods that need to
 * be implemented are marked with TODO.  
 * 
 */
@SuppressWarnings("unused")
public class RDState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RDState.class);

	@Override
	public AbstractState join(LatticeElement l) {
		RDState other = (RDState)l;
		// TODO Implement the join (supremum) of two RDState objects
		return null;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		RDState other = (RDState)l;
		// TODO Check if this state is less or equal to another state with respect to
		// the lattice of RD states.
		return false;
	}

	@Override
	public boolean isBot() {
		// TODO Check if this is the least element.
		return false;
	}

	@Override
	public boolean isTop() {
		// TODO Check if this is the greatest element
		return false;
	}

	@Override
	public boolean equals(Object arg0) {
		// TODO Override equals such that (x.lessOrEqual(y) && y.lessOrEqual(x)) <=> x.equals(y) <=> y.equals(x)
		return super.equals(arg0);
	}

	@Override
	public int hashCode() {
		// TODO Override hashcode to allow storing this state in a map or set (required)
		return super.hashCode();
	}
	
	@Override
	public String toString() {
		// TODO Print reaching definition information for all variables to a string.
		// This will show up in the generated _cfa.dot - file.
		return "Implement me!";
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		// Not required for secondary analyses
		return null;
	}

	@Override
	public String getIdentifier() {
		// Default ID based on hashcode
		return Integer.toString(hashCode());
	}

	@Override
	public Location getLocation() {
		// No location information in this state
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}

}
