package org.jakstab.analysis.rd;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;

/**
 * Demo analysis for classroom use.
 * 
 * Template for a reaching definitions analysis based on the CPA framework. All methods that need to
 * be implemented are marked with TODO.  
 */
public class ReachingDefinitionsAnalysis extends SimpleCPA implements ConfigurableProgramAnalysis {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ReachingDefinitionsAnalysis.class);
	
	public static void register(AnalysisProperties p) {
		// This registers the analysis with the framework
		p.setShortHand('r');
		p.setName("Reaching definitions analysis");
		p.setDescription("For each program point, calculate the set of variable definitions that reach it.");
		p.setExplicit(false);
	}

	@Override
	public AbstractState initStartState(Location label) {
		// TODO Return the initial state for a program entry location "label" here.
		return new RDState(); // Dummy
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2) {
		// TODO Implement the merge operator
		return s2; // Dummy
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge edge) {
		// TODO Implement the abstract transfer relation.
		
		// Read statement from control flow edge
		RTLStatement statement = (RTLStatement)edge.getTransformer();
		// Cast the current abstract state to it's type
		final RDState curState = (RDState)state;
		
		// Calculate the set of abstract successors using a visitor pattern
		// The DefaultStatementVisitor throws exceptions on every not overridden visit method
		Set<AbstractState> abstractSuccessors = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			@Override
			protected Set<AbstractState> visitDefault(RTLStatement stmt) {
				// Just return the same state for unsupported statements.
				return Collections.singleton((AbstractState)curState);
			}

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				// TODO Implement transfer function for assignments
				logger.info("Processing assignment at " + stmt.getLabel() + ": " + stmt.toString());
				return Collections.singleton((AbstractState)curState); // Dummy
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				// TODO Implement transfer function for assume
				logger.info("Processing assume at " + stmt.getLabel() + ": " + stmt.toString());
				return Collections.singleton((AbstractState)curState); // Dummy
			}

		});
		
		return abstractSuccessors;
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached) {
		// TODO Implement stop operator
		// You can use the following template, but since
		// lessOrEqual in RDState currently always returns
		// false, the analysis would never terminate.
//		for (AbstractState a : reached) {
//			if (s.lessOrEqual(a)) {
//				return true;
//			}
//		}
//		return false;

		return true; // Dummy
	}
}
