/*
 * TraceReplayAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.tracereplay;


import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.Program;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.CPAOperators;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.statements.RTLAssume;
import org.jakstab.rtl.statements.RTLGoto;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

/**
 * Analysis for replaying the program counter values of a single recorded trace.
 */
public class TraceReplayAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('t');
		p.setName("Trace replay analysis");
		p.setDescription("Replays pre-recorded traces as an under-approximation of control flow.");
	}
	
	public static JOption<String> traceFiles = JOption.create("trace-file", "f", "", "Comma separated list of trace files to use for tracereplay (default is <mainFile>.parsed)");
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(TraceReplayAnalysis.class);

	private final SetMultimap<AbsoluteAddress, AbsoluteAddress> succ;

	public TraceReplayAnalysis(String filename) {
		
		succ = HashMultimap.create();

		BufferedReader in;
		
		try {
			in = new BufferedReader(new FileReader(filename));
		} catch (FileNotFoundException e) {
			logger.fatal("Trace file not found: " + e.getMessage());
			throw new RuntimeException(e);
		}

		// Read entire trace
		
		String line = null;
		AbsoluteAddress curPC = null;
		AbsoluteAddress lastPC = null;
		
		do {
			String lastLine = line; 
			try {
				line = in.readLine();
			} catch (IOException e) {
				logger.fatal("IO error when reading from trace: " + e.getMessage());
				throw new RuntimeException(e);
			}
			if (line != null) {
				
				if (line.charAt(0) == 'A') {
					// Dima's "parsed" format
					curPC = new AbsoluteAddress(Long.parseLong(line.substring(9, line.indexOf('\t', 9)), 16));
				} else {
					// Pure format produced by temu's text conversion
					curPC = new AbsoluteAddress(Long.parseLong(line.substring(0, line.indexOf(':')), 16));
				}
				
				if (line.equals(lastLine)) {
					//logger.warn("Warning: Skipping duplicate line in trace for address " + curPC);
				} else {
					
					// Only add the edge if either source or target are in the program. This collapses library functions. 
					if (lastPC != null && (isProgramAddress(lastPC) || isProgramAddress(curPC))) {
						succ.put(lastPC, curPC);
						lastPC = curPC;
					}
					// Find the first program address
					if (lastPC == null && isProgramAddress(curPC)) {
						lastPC = curPC;
					}
				}
			}
		} while (line != null);
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return null;
	}

	public AbstractState initStartState(Location label) {
		//return new TraceReplayState(succ, ((Location)label).getAddress());
		return TraceReplayState.BOT;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		
		if (s2.isBot()) {
			return s1;
		}
		return s2;
	}

	private static boolean isProgramAddress(AbsoluteAddress a) {
		return Program.getProgram().getModule(a) != null;
	}

	private static boolean isProgramAddress(Location l) {
		return isProgramAddress(l.getAddress());
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {
		return Collections.singleton(singlePost(state, cfaEdge, precision));
	}		

	private AbstractState singlePost(AbstractState state, CFAEdge cfaEdge, Precision precision) {

		
		Location edgeTarget = cfaEdge.getTarget();
		Location edgeSource = cfaEdge.getSource();
		
		// If the entire edge is outside the module, just wait and do nothing 
		if (!isProgramAddress(edgeSource) && !isProgramAddress(edgeTarget)) {
			//logger.debug("Outside of module at edge " + cfaEdge);
			return state;
		}
		
		//logger.debug("Inside module " + cfaEdge);
		
		TraceReplayState tState = (TraceReplayState)state;
		
		RTLStatement stmt = (RTLStatement)cfaEdge.getTransformer();
		
		if (edgeTarget.getAddress().equals(tState.getCurrentPC()) &&  
				!(stmt instanceof RTLAssume && ((RTLAssume)stmt).getSource().getType() == RTLGoto.Type.REPEAT)) {
			// Next statement has same address (and is no back jump from REP), so do not move forward in trace 
			return tState;
		} else {
			// Next statement has a different address (or is the re-execution of a REP prefixed instruction)
			
			if (succ.containsKey(edgeTarget.getAddress())) {
				// Edge goes along a recorded edge
				return new TraceReplayState(succ, edgeTarget.getAddress());
			} else {
				// Edge diverges from trace - either other path or into library

				if (isProgramAddress(edgeTarget)) {
					// Target is in program, but on a different path not taken by this trace
					if (!tState.isBot())
						logger.debug("Visiting edge " + cfaEdge + ", trace expected " + tState.getNextPC() + " next.");
					return TraceReplayState.BOT;
				} else {
					// Target is not in program, so we went into another module (library) that the over-approximation models by a stub
					// In the trace, the TraceReplayAnalysis constructor collapsed the function to a single address
					logger.debug("Jumping out of module to " + edgeTarget + " (" + Program.getProgram().getSymbolFor(edgeTarget) + "), fast forwarding from " + cfaEdge.getSource());
					
					// If we are in a BOT state, we cannot figure out what the native address of the library function is
					if (tState.isBot())
						return TraceReplayState.BOT;
					
					// This only works if only a single library function can be called from each instruction 
					//assert succ.get(edgeSource.getAddress()).size() == 1 : "Successors from " + edgeSource.getAddress() + ": " + succ.get(edgeSource.getAddress());
					
					if (succ.get(edgeSource.getAddress()).size() != 1) {
						logger.error("Cannot map virtual edge " + cfaEdge + " to trace, possible trace successors: " + succ.get(edgeSource.getAddress()));
						return TraceReplayState.BOT;
					}
					
					// Since state is not BOT, we know edgeSource is contained in succ.
					return new TraceReplayState(succ, succ.get(edgeSource.getAddress()).iterator().next());
				}
			}
		}
		
	}
	
	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates, CFAEdge cfaEdge, Precision precision) {
		return null;
	}

}