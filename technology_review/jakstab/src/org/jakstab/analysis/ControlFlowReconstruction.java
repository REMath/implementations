/*
 * ControlFlowReconstruction.java - This file is part of the Jakstab project.
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

import java.util.*;

import org.jakstab.AnalysisManager;
import org.jakstab.AnalysisProperties;
import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.Algorithm;
import org.jakstab.analysis.composite.CompositeProgramAnalysis;
import org.jakstab.analysis.composite.DualCompositeAnalysis;
import org.jakstab.analysis.location.LocationAnalysis;
import org.jakstab.analysis.tracereplay.TraceReplayAnalysis;
import org.jakstab.asm.*;
import org.jakstab.asm.x86.X86Instruction;
import org.jakstab.cfa.*;
import org.jakstab.rtl.statements.BasicBlock;
import org.jakstab.util.*;

/**
 * The control flow reconstruction algorithm in the CPA framework.
 * 
 * @author Johannes Kinder
 */
public class ControlFlowReconstruction implements Algorithm {

	private class PriorityWorklist implements Worklist<AbstractState> {
		private FastSet<AbstractState> worklist = new FastSet<AbstractState>();
		private FastSet<AbstractState> priorityList = new FastSet<AbstractState>();
		
		@Override
		public AbstractState pick() {
			if (!priorityList.isEmpty()) {
				AbstractState p = priorityList.pick();
				//logger.info("Returning prioritized state at " + p.getLocation());
				return p;
			} else {
				return worklist.pick();
			}
		}
		
		@Override
		public boolean add(AbstractState a) {
			if (!program.containsLabel((a.getLocation()))) {
				return priorityList.add(a);
			} else {
				if (priorityList.contains(a)) return false;
				else return worklist.add(a);
			}
		}
		
		public boolean isEmpty() {
			return priorityList.isEmpty() && worklist.isEmpty();
		}
		
		@Override
		public boolean remove(AbstractState a) {
			// Single | is intended, run remove on both
			return priorityList.remove(a) | worklist.remove(a);
		}

		@Override
		public int size() {
			return priorityList.size() + worklist.size();
		}

	}
	
	@SuppressWarnings("unused")
	private class RandomizedWorklist implements Worklist<AbstractState> {

		private ArrayList<AbstractState> list = new ArrayList<AbstractState>(10);
		private Random rand = new Random();
		
		@Override
		public boolean add(AbstractState element) {
			return list.add(element);
		}

		@Override
		public boolean isEmpty() {
			return list.isEmpty();
		}

		@Override
		public AbstractState pick() {
			return list.get(rand.nextInt(list.size()));
		}

		@Override
		public boolean remove(AbstractState element) {
			return list.remove(element);
		}

		@Override
		public int size() {
			return list.size();
		}

	}
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ControlFlowReconstruction.class);
	
	private Program program;
	private ResolvingTransformerFactory transformerFactory;
	private CPAAlgorithm cpaAlgorithm;
	private String status;
	
	public ControlFlowReconstruction(Program program) {

		logger.info("Initializing control flow reconstruction.");
		
		this.program = program;

		// Init CPAs
		List<ConfigurableProgramAnalysis> cpas = new LinkedList<ConfigurableProgramAnalysis>();
		boolean addedExplicitAnalysis = false;
		boolean addedUnderApproximation = false;
		AnalysisManager mgr = AnalysisManager.getInstance();


		for (int i=0; i<Options.cpas.getValue().length(); i++) {
			
			char shortHand = Options.cpas.getValue().charAt(i);
			
			// Special handling for trace replay analysis that really creates multiple CPAs
			if (shortHand == 't') {
				logger.info("--- Using trace replay analysis.");
				for (String fileName : TraceReplayAnalysis.traceFiles.getValue().split(",")) {
					cpas.add(new TraceReplayAnalysis(fileName));
				}
				addedExplicitAnalysis = true;
				addedUnderApproximation = true;
				continue;
			}

			ConfigurableProgramAnalysis cpa = mgr.createAnalysis(shortHand);
			if (cpa != null) {
				AnalysisProperties p = mgr.getProperties(cpa);
				logger.info("--- Using " + p.getName());
				addedExplicitAnalysis |= p.isExplicit();
				cpas.add(cpa);
			} else {
				logger.fatal("No analysis corresponds to letter \"" + shortHand + "\"!");
				System.exit(1);
			}
		}			
		
		if (!addedExplicitAnalysis) {
			logger.fatal("You need to specify at least one explicit value analysis: c, b, x or i");
			System.exit(1);
		}
		
		ConfigurableProgramAnalysis cpa;
		if (!addedUnderApproximation) {
			cpa = new CompositeProgramAnalysis(new LocationAnalysis(), cpas.toArray(new ConfigurableProgramAnalysis[cpas.size()]));
		} else {
			cpa = new DualCompositeAnalysis(new LocationAnalysis(), cpas.toArray(new ConfigurableProgramAnalysis[cpas.size()]));
		}

		// Init State transformer factory
		if (Options.basicBlocks.getValue()) {
			
			if (addedUnderApproximation) {
				logger.fatal("Currently, basic block summarization cannot be combined with under-approximations!");
				System.exit(1);
			}
			transformerFactory = new PessimisticBasicBlockFactory();
			
		} else if (addedUnderApproximation) {
			
			transformerFactory = new AlternatingStateTransformerFactory();
			
		} else {
			switch (Options.procedureAbstraction.getValue()) {
			case 0: 
				transformerFactory = new PessimisticStateTransformerFactory();
				break;
			case 1:
				transformerFactory = new SemiOptimisticStateTransformerFactory();
				break;
			case 2:
				transformerFactory = new OptimisticStateTransformerFactory();
				break;
			default:
				throw new RuntimeException("Invalid procedure abstraction level: " + Options.procedureAbstraction);
			}
		}
		
		//Worklist<AbstractState> worklist = new RandomizedWorklist();
		Worklist<AbstractState> worklist = new PriorityWorklist();
		//Worklist<AbstractState> worklist = new FastSet<AbstractState>();

		cpaAlgorithm = new CPAAlgorithm(program, cpa, transformerFactory, worklist, Options.failFast.getValue());
	}

	public ReachedSet getReachedStates() {
		return cpaAlgorithm.getReachedStates();
	}
	
	public long getNumberOfStatesVisited()  {
		return cpaAlgorithm.getNumberOfStatesVisited();
	}
	
	public AbstractReachabilityTree getART() {
		return cpaAlgorithm.getART();
	}
	
	public boolean isCompleted() {
		return cpaAlgorithm.isCompleted();
	}
	
	public boolean isSound() {
		return !Options.ignoreWeakUpdates.getValue() && transformerFactory.isSound();
	}
	
	public void run() {
		logger.info("Starting control flow reconstruction.");
		try {
			cpaAlgorithm.run();
			status = cpaAlgorithm.isCompleted() ? "OK" : "interrupted"; 
		} catch (StateException e) {
			logger.warn(e.getMessage());
			status = e.getClass().getSimpleName();
			
			Deque<AbstractState> trace = new LinkedList<AbstractState>();
			
			if (cpaAlgorithm.getART() != null) {
				if (Options.errorTrace.getValue()) {

					AbstractState s = e.getState();
					while (s != null) {
						trace.addFirst(s);
						s = cpaAlgorithm.getART().getParent(s);
					}
					
					AbstractState last = null;
					logger.warn("==== Error trace ====");
					for (AbstractState state : trace) {

						// If we use basic blocks, don't attempt to print last edge (is probably a split block)
						if (transformerFactory instanceof PessimisticBasicBlockFactory && 
								state == e.getState())
							break;
						
						if (last != null) {
							for (CFAEdge edge : transformerFactory.getExistingOutEdges(last.getLocation())) {
								if (edge.getTarget().equals(state.getLocation())) {
									logger.warn(edge.getTransformer());
									break;
								}
							}
						}
						
						logger.warn("");
						logger.warn(state);
						logger.warn("");
						last = state;
					}

					// Replay basic block up to the error state location
					if (transformerFactory instanceof PessimisticBasicBlockFactory) {
						for (CFAEdge edge : transformerFactory.getExistingOutEdges(last.getLocation())) {
							BasicBlock bb = (BasicBlock)edge.getTransformer();
							if (bb.containsLocation(e.getState().getLocation())) {
								logger.warn(bb.toStringUntil(e.getState().getLocation()));
								break;
							}
						}
						logger.warn("State before last statement in block:");
						logger.warn(e.getState());
					} 
					// No basic block, just output all transformers where post possibly failed
					else {
						logger.warn("Edges from error state: ");
						for (CFAEdge edge : transformerFactory
								.getExistingOutEdges(e.getState().getLocation()))
							logger.warn(edge.getTransformer());
					}
					
					
					//logger.warn("Error state:");
					//logger.warn(s);
/*
					AbstractState p = cpaAlgorithm.getART().getParent(s);
					while (p != null) {
						//logger.warn(program.getStatement((Location)s.getLocation()));
						//logger.warn(s);
						//s = cpaAlgorithm.getART().getParent(s);
						for (CFAEdge edge : transformerFactory.getExistingOutEdges(p.getLocation())) {
							if (edge.getTarget().equals(s.getLocation())) {
								logger.warn(edge.getTransformer());
								break;
							}
						}
						logger.warn(p);
						s = p;
						p = cpaAlgorithm.getART().getParent(s);
					}
*/
				}

				if (Options.asmTrace.getValue()) {
					logger.warn("==== Error trace (ASM) ====");
					AbsoluteAddress lastAddr = null;
					AbsoluteAddress addr = null;
					AbstractState s = e.getState();
					while (s != null) {
						
						lastAddr = addr;
						addr = s.getLocation().getAddress();
						if (!addr.equals(lastAddr) && program.getModule(addr) != null) {
							StringBuilder sb = new StringBuilder();
							SymbolFinder symFinder = program.getModule(addr).getSymbolFinder();
							sb.append(symFinder.getSymbolFor(addr));
							sb.append(":\t");
							Instruction instr = program.getInstruction(addr);
							if (instr != null) {
								if (instr instanceof X86Instruction &&
										((X86Instruction)instr).hasPrefixLOCK() &&
										((X86Instruction)instr).hasPrefixREPZ()) {
									sb.append(program.getStatement(s.getLocation()));
								} else {
									sb.append(instr.toString(addr.getValue(), symFinder));
								}
							}
							if (symFinder.hasSymbolFor(addr)) sb.append(Characters.NEWLINE);
							logger.warn(sb.toString());
						}
						s = cpaAlgorithm.getART().getParent(s);
					}
				}
			} else {
				logger.warn("No ART has been built, cannot show backtrace!");
			}
			
		} catch (RuntimeException e) {
			// For other runtime exceptions (bugs in Jakstab), set the status to the name of the exception 
			status = e.toString();
			throw e;
		} finally {
			program.setCFA(transformerFactory.getCFA());
			program.setUnresolvedBranches(transformerFactory.getUnresolvedBranches());
		}
	}
	
	public void stop() {
		cpaAlgorithm.stop();
	}
	
	public String getStatus() {
		return status;
	}

}
