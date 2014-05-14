/*
 * Main.java - This file is part of the Jakstab project.
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

package org.jakstab;

import java.io.*;
import java.util.*;

import org.jakstab.transformation.DeadCodeElimination;
import org.jakstab.transformation.ExpressionSubstitution;
import org.jakstab.util.*;
import org.jakstab.analysis.*;
import org.jakstab.analysis.composite.CompositeState;
import org.jakstab.analysis.explicit.BasedNumberValuation;
import org.jakstab.analysis.explicit.BoundedAddressTracking;
import org.jakstab.analysis.procedures.ProcedureAnalysis;
import org.jakstab.analysis.procedures.ProcedureState;
import org.jakstab.asm.*;
import org.jakstab.cfa.Location;
import org.jakstab.loader.*;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.ssl.Architecture;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import antlr.ANTLRException;

public class Main {

	private static Logger logger = Logger.getLogger(Main.class);;

	private final static String version = "0.8.3";

	private static volatile Algorithm activeAlgorithm;
	private static volatile Thread mainThread;
	
	public static void main(String[] args) {

		mainThread = Thread.currentThread();
		StatsTracker stats = StatsTracker.getInstance();

		// Parse command line
		Options.parseOptions(args);

		logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);
		logger.error("   Jakstab " + version);
		logger.error("   Copyright 2007-2012  Johannes Kinder  <johannes.kinder@epfl.ch>");
		logger.error("");
		logger.error("   Jakstab comes with ABSOLUTELY NO WARRANTY. This is free software,");
		logger.error("   and you are welcome to redistribute it under certain conditions.");
		logger.error("   Refer to LICENSE for details.");
		logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);

		/////////////////////////
		// Parse SSL file

		Architecture arch;
		try {
			arch = new Architecture(Options.sslFilename.getValue());
		} catch (IOException e) {
			logger.fatal("Unable to open SSL file!", e);
			return;
		} catch (ANTLRException e)  {
			logger.fatal("Error parsing SSL file!", e);
			return;
		}

		long overallStartTime = System.currentTimeMillis();

		/////////////////////////
		// Parse executable

		Program program = Program.createProgram(arch);

		File mainFile = new File(Options.mainFilename).getAbsoluteFile();

		String baseFileName = null; 

		try {
			// Load additional modules
			for (String moduleName : Options.moduleFilenames) {
				logger.warn("Parsing " + moduleName + "...");
				File moduleFile = new File(moduleName).getAbsoluteFile();
				program.loadModule(moduleFile);
				
				// If we are processing drivers, use the driver's name as base name
				if (Options.wdm.getValue() && moduleFile.getName().toLowerCase().endsWith(".sys")) {
					baseFileName = getBaseFileName(moduleFile);
				}
			}
			// Load main module last
			logger.warn("Parsing " + Options.mainFilename + "...");
			program.loadMainModule(mainFile);
			
			// Use main module as base name if we have none yet
			if (baseFileName == null)
				baseFileName = getBaseFileName(mainFile);

		} catch (FileNotFoundException e) {
			logger.fatal("File not found: " + e.getMessage());
			return;
		} catch (IOException e) {
			logger.fatal("IOException while parsing executable!", e);
			//e.printStackTrace();
			return;
		} catch (BinaryParseException e) {
			logger.fatal("Error during parsing!", e);
			//e.printStackTrace();
			return;
		}
		logger.info("Finished parsing executable.");


		// Change entry point if requested
		if (Options.startAddress.getValue() > 0) {
			logger.verbose("Setting start address to 0x" + Long.toHexString(Options.startAddress.getValue()));
			program.setEntryAddress(new AbsoluteAddress(Options.startAddress.getValue()));
		}

		// Add surrounding "%DF := 1; call entrypoint; halt;" 
		program.installHarness(Options.heuristicEntryPoints.getValue() ? new HeuristicHarness() : new DefaultHarness());

		int slashIdx = baseFileName.lastIndexOf('\\');
		if (slashIdx < 0) slashIdx = baseFileName.lastIndexOf('/');
		if (slashIdx < 0) slashIdx = -1;
		slashIdx++;
		stats.record(baseFileName.substring(slashIdx));
		stats.record(version);


		//StatsPlotter.create(baseFileName + "_states.dat");
		//StatsPlotter.plot("#Time(ms)\tStates\tInstructions\tGC Time\tSpeed(st/s)");		
		
		// Catches control-c and System.exit
		Thread shutdownThread = new Thread() {
			@Override
			public void run() {
				if (mainThread.isAlive() && activeAlgorithm != null) {
					//stop = true; // Used for CFI checks
					activeAlgorithm.stop();
					try {
						mainThread.join();
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
			}
		};
		Runtime.getRuntime().addShutdownHook(shutdownThread);

		// Add shutdown on return pressed for eclipse
		if (!Options.background.getValue() && System.console() == null) {
			logger.info("No console detected (eclipse?). Press return to terminate analysis and print statistics.");
			Thread eclipseShutdownThread = new Thread() { 
				public void run() { 
					try { 
						System.in.read(); 
					} catch (IOException e) { 
						e.printStackTrace(); 
					} 
					System.exit(1);
				} 
			};
			// yices.dll blocks for input on load for some reason, so load it before we start reading from System.in  
			// If you are having problems with that, uncomment the next line
			// org.jakstab.solver.yices.YicesWrapper.getVersion();
			eclipseShutdownThread.start();
		}
		

		// Necessary to stop shutdown thread on exceptions being thrown
		try {

			/////////////////////////
			// Reconstruct Control Flow
			ControlFlowReconstruction cfr = new ControlFlowReconstruction(program);
			// Execute the algorithm
			try {
				runAlgorithm(cfr);
			} catch (RuntimeException r) {
				logger.error("!! Runtime exception during Control Flow Reconstruction! Trying to shut down gracefully.");
				r.printStackTrace();
			}
			long overallEndTime = System.currentTimeMillis();

			ReachedSet reached = cfr.getReachedStates();
			if (Options.dumpStates.getValue()) {
				// output
				logger.fatal("=================");
				logger.fatal(" Reached states:");
				logger.fatal("=================");
				AbstractState[] stateArray = reached.toArray(new AbstractState[reached.size()]);
				Arrays.sort(stateArray, new Comparator<AbstractState>() {
					@Override
					public int compare(AbstractState o1, AbstractState o2) {
						return ((CompositeState)o1).getLocation().compareTo(((CompositeState)o2).getLocation());
					}
				});
				Location lastLoc = null;
				for (AbstractState s : stateArray) {
					if (!s.getLocation().equals(lastLoc)) {
						lastLoc = s.getLocation();
						logger.fatal("");
					}
					logger.fatal(s);
				}
			}

			int stateCount = reached.size();

			if (Options.outputLocationsWithMostStates.getValue()) reached.logHighestStateCounts(10);

			if (!cfr.isCompleted()) {
				logger.error(Characters.starredBox("WARNING: Analysis interrupted, CFG might be incomplete!"));
			}

			if (!cfr.isSound()) {
				logger.error(Characters.starredBox("WARNING: Analysis was unsound!"));
			}

			/*logger.verbose("Unresolved locations: " + program.getUnresolvedBranches());
			for (Location l : program.getUnresolvedBranches()) {
				AbsoluteAddress a = ((Location)l).getAddress();
				if (program.getInstruction(a) == null) {
					logger.verbose(l + ": " + program.getStatement((Location)l));
				} else {
					logger.verbose(a + "\t" + program.getInstructionString(a));
				}
			}*/

			int indirectBranches = program.countIndirectBranches();

			logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);
			logger.error( "   Statistics for Control Flow Reconstruction");
			logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);
			logger.error( "   Runtime:                     " + String.format("%8dms", (overallEndTime - overallStartTime)));
			logger.error( "   Instructions:                        " + String.format("%8d", program.getInstructionCount()));
			logger.error( "   RTL Statements:                      " + String.format("%8d", program.getStatementCount()));
			logger.error( "   CFA Edges:                           " + String.format("%8d", program.getCFA().size()));
			logger.error( "   States visited:                      " + String.format("%8d", cfr.getNumberOfStatesVisited()));
			logger.error( "   Final state space:                   " + String.format("%8d", stateCount));
			logger.error( "   Finished normally:                   " + String.format("%8b", cfr.isCompleted()));
			logger.error( "   Analysis result:                     " + cfr.getStatus());
			//				logger.error( "   Sound:                               " + String.format("%8b", cfr.isSound()));
			logger.error( "   Indirect Branches (no import calls): " + String.format("%8d", indirectBranches));
			logger.error( "   Unresolved Branches:                 " + String.format("%8d", program.getUnresolvedBranches().size()));
			logger.debug("   FastSet conversions:                 " + String.format("%8d", FastSet.getConversionCount()));
			logger.debug("   Variable count:                      " + String.format("%8d", ExpressionFactory.getVariableCount()));
			logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);

			
			stats.record(program.getInstructionCount());
			stats.record(program.getStatementCount());
			stats.record(program.getCFA().size());
			stats.record(indirectBranches);
			stats.record(program.getUnresolvedBranches().size());
			stats.record(cfr.getNumberOfStatesVisited());
			stats.record(stateCount);
			stats.record(Math.round((overallEndTime - overallStartTime)/1000.0));
			stats.record(cfr.getStatus());
			stats.record(Options.cpas.getValue());
			stats.record(BoundedAddressTracking.varThreshold.getValue());
			stats.record(BoundedAddressTracking.heapThreshold.getValue());
			stats.record(Options.basicBlocks.getValue() ? "y" : "n");
			stats.record(Options.summarizeRep.getValue() ? "y" : "n" );
			stats.record(BasedNumberValuation.ExplicitPrintfArgs);
			stats.record(BasedNumberValuation.OverAppPrintfArgs);
			
			stats.print();

			ProgramGraphWriter graphWriter = new ProgramGraphWriter(program);
			
			graphWriter.writeDisassembly(program, baseFileName + "_jak.asm");

			if (!(cfr.isCompleted() && Options.secondaryCPAs.getValue().length() > 0)) {
				if (!Options.noGraphs.getValue()) {
					graphWriter.writeControlFlowAutomaton(baseFileName + "_cfa");
					graphWriter.writeAssemblyCFG(baseFileName + "_asmcfg");
				}
				//if (Options.errorTrace) graphWriter.writeART(baseFileName + "_art", cfr.getART());
			} else {
				// If control flow reconstruction finished normally and other analyses are configured, start them now 

				// Simplify CFA
				logger.info("=== Simplifying CFA ===");
				DeadCodeElimination dce;
				long totalRemoved = 0;
				runAlgorithm(new ExpressionSubstitution(program));
				do {
					dce = new DeadCodeElimination(program); 
					runAlgorithm(dce);
					totalRemoved += dce.getRemovalCount();
				} while (dce.getRemovalCount() > 0);
				logger.info("=== Finished CFA simplification, removed " + totalRemoved + " edges. ===");

				AnalysisManager mgr = AnalysisManager.getInstance();				
				List<ConfigurableProgramAnalysis> secondaryCPAs = new LinkedList<ConfigurableProgramAnalysis>();
				for (int i=0; i<Options.secondaryCPAs.getValue().length(); i++) {			
					ConfigurableProgramAnalysis cpa = mgr.createAnalysis(Options.secondaryCPAs.getValue().charAt(i));
					if (cpa != null) {
						AnalysisProperties p = mgr.getProperties(cpa);
						logger.info("--- Using " + p.getName());
						secondaryCPAs.add(cpa);
					} else {
						logger.fatal("No analysis corresponds to letter \"" + Options.secondaryCPAs.getValue().charAt(i) + "\"!");
						System.exit(1);
					}
				}
				// Do custom analysis
				long customAnalysisStartTime = System.currentTimeMillis();
				CPAAlgorithm cpaAlg;
				ConfigurableProgramAnalysis[] cpaArray = secondaryCPAs.toArray(new ConfigurableProgramAnalysis[secondaryCPAs.size()]);
				if (Options.backward.getValue()) {
					cpaAlg = CPAAlgorithm.createBackwardAlgorithm(program, cpaArray);
				} else {
					cpaAlg = CPAAlgorithm.createForwardAlgorithm(program, cpaArray);
				}
				activeAlgorithm = cpaAlg;
				cpaAlg.run();
				long customAnalysisEndTime = System.currentTimeMillis();

				if (!Options.noGraphs.getValue())
					graphWriter.writeControlFlowAutomaton(baseFileName + "_cfa", cpaAlg.getReachedStates().select(1));

				logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);
				logger.error( "   Statistics for " + Options.secondaryCPAs.getValue());
				logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);
				logger.error( "   Runtime:                " + String.format("%8dms", (customAnalysisEndTime - customAnalysisStartTime)));
				logger.error( "   States:                   " + String.format("%8d", cpaAlg.getReachedStates().size()));
				logger.error(Characters.DOUBLE_LINE_FULL_WIDTH);


			}

			// If procedure abstraction is active, detect procedures now
			if (cfr.isCompleted() && Options.procedureAbstraction.getValue() == 2) {
				cfr = null;
				reached = null;
				ProcedureAnalysis procedureAnalysis = new ProcedureAnalysis();		
				CPAAlgorithm cpaAlg = CPAAlgorithm.createForwardAlgorithm(program, procedureAnalysis);
				runAlgorithm(cpaAlg);
				reached = cpaAlg.getReachedStates().select(1);
				Set<Location> procedures = procedureAnalysis.getCallees();

				SetMultimap<Location, Location> callGraph = HashMultimap.create();

				// Procedure analysis and thus this callgraph only works with --procedures 2
				// A broken callgraph does not affect the safety checks, though, as all
				// procedures are checked without any interprocedural abstraction anyway
				for (Pair<Location,Location> callSite : procedureAnalysis.getCallSites()) {
					ProcedureState procedureState = (ProcedureState)Lattices.joinAll(reached.where(callSite.getLeft()));
					for (Location procedure : procedureState.getProcedureEntries()) {
						callGraph.put(procedure, callSite.getRight()); 
					}
				}
				logger.info("Found " + procedures.size() + " function entry points from procedure analysis.");

				if (!Options.noGraphs.getValue())
					graphWriter.writeCallGraph(baseFileName + "_callgraph", callGraph);
			}

			 

			// Kills the keypress-monitor-thread.
			try {
				Runtime.getRuntime().removeShutdownHook(shutdownThread);
				System.exit(0);
			} catch (IllegalStateException e) {
				// Happens when shutdown has already been initiated by Ctrl-C or Return
			}
		} catch (Throwable e) {
			System.out.flush();
			e.printStackTrace();
			Runtime.getRuntime().removeShutdownHook(shutdownThread);
			// Kills eclipse shutdown thread
			System.exit(1);
		}


	}


	private static void runAlgorithm(Algorithm a) {
		activeAlgorithm = a;
		a.run();
		activeAlgorithm = null;
	}

	@SuppressWarnings("unused")
	private static final void appendToFile(String filename, String text) {
		try {
			FileWriter statsFile = new FileWriter(filename, true);
			statsFile.append(text);
			statsFile.close();
		} catch (Exception e) {
			logger.error("Cannot write to outputfile!", e);
		}
	}
	
	private static String getBaseFileName(File file) {
		String baseFileName = file.getAbsolutePath();
		// Get name of the analyzed file without file extension if it has one
		if (file.getName().contains(".")) { 
			int dotIndex = file.getPath().lastIndexOf('.');
			if (dotIndex > 0) {
				baseFileName = file.getPath().substring(0, dotIndex);
			}
		}
		return baseFileName;
	}

}
