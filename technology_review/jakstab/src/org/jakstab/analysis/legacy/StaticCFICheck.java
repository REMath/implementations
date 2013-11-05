package org.jakstab.analysis.legacy;

import org.jakstab.util.Logger;

public class StaticCFICheck {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(StaticCFICheck.class);

//	private static void checkCFI() {
//	logger.info("=======================");
//	logger.info("Starting CFI checks");
//	logger.info("=======================");
//
//	Program program = Program.getProgram();
//	ReachedSet reached;
//
//	// Add function symbols as procedure entry points
//	Collection<ExportedSymbol> procedures = program.getSymbols();
//	
//	logger.info("Got " + procedures.size() + " function entry points total using symbol information.");
//
//	Options.cpas = "x";
//	Options.procedureAbstraction = 0;
//	Options.failFast = true;
//	Set<ExportedSymbol> safeProcedures = new HashSet<ExportedSymbol>();
//	Set<ExportedSymbol> worklist = new HashSet<ExportedSymbol>(procedures);
//
//	int lastSafe = -1;
//
//	while (safeProcedures.size() > lastSafe && !stop) {		
//		lastSafe = safeProcedures.size();
//
//		for (ExportedSymbol procedure : worklist) {
//			//				if (safeProcedures.containsAll(callGraph.get(procedureEntry))) {
//			logger.info("Verifying procedure at " + procedure);
//			program.setEntryAddress(procedure.getAddress());
//			program.installHarness(new DefaultHarness());
//			ControlFlowReconstruction cfr = new ControlFlowReconstruction(program);
//
//			runAlgorithm(cfr);
//			if (stop) break;
//
//			if (cfr.isSound() && cfr.isCompleted()) {
//				logger.info("Procedure " + procedure + " is safe!");
//				safeProcedures.add(procedure);
//
//				reached = cfr.getReachedStates().select(1);
//				BasedNumberValuation initialState = (BasedNumberValuation)Lattices.joinAll(reached.where(new Location(new AbsoluteAddress(DefaultHarness.PROLOGUE_BASE))));
//				ReachedSet finalStates = reached.where(new Location(new AbsoluteAddress(DefaultHarness.EPILOGUE_BASE)));
//				if (finalStates.isEmpty()) {
//					logger.warn("Non-returning procedure: " + procedure);
//				} else {
//					BasedNumberValuation finalState = (BasedNumberValuation)Lattices.joinAll(finalStates); 
//					if (!finalState.isTop() && !initialState.isTop()) {
//						BasedNumberElement initialSP = initialState.getValue(program.getArchitecture().stackPointer());
//						BasedNumberElement finalSP = finalState.getValue(program.getArchitecture().stackPointer());
//						logger.warn("Initial ESP: " + initialSP + " and final ESP: " + finalSP);
//					}
//				}
//			} else {
//				logger.warn("Could not prove safety of procedure " + procedure + "!");
//			}
//			//				}
//		}
//		worklist.removeAll(safeProcedures);
//	}
//	
//	logger.warn("Safe procedures:");
//	for (ExportedSymbol proc : safeProcedures) {
//		logger.warn(proc);
//	}
//	
//	logger.warn(Characters.starredBox(safeProcedures.size() + " safe procedures of " + procedures.size()));
//	int stubs = 0;
//	int safeRealProcs = safeProcedures.size();
//	// Count import stubs and code from object files
//	for (ExportedSymbol proc : procedures) {
//		ExecutableImage module = proc.getModule();
//		// if the procedure head is not in the main module, it's not a real procedure
//		if (module != program.getMainModule() ||
//				// Check if it's just a trampoline in the PLT
//				(module instanceof ELFModule && ((ELFModule)module).isInPlt(proc.getAddress()))) {
//			stubs++;
//			if (safeProcedures.contains(proc)) {
//				safeRealProcs--;
//			} else {
//				logger.warn("Stub procedure " + proc + " is not safe?");
//			}
//		} 
//	}
//	logger.error("TotalP\tStubs\tRealP\tSafeRealProcs");
//	logger.error(procedures.size() + "\t" + stubs + "\t" + (procedures.size() - stubs) + "\t" + safeRealProcs);
//
//}
}
