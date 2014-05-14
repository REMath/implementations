/*
 * BoundedAddressTracking.java - This file is part of the Jakstab project.
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

package org.jakstab.analysis.explicit;

import java.util.*;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.x86.X86Instruction;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

import com.google.common.collect.*;

/**
 * @author Johannes Kinder
 */
public class BoundedAddressTracking implements ConfigurableProgramAnalysis {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(BoundedAddressTracking.class);

	public static void register(AnalysisProperties p) {
		p.setShortHand('x');
		p.setName("Bounded Address Tracking");
		p.setDescription("Enumerate region-based addresses up to a bound per variable per location.");
		p.setExplicit(true);
	}
	
	public static JOption<Integer> varThreshold = JOption.create("explicit-threshold", "k", 5, "Set the maximum number of values tracked per variable per location.");
	public static JOption<Integer> heapThreshold = JOption.create("heap-threshold", "k", 5, "Explicit threshold for data stored on the heap.");
	public static JOption<Boolean> repPrecBoost = JOption.create("rep-prec-boost", "Increase precision for rep-prefixed instructions.");
	public static JOption<Boolean> keepDeadStack = JOption.create("keep-dead-stack", "Do not discard stack contents below current stack pointer.");
	
	public BoundedAddressTracking() {
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		// Reduces states, but makes it harder to reconstruct the trace that lead to a certain state
		if (s2.lessOrEqual(s1)) return s1;
		return CPAOperators.mergeSep(s1, s2, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge, Precision precision) {
		return ((BasedNumberValuation)state).abstractPost((RTLStatement)cfaEdge.getTransformer(), precision);
	}
	
	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {
		return s;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		
		// This method uses the fact that there is only 1 precision per location
		
		ExplicitPrecision eprec = (ExplicitPrecision)precision;
		BasedNumberValuation widenedState = (BasedNumberValuation)s;

		// Only check value counts if we have at least enough states to reach it
		if (reached.size() > Math.min(varThreshold.getValue(), heapThreshold.getValue())) {
			
			boolean changed = false;

			// Check value counts for variables
			for (RTLVariable v : eprec.varMap.keySet()) {
				//BasedNumberElement currentValue = ((BasedNumberValuation)s).getValue(v);
				Set<BasedNumberElement> existingValues = eprec.varMap.get(v);
				int threshold = eprec.getThreshold(v);
				if (existingValues.size() > threshold) {
					// Lower precisions and widen the value in this state, too.
					// This avoids values accumulating at join points (where they are not
					// intercepted by the precision-aware setValue)
					if (countRegions(existingValues) > threshold) {
						eprec.stopTracking(v);
						if (!changed) {
							widenedState = new BasedNumberValuation(widenedState);
							changed = true;
						}
						widenedState.setValue(v, BasedNumberElement.getTop(v.getBitWidth()));
					} else {
						eprec.trackRegionOnly(v);
						if (!changed) {
							widenedState = new BasedNumberValuation(widenedState);
							changed = true;
						}
						logger.debug("Only tracking region of " + v + ", values were " + existingValues);
						widenedState.setValue(v, new BasedNumberElement(
								widenedState.getValue(v).getRegion(), 
								NumberElement.getTop(v.getBitWidth())));
					}
				}
			}

			
			// Check value counts for store
			PartitionedMemory<BasedNumberElement> sStore = ((BasedNumberValuation)s).getStore();
			for (EntryIterator<MemoryRegion, Long, BasedNumberElement> entryIt = sStore.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
				MemoryRegion region = entryIt.getLeftKey();
				Long offset = entryIt.getRightKey();
				BasedNumberElement value = entryIt.getValue();
				SetMultimap<Long, BasedNumberElement> memoryMap = eprec.regionMaps.get(region);
				if (memoryMap == null) continue;
				
				//BasedNumberElement currentValue = entry.getValue();
				Set<BasedNumberElement> existingValues = memoryMap.get(offset);

				int threshold = eprec.getStoreThreshold(region, offset);
				if (existingValues.size() > threshold) {
					if (countRegions(existingValues) > 5*threshold) {
						eprec.stopTracking(region, offset);
						if (!changed) {
							widenedState = new BasedNumberValuation(widenedState);
							changed = true;
						}
						widenedState.getStore().set(region, 
								offset, value.getBitWidth(), 
								BasedNumberElement.getTop(value.getBitWidth()));
					} else {
						eprec.trackRegionOnly(region, offset);
						if (!changed) {
							widenedState = new BasedNumberValuation(widenedState);
							changed = true;
						}
						widenedState.getStore().set(region, offset, value.getBitWidth(), 
								new BasedNumberElement(value.getRegion(), NumberElement.getTop(value.getBitWidth())));
					}
				}
			}
		}
		
		// Collect all values for all variables
		for (Map.Entry<RTLVariable, BasedNumberElement> entry : widenedState.getVariableValuation()) {
			eprec.varMap.put(entry.getKey(), entry.getValue());
		}

		// Collect all values for all memory areas
		PartitionedMemory<BasedNumberElement> store = widenedState.getStore();
		for (EntryIterator<MemoryRegion, Long, BasedNumberElement> entryIt = store.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
			SetMultimap<Long, BasedNumberElement> memoryMap = eprec.regionMaps.get(entryIt.getLeftKey());
			if (memoryMap == null) {
				memoryMap = HashMultimap.create();
				eprec.regionMaps.put(entryIt.getLeftKey(), memoryMap);
			}
			memoryMap.put(entryIt.getRightKey(), entryIt.getValue());
		}


		// If it was changed, widenedState is now a new state
		return Pair.create((AbstractState)widenedState, precision);
	}

	@Override
	public AbstractState initStartState(Location label) {
		return BasedNumberValuation.createInitialState();
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		ExplicitPrecision p = new ExplicitPrecision(varThreshold.getValue());
		
		// Increase precision of ecx, esi, edi for REP prefixed instructions
		Program program = Program.getProgram();
		if (BoundedAddressTracking.repPrecBoost.getValue()) {
			AbsoluteAddress addr = location.getAddress();
			X86Instruction instr = (X86Instruction)program.getInstruction(addr);
			if (instr != null && (instr.hasPrefixREPZ() || instr.hasPrefixREPNZ())) {
				logger.debug("boost-rep: REP instruction at " + location + ", increasing precision of loop registers.");
				p.setThreshold(ExpressionFactory.createVariable("%ecx"), 1000);
				p.setThreshold(ExpressionFactory.createVariable("%esi"), 1000);
				p.setThreshold(ExpressionFactory.createVariable("%edi"), 1000);
			}
		}
		
		return p;
	}
	
	private int countRegions(Set<BasedNumberElement> values) {
		Set<MemoryRegion> regions = new HashSet<MemoryRegion>();
		for (BasedNumberElement e : values)
			regions.add(e.getRegion());
		return regions.size();
	}

}
