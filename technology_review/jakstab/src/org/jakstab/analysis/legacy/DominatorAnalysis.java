/*
 * DominatorAnalysis.java - This file is part of the Jakstab project.
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

package org.jakstab.analysis.legacy;

//import org.jakstab.util.FastSet;
//import org.jakstab.util.Logger;

//import java.util.*;

/**
 * Implementation of the Lengauer and Tarjan algorithm for calculating
 * dominators.
 * 
 * Original code taken from familyJ.
 * Copyright (C) 1990-2001 DMS Decision Management Systems Ges.m.b.H.
 * 
 * @author Johannes Kinder
 */
public class DominatorAnalysis {
//	
//	public static Map<BasicBlock, BasicBlock> getIDom(Set<BasicBlock> basicBlocks, BasicBlock start) {
//		Map<BasicBlock, BasicBlock> idomRel = new HashMap<BasicBlock, BasicBlock>();
//		DominatorAnalysis analysis = new DominatorAnalysis(basicBlocks, start, false);
//		analysis.run();
//		for (int i=0; i<analysis.nodes.length; i++) {
//			idomRel.put(analysis.nodes[i], analysis.nodes[analysis.idom[i]]);
//		}
//		return idomRel;
//	}
//
//	public static Map<BasicBlock, BasicBlock> getIPdom(Set<BasicBlock> basicBlocks, BasicBlock end) {
//		Map<BasicBlock, BasicBlock> ipdomRel = new HashMap<BasicBlock, BasicBlock>();
//		DominatorAnalysis analysis = new DominatorAnalysis(basicBlocks, end, true);
//		analysis.run();
//		for (int i=0; i<analysis.nodes.length; i++) {
//			ipdomRel.put(analysis.nodes[i], analysis.nodes[analysis.idom[i]]);
//		}
//		return ipdomRel;
//	}
//
//
//
//	private static final Logger logger = Logger.getLogger(DominatorAnalysis.class);
//
//	private BasicBlock[] nodes;
//	private BasicBlock start;
//	private final boolean reversed;
//
//	private int[] label;
//	private int[] parent;
//	private int[] ancestor;
//	private int[] child;
//	private int[] ndfs;
//	private int[] sdno;
//	private int[] size;
//	private int n0;
//	private int n;
//
//	private Set<Integer>[] bucket;
//
//	private int[] idom;
//	private Set<Integer>[] domFront;
//
//
//	public DominatorAnalysis(Set<BasicBlock> basicBlocks, BasicBlock root, boolean reversed) {
//		this.reversed = reversed;
//		nodes = new BasicBlock[basicBlocks.size()];
//		int j = 0;
//		for (BasicBlock bb : basicBlocks) {
//			bb.setTmpIndex(j);
//			nodes[j++] = bb;
//		}
//		this.start = root;
//	}
//	
//	private Set<BasicBlock> pred(BasicBlock bb) {
//		return reversed ? bb.getSuccessors() : bb.getPredecessors();
//	}
//
//	private Set<BasicBlock> succ(BasicBlock bb) {
//		return reversed ? bb.getPredecessors() : bb.getSuccessors();
//	}
//
//	@SuppressWarnings("unchecked")
//	public void run() {
//		
//		logger.info("Starting dominator analysis...");
//		long startTime = System.currentTimeMillis();
//
//		n0 = nodes.length;
//		label = new int[n0 + 1];
//		parent = new int[n0 + 1];
//		ancestor = new int[n0 + 1];
//		child = new int[n0 + 1];
//		ndfs = new int[n0 + 1];
//		sdno = new int[n0 + 1];
//		size = new int[n0 + 1];
//		bucket = new Set[n0 + 1];
//		idom = new int[n0 + 1];
//		for (int i = 0; i < n0 + 1; ++i) {
//			bucket[i] = new HashSet<Integer>();
//		}
//		ancestor[n0] = n0;
//		label[n0] = n0;
//		n = 0;
//
//		// Initialize data structures by a DFS 
//		Deque<Integer> stack = new LinkedList<Integer>();
//		stack.push(start.getTmpIndex());
//		while (!stack.isEmpty()) {
//			int node = stack.pop();
//			if (sdno[node] != 0) continue;
//			
//			sdno[node] = ++n;
//			ndfs[n] = node;
//			label[node] = node;
//			ancestor[node] = n0;
//			child[node] = n0;
//			size[node] = 1;
//			for (BasicBlock succ : succ(nodes[node])) {
//				int w = succ.getTmpIndex();
//				if (sdno[w] == 0) {
//					parent[w] = node;
//					stack.push(w);
//				}
//			}
//		}
//
//		for (int i = n; i >= 1; --i) {
//			//compute initial values for semidominators and store
//			//nodes with the same semidominator in the same bucket
//			int w = ndfs[i];
//			for (BasicBlock pred : pred(nodes[w])) {
//				int v = pred.getTmpIndex();
//				int u = eval(v);
//				if (sdno[u] < sdno[w]) {
//					sdno[w] = sdno[u];
//				}
//			}
//			bucket[ndfs[sdno[w]]].add(w);
//			link(parent[w],w);
//			// compute immediate dominators for nodes in the bucket
//			// of w's parent
//			Iterator<Integer> itBucket = bucket[parent[w]].iterator();
//			while (itBucket.hasNext()) {
//				int v = itBucket.next().intValue();
//				itBucket.remove();
//				int u = eval(v);
//				if (sdno[u] < sdno[v]) {
//					idom[v] = u;
//				} else {
//					idom[v] = parent[w];
//				}
//			}
//		}
//		// adjust immediate dominators of nodes whose current version is
//		// the immediate dominator differs from the node with the
//		// depth-first number of the node's semidominator
//		for (int  i = 1; i <= n; ++i) {
//			int w = ndfs[i];
//			if (idom[w] != ndfs[sdno[w]]) {
//				idom[w] = idom[idom[w]];
//			}
//		}
//
//		// Free temporary arrays
//		label = null;
//		parent = null;
//		ancestor = null;
//		child = null;
//		ndfs = null;
//		sdno = null;
//		size = null;
//		bucket = null;
//
//		// compute the dominance frontier
//		computeDomimanceFrontier();
//		
//		long endTime = System.currentTimeMillis();
//		logger.info("Finished after " + (endTime - startTime) + "ms.");
//		
//		/*
//		for (int i = 0; i < nodes.length; i++) {
//			logger.info(nodes[i].getIndex() + " is immediately " + (reversed ? "post" : "") + "dominated by " + 
//					(idom[i] >= 0 ? nodes[idom[i]].getIndex() : "nothing") + ".");
//			StringBuilder df = new StringBuilder();
//			df.append("[");
//			for (Integer el : domFront[i])
//				df.append(nodes[el].getIndex() + ",");
//			df.append("]");
//			logger.info("Dominance frontier of " + nodes[i].getIndex() + ": " + df.toString());
//		}
//		*/
//
//	}
//	
//	/**
//	 * Compute the iterated dominance frontier of a flowgraph.
//	 *
//	 * @param nodes a set of nodes (Integer)
//	 * @return iterated dominance frontier of the given nodes
//	 */
//	public Set<BasicBlock> getDFPlus(Set<BasicBlock> nodeSet) {
//		boolean change = true;
//		Set<BasicBlock> dFP = getDFSet(nodeSet);
//		while (change) {
//			change = false;
//			Set<BasicBlock> tmp = new HashSet<BasicBlock>();
//			tmp.addAll(nodeSet);
//			tmp.addAll(dFP);
//			Set<BasicBlock> d = getDFSet(tmp);
//			if (!d.equals(dFP)) {
//				dFP = d;
//				change = true;
//			}
//		}
//		return dFP;
//	}
//
//	/**
//	 * Compute the dominance frontier of each node
//	 * 
//	 * cf. K. D. Cooper, T. J. Harvey, and K. Kennedy. A simple, fast 
//	 * dominance algorithm. In Software-Practice And Experience, 
//	 * pages 4:1�10. John Wiley and Sons, Ltd., 2001.
//	 */
//	@SuppressWarnings("unchecked")
//	private void computeDomimanceFrontier() {
//		domFront = new Set[nodes.length];
//		for (int i = 0; i < domFront.length; ++i) {
//			domFront[i] = new FastSet<Integer>();
//		}
//		
//		for (int i = 0; i < nodes.length; i++) {
//			if (nodes[i].getInDegree() > 1) {
//				for (BasicBlock pred : nodes[i].getPredecessors()) {
//					int runner = pred.getTmpIndex();
//					while (runner != idom[i]) {
//						domFront[runner].add(i);
//						runner = idom[runner];
//					}
//				}
//			}
//		}
//	}
//
//	/**
//	 * Compute the union of the dominance frontiers of a set of nodes. Used
//	 * for constructing the SSA form.
//	 *
//	 * @param nodes the set of nodes
//	 */
//	private Set<BasicBlock> getDFSet(Set<BasicBlock> nodeSet) {
//		Set<BasicBlock> d = new FastSet<BasicBlock>();
//		for (BasicBlock n : nodeSet)
//			for (Integer e : domFront[n.getTmpIndex()])
//				d.add(nodes[e]);
//		return d;
//	}
//
//	/**
//	 * determine the ancestor of v whose semidominator has the
//	 * minimal depth-first number
//	 *
//	 * @param v the node
//	 */
//	private int eval(int v) {
//		if (ancestor[v] == n0) {
//			return label[v];
//		} else {
//			compress(v);
//			if (sdno[label[ancestor[v]]] >= sdno[label[v]]) {
//				return label[v];
//			} else {
//				return label[ancestor[v]];
//			}
//		}
//	}
//
//	/**
//	 * Compress ancestor path to node v to the node whose lable has
//	 * the maximal semidominator number
//	 *
//	 * @param v the node
//	 */
//	private void compress(int v) {
//		if (ancestor[ancestor[v]] != n0) {
//			compress(ancestor[v]);
//			if (sdno[label[ancestor[v]]] < sdno[label[v]]) {
//				label[v] = label[ancestor[v]];
//			}
//			ancestor[v] = ancestor[ancestor[v]];
//		}
//	}
//
//	/**
//	 * Rebalance the forest to trees maintained by the child and ancestor
//	 * data structures
//	 */
//	private void link(int v, int w) {
//		int s = w;
//		while (sdno[label[w]] < sdno[label[child[s]]]) {
//			if ((size[s] + size[child[child[s]]]) >= 2 * size[child[s]]) {
//				ancestor[child[s]] = s;
//				child[s] = child[child[s]];
//			} else {
//				size[child[s]] = size[s];
//				s = ancestor[s] = child[s];
//			}
//		}
//		label[s] = label[w];
//		size[v] += size[w];
//		if (size[v] < 2 * size[w]) {
//			int tmp = s;
//			s = child[v];
//			child[v] = tmp;
//		}
//		while (s != n0) {
//			ancestor[s] = v;
//			s = child[s];
//		}
//	}
//
}