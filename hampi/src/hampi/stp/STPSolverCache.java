package hampi.stp;

import hampi.constraints.*;
import hampi.utils.*;

import java.util.*;

/**
 * This cache stores various partial results. Hampi must not have any static
 * caches to avoid interference of solving sessions and prevent memory leaks.
 * Instead, this cache is kept during each solving session and discarded when
 * not needed.
 */
public final class STPSolverCache{

  private final Map<List<STPExpr>, STPExpr> cachedAnd = new LinkedHashMap<List<STPExpr>, STPExpr>();

  private final Map<Integer, STPExpr> cachedExpr = new LinkedHashMap<Integer, STPExpr>();

  private final Map<List<STPExpr>, STPExpr> cachedOr = new LinkedHashMap<List<STPExpr>, STPExpr>();

  /**
   * Cache for stp expressions. Cache is a map: valLev, regexp -> startIdx,
   * stpexp. Retrieved stp expressions need to be 'shifted', i.e., each
   * bitvector extraction expression gets shifted by the same number of bits.
   */
  private final DoubleKeyMap<Integer, Regexp, Pair<Integer, STPExpr>> concatCache = new DoubleKeyMap<Integer, Regexp, Pair<Integer, STPExpr>>();

  public Pair<Integer, STPExpr> getConcat(int varLen, ConcatRegexp regexp){
    return concatCache.get(varLen, regexp);
  }

  public void putConcat(int varLen, ConcatRegexp regexp, Pair<Integer, STPExpr> create){
    concatCache.put(varLen, regexp, create);
  }

  public STPExpr getOr(List<STPExpr> expressions){
    return cachedOr.get(expressions);
  }

  public void putOr(List<STPExpr> expressions, STPExpr e){
    cachedOr.put(expressions, e);
  }

  public STPExpr getAnd(List<STPExpr> expressions){
    return cachedAnd.get(expressions);
  }

  public void putAnd(List<STPExpr> expressions, AndExpr e){
    cachedAnd.put(expressions, e);
  }

  public STPExpr getConst(int val){
    return cachedExpr.get(val);
  }

  public void putConst(int val, ConstExpr e){
    cachedExpr.put(val, e);
  }
}
