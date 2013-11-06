package hampi.utils;

import java.util.*;

/**
 * Implements exhaustively allocating (distributing) pigeons to holes.
 */
public class PigeonHoleDistributor{

  /**
   * Returns all distributions of pigeons to holes.
   */
  public Set<List<Integer>> distribute(int holes, int pigeons, boolean allowEmpty){
    return distribute(holes, pigeons, allowEmpty, new DoubleKeyMap<Pair<Integer, Integer>, Boolean, Set<List<Integer>>>());
  }

  private Set<List<Integer>> distribute(int holes, int pigeons, boolean allowEmpty, DoubleKeyMap<Pair<Integer, Integer>, Boolean, Set<List<Integer>>> cache){
    if (holes <= 0 || pigeons < 0)
      throw new IllegalArgumentException("invalid arguments " + holes + " " + pigeons);
    //    System.out.println("distribute " + holes + " " + pigeons + " " + allowEmpty);
    Pair<Integer, Integer> pair = Pair.create(holes, pigeons);
    if (cache.containsKeys(pair, allowEmpty))
      return cache.get(pair, allowEmpty);
    if (!allowEmpty && pigeons < holes){//not enough pigeons
      Set<List<Integer>> result = Collections.emptySet();
      cache.put(pair, allowEmpty, result);
      return result;
    }
    if (holes == 1){
      Set<List<Integer>> result = singleHoleDistro(pigeons);
      cache.put(pair, allowEmpty, result);
      return result;
    }
    Set<List<Integer>> result = new LinkedHashSet<List<Integer>>();

    //allocate first hole, recurse
    int low = allowEmpty ? 0 : 1;
    int high = allowEmpty ? pigeons : pigeons - holes + 1;
    for (int i = low; i <= high; i++){
      Set<List<Integer>> subDistr = distribute(holes - 1, pigeons - i, allowEmpty, cache);
      for (List<Integer> subList : subDistr){
        List<Integer> newList = new ArrayList<Integer>();
        newList.add(i);
        newList.addAll(subList);
        result.add(newList);
      }
    }
    cache.put(pair, allowEmpty, result);
    return result;
  }

  private static final Boolean CACHE = true;

  //up to this limit we will eagerly compute all permutations.
  private static final int HEURISTIC_PERMUTATION_LIMIT = 8;

  private final Map<Object, Set<List<Integer>>> cachedDistros = new LinkedHashMap<Object, Set<List<Integer>>>();
  private final Map<Integer, List<List<Integer>>> cachedPermutations = new LinkedHashMap<Integer, List<List<Integer>>>();

  public Set<List<Integer>> distribute2(int holes, int pigeons, List<Integer> lowerBounds, List<Integer> origUpperBounds){
    if (holes == 0)
      return Collections.emptySet();
    if (holes < 0 || pigeons < 0 || lowerBounds.size() != holes || origUpperBounds.size() != holes)
      throw new IllegalArgumentException("invalid arguments " + holes + " " + pigeons + " " + lowerBounds + " " + origUpperBounds);

    int lowerSum = sum(lowerBounds);

    //nothing will be higher than the # of pigeons so we can adjust
    List<Integer> upperBounds = new ArrayList<Integer>(origUpperBounds.size());
    for (int i = 0; i<origUpperBounds.size() ; i++) {
      int up = origUpperBounds.get(i);
      int min = Math.min(up, pigeons);//can't put more than we have pigeons
      min = Math.min(min, pigeons - (lowerSum - lowerBounds.get(i)));//can't have more than this many or it'll overflow
      upperBounds.add(min);
    }

    List<Object> cacheKey;
    if (CACHE){
      cacheKey = Arrays.asList(holes, pigeons, lowerBounds, upperBounds);
      Set<List<Integer>> cached = cachedDistros.get(cacheKey);
      if (cached != null)
        return cached;
    }else{
      cacheKey= null;
    }
    //    System.out.println("distro holes:" + holes + " pigeons:" + pigeons + " low:" + lowerBounds + " upp:" + upperBounds);

    int minLower = Collections.min(lowerBounds);
    if (minLower > 0 && pigeons < holes){
      Set<List<Integer>> res = Collections.emptySet();//too few pigeons
      if (CACHE){
        cachedDistros.put(cacheKey, res);
      }
      return res;
    }
    if (pigeons < lowerSum){
      Set<List<Integer>> res = Collections.emptySet();//too few pigeons
      if (CACHE){
        cachedDistros.put(cacheKey, res);
      }
      return res;
    }
    int upperSum = sum(upperBounds);
    if (pigeons > upperSum){
      Set<List<Integer>> res = Collections.emptySet();//too many pigeons
      if (CACHE){
        cachedDistros.put(cacheKey, res);
      }
      return res;
    }

    //base case
    if (holes == 1){
      Set<List<Integer>> res = singleHoleDistro(pigeons);
      if (CACHE){
        cachedDistros.put(cacheKey, res);
      }
      return res;
    }
    //all lower and upper bounds are the same, so there'is just 1 distribution
    if (lowerSum == pigeons || lowerBounds.equals(upperBounds)){
      Set<List<Integer>> res = Collections.singleton(lowerBounds);
      if (CACHE){
        cachedDistros.put(cacheKey, res);
      }
      return res;
    }

    //    System.out.println("distribute holes:" + holes + " pigeons:" + pigeons + " " + lowerBounds + " " + upperBounds);

    /* All lows are the same and all uppers are the same
       So the problem is fully symmetrical.
       We compute distro for 1 choice for the first position --- all others are permutations.
       But we only do it for small size lists because it requires computing all permutations
       and we currently compute them eagerly.
    */
    if (lowerBounds.size() <= HEURISTIC_PERMUTATION_LIMIT){
      int maxLower = Collections.max(lowerBounds);
      int maxUpper = Collections.max(upperBounds);
      int minUpper = Collections.min(upperBounds);
      if (minLower == maxLower && minUpper == maxUpper){
        Set<List<Integer>> result = new LinkedHashSet<List<Integer>>();
        int low = lowerBounds.get(0);
        int high = Math.min(pigeons, upperBounds.get(0));
        List<Integer> subListLowers = lowerBounds.subList(1, lowerBounds.size());
        List<Integer> subListUppers = upperBounds.subList(1, upperBounds.size());
        firstHoleAllocation: for (int i = low; i <= high; i++){
          //we skip skip any i that is already present in any result
          for (List<Integer> is : result){
            if (is.contains(i)){
              continue firstHoleAllocation;
            }
          }

          int minLowerSubList = Collections.min(subListLowers);
          int subPigeons = pigeons - i;
          if (minLowerSubList > 0 && subPigeons < holes - 1){
            Set<List<Integer>> res = Collections.emptySet();//too few pigeons for the remaining holes
            if (CACHE){
              cachedDistros.put(cacheKey, res);
            }
            return res;
          }
          if (subPigeons < lowerSum - lowerBounds.get(0)){
            Set<List<Integer>> res = Collections.emptySet();//too few pigeons for the remaining holes
            if (CACHE){
              cachedDistros.put(cacheKey, res);
            }
            return res;
          }

          Set<List<Integer>> subDistr = distribute2(holes - 1, subPigeons, subListLowers, subListUppers);
          for (List<Integer> subList : subDistr){
            List<Integer> newList = new ArrayList<Integer>(1 + subList.size());
            newList.add(i);
            newList.addAll(subList);
            result.add(newList);
          }
        }

      result = permuteAll(result);
      if (CACHE){
        cachedDistros.put(cacheKey, result);
      }
      return result;
    }
    }

    Set<List<Integer>> result = new LinkedHashSet<List<Integer>>();

    //allocate first hole, recurse
    int low = lowerBounds.get(0);
    int high = Math.min(pigeons, upperBounds.get(0));
    if (low > high)
      throw new IllegalStateException("invalid bounds");
    List<Integer> subListLowers = lowerBounds.subList(1, lowerBounds.size());
    List<Integer> subListUppers = upperBounds.subList(1, upperBounds.size());
    for (int i = low; i <= high; i++){
      int minLowerSubList = Collections.min(subListLowers);
      int subPigeons = pigeons - i;
      if (minLowerSubList > 0 && subPigeons < holes - 1){
        break;//too few pigeons for the remaining holes
      }
      if (subPigeons < lowerSum - lowerBounds.get(0)){
        break;//too few pigeons for the remaining holes
      }

      Set<List<Integer>> subDistr = distribute2(holes - 1, subPigeons, subListLowers, subListUppers);
      for (List<Integer> subList : subDistr){
        List<Integer> newList = new ArrayList<Integer>(1 + subList.size());
        newList.add(i);
        newList.addAll(subList);
        result.add(newList);
      }
    }
    if (CACHE){
      cachedDistros.put(cacheKey, result);
    }
    return result;
  }

  /**
   * Returns a set in which, for every list, all permutations have been added.
   */
  private Set<List<Integer>> permuteAll(Set<List<Integer>> lists){
    //first sort each list to remove dups
    Set<List<Integer>> sortedLists = new LinkedHashSet<List<Integer>>();
    for (List<Integer> list : lists){
      List<Integer> copy = new ArrayList<Integer>(list);
      Collections.sort(copy);
      sortedLists.add(copy);
    }

    //then take each sorted list and apply all permutations
    Set<List<Integer>> result = new LinkedHashSet<List<Integer>>();
    for (List<Integer> list : sortedLists){
      result.addAll(applyAllPermutations(list));
    }
    return result;
  }

  private List<List<Integer>> applyAllPermutations(List<Integer> list){
    List<List<Integer>> allPermuted = new ArrayList<List<Integer>>(factorial(list.size()));
    List<List<Integer>> permutations = getPermutations(list.size());
    for (List<Integer> perm : permutations){
      allPermuted.add(applyPermutation(list, perm));
    }
    return allPermuted;
  }

  /**
   * Applies the given permutation. A permutation is a list of indices, so we
   * just construct a new list and set elements.
   */
  private List<Integer> applyPermutation(List<Integer> list, List<Integer> perm){
    assert list.size() == perm.size();
    Integer[] newElements = new Integer[list.size()];
    //take all elements and set them to indices given by perm
    for (int i = 0; i < list.size(); i++){
      Integer elem = list.get(i);
      Integer permutedIndex = perm.get(i);
      newElements[permutedIndex] = elem;
    }
    return Arrays.asList(newElements);
  }

  /**
   * Returns all permutations of a given size.
   */
  private List<List<Integer>> getPermutations(int size){
    if (CACHE){
      List<List<Integer>> cached = cachedPermutations.get(size);
      if (cached != null)
        return cached;
    }
    List<List<Integer>> result = new ArrayList<List<Integer>>(factorial(size));
    if (size == 1){
      result = Collections.singletonList(Arrays.asList(0));//identity permutation
      if (CACHE){
        cachedPermutations.put(size, result);
      }
      return result;
    }
    List<List<Integer>> subPerms = getPermutations(size - 1);
    for (List<Integer> subPerm : subPerms){
      //add the new number in all positions
      int numToInsert = size - 1;
      for (int insert = 0; insert <= subPerm.size(); insert++){
        List<Integer> copy = new ArrayList<Integer>(subPerm);
        copy.add(insert, numToInsert);
        result.add(copy);
      }
    }

    if (CACHE){
      cachedPermutations.put(size, result);
    }
    return result;
  }

  private int factorial(int n){
    int f = 1;
    for (int i = 1; i <= n; i++){
      f *= i;
    }
    return f;
  }

  private static Set<List<Integer>> singleHoleDistro(int pigeons){
    List<Integer> l = new ArrayList<Integer>(1);//do not use Collections.singletonList because we want to keep this writable
    l.add(pigeons);
    return Collections.singleton(l);
  }

  private static int sum(List<Integer> ints){
    int sum = 0;
    for (int i : ints){
      if (i == Integer.MAX_VALUE)
        return i;
      sum += i;
    }
    return sum;
  }


}
