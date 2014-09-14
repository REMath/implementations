package cc.sven.intset

import cc.sven.bdd._
import cc.sven.bounded._
import scala.collection.SetLike
import scala.collection.IterableLike
import scala.collection.JavaConverters._
import cc.sven.bounded.BoundedBits
import cc.sven.bounded.Bounded
import cc.sven.integral.Implicits._
import cc.sven.interval._



class IntSet[T](val cbdd: CBDD)(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]) extends Set[T] with SetLike[T, IntSet[T]] {
  //enumeration
  //interval
  //strided ival
  /*todo:
   * equals, canEqual
   * diff (--)
   */
  override def equals(other : Any) = other match {
    case otherSet : IntSet[T] => cbdd == otherSet.cbdd
    case _ => super.equals(other)
  }
  override def hashCode() = cbdd.hashCode()
  def unary_! = new IntSet[T](!cbdd)
  def invert = !this
  def ite(t: IntSet[T], e: IntSet[T]) = new IntSet[T](cbdd.ite(t.cbdd, e.cbdd))
  def +(elem: T): IntSet[T] = new IntSet[T](cbdd || IntSet.apply[T](elem)(int, bounded, boundedBits).cbdd)
  def add(elem: T) = this + elem
  def -(elem: T): IntSet[T] = new IntSet[T](cbdd && !IntSet.apply[T](elem)(int, bounded, boundedBits).cbdd)
  def remove(elem: T) = this - elem
  def contains(elem: T): Boolean = cbdd.partialEval(IntSet.toBitVector(elem)) match {
    case Some(True)  => true
    case _ => false
  }
  def iterator() = new IntSetIterator(this)
  override def empty = new IntSet(False)
  def intersect(that: IntSet[T]): IntSet[T] = new IntSet(cbdd && that.cbdd)
  def &(that: IntSet[T]): IntSet[T] = this intersect that
  def union(that: IntSet[T]): IntSet[T] = new IntSet(cbdd || that.cbdd)
  def |(that: IntSet[T]): IntSet[T] = this union that
  def max = cbdd match {
    case False            => throw new UnsupportedOperationException
    case True             => IntSet.fromBitVector(List(false).padTo(boundedBits.bits - 1, true))(int, bounded, boundedBits)
    //set cannot be false because of canonical bdd, threfore set.trueMost != None
    case Node(set, False) => IntSet.fromBitVector(true :: set.trueMost.get.padTo(boundedBits.bits - 1, true))(int, bounded, boundedBits)
    case Node(_, uset)    => IntSet.fromBitVector(false :: uset.trueMost.get.padTo(boundedBits.bits - 1, true))(int, bounded, boundedBits)
  }
  def min = cbdd match {
    case False             => throw new UnsupportedOperationException
    case True              => IntSet.fromBitVector(List(true).padTo(boundedBits.bits - 1, false))(int, bounded, boundedBits)
    case Node(False, uset) => IntSet.fromBitVector(false :: uset.falseMost.get.padTo(boundedBits.bits - 1, false))(int, bounded, boundedBits)
    case Node(set, _)      => IntSet.fromBitVector(true :: set.falseMost.get.padTo(boundedBits.bits - 1, false))(int, bounded, boundedBits)
  }
  def sizeBigInt: BigInt = {
    import scala.math.BigInt._
    cbdd.truePaths.map((x) => 2 pow (boundedBits.bits - x.length)).sum
  }
  override def size : Int = {
    val bint = sizeBigInt
    if(bint > Integer.MAX_VALUE) throw new IllegalArgumentException("size does not fit into an Int")
    bint.intValue
  }
  def sizeGreaterThan(value : BigInt) : Boolean = {
    import scala.math.BigInt.int2bigInt
    var size : BigInt = 0
    for(p <- cbdd.truePaths) {
      size += 2 pow (boundedBits.bits - p.length)
      if(size > value) return true
    }
    return false
  }
  def sizeGreaterThan(value : Int) : Boolean = sizeGreaterThan(value : BigInt)
  def randomElement() = {
    val path = this.cbdd.randomTruePath()
    val path_ = path ++ List.fill(boundedBits.bits - path.length)(scala.util.Random.nextBoolean())
    IntSet.fromBitVector(path_)(int, bounded, boundedBits)
  }
  def subsetOf(that: IntSet[T]): Boolean = this.cbdd doesImply that.cbdd
  override def isEmpty: Boolean = this.cbdd match { case False => true; case _ => false }
  override def nonEmpty: Boolean = !this.isEmpty //perhaps not needed - see implementation
  def isFull: Boolean = this.cbdd match { case True => true; case _ => false }
  /* XXX todo
   * cartesian product operation (+, -, bitwise, mult, div)
   * idea for optimization:
   *   since with msb->lsb ordering, the bdd is essentially a set of intervals where the set is held small
   *   by precise ivals, we could find more precise intervals by "communicating" breadth first search.
   *   Communicating, because we could say: recurse up to $n$ times.
   *   this could be implemented as a widening operator
   */
  def plus(that: IntSet[T]): IntSet[T] = {
    val res = CBDD.plus(this.cbdd, that.cbdd, boundedBits.bits)
    new IntSet(res._1 || res._2)
  }
  def plusWithCarry(that: IntSet[T]): (IntSet[T], IntSet[T]) = {
    val res = CBDD.plus(this.cbdd, that.cbdd, boundedBits.bits)
    (new IntSet(res._1), new IntSet(res._2))
  }
  def negate = new IntSet[T](CBDD.negate(boundedBits.bits, cbdd))
  def unary_- = this.negate
  /*def bAndRef(that: IntSet[T]): IntSet[T] = bitwiseOp(_ && _)(that.cbdd))
  def bOrRef(that: IntSet[T]): IntSet[T] = bitwiseOp(_ || _)(that.cbdd))
  def bXOrRef(that: IntSet[T]): IntSet[T] = bitwiseOp(_ != _)(that.cbdd))*/
  def bitwiseOp(op : (Boolean, Boolean) => Boolean)(that : IntSet[T]) : IntSet[T] = new IntSet(CBDD.bitwiseOp(op)(this.cbdd, that.cbdd))
  def bAnd(that : IntSet[T]) : IntSet[T] = new IntSet(CBDD.bAnd(cbdd, that.cbdd))
  def bOr(that : IntSet[T]) : IntSet[T] = new IntSet(CBDD.bOr(cbdd, that.cbdd))
  def bXOr(that : IntSet[T]) : IntSet[T] = new IntSet(CBDD.bXOr(cbdd, that.cbdd))
  def bNot: IntSet[T] = new IntSet(CBDD.bNot(cbdd))
  def lessThan(that : IntSet[T]) : IntSet[T] = intersect(IntSet(FilledIval(bounded.minBound, that.max)))
  def greaterThan(that : IntSet[T]) : IntSet[T] = intersect(IntSet(FilledIval(that.min, bounded.maxBound)))
  def java = this.asJava
}

class IntSetIterator[T](iset: IntSet[T])(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]) extends Iterator[T] {
  val iter = new CBDDIterator(iset.cbdd, boundedBits.bits)
  def hasNext() = iter.hasNext()
  def next() = IntSet.fromBitVector(iter.next())(int, bounded, boundedBits)
}

object IntSet {
  def toBitVector[T](i: T)(implicit int: Integral[T], boundedBits: BoundedBits[T]): List[Boolean] = {
    import int.{ mkNumericOps, mkOrderingOps }
    val extendSign = i < int.zero
      def helper(rest: T, bitvector: List[Boolean], c: Int, carry: Boolean): List[Boolean] = {
        if (rest equiv int.zero) List.fill(c)(extendSign) ++ bitvector else {
          //half adder for the +1 in two's complement
          val bit = ((rest % int.fromInt(2) != int.zero) != extendSign)
          val bitWithCarry = bit != carry
          val nextCarry = bit && carry
          helper(rest / int.fromInt(2), bitWithCarry :: bitvector, c - 1, nextCarry)
        }
      }
    helper(i, List.empty, boundedBits.bits, extendSign)
  }
  def fromBitVector[T](bs: List[Boolean])(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): T = {
    import int.{ mkNumericOps, mkOrderingOps }
    val bslen = bs.length
    require(bslen <= boundedBits.bits)
    val isNegative = bounded.minBound < int.zero && (bs match {
      case Nil       => false
      case sbit :: _ => sbit
    })
    val zipped = bs.zip(List.iterate(int.one, bslen)(_ * int.fromInt(2)).reverse)
    val positive = (int.zero /: zipped)((acc: T, tuple: (Boolean, T)) => if (tuple._1 != isNegative) acc + tuple._2 else acc)
    if (isNegative) -(positive + int.one) else positive
  }
  /* The following 3 apply methods are there for java interop.
   * one T* method would generate code that is not very useful in java
   * but we want at least apply(1) and apply() for java
   */
  def apply[T]()(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = IntSet(Set[T]())
  def apply[T](i1: T, i2: T, is: T*)(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = (IntSet(Set[T]()) /: (i1 :: i2 :: is.toList)) {
    (acc, i) => acc | IntSet(Set(i))
  }
  def apply[T](i: T)(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = new IntSet(CBDD(toBitVector(i)(int, boundedBits)))
  def apply[T](s: Set[T])(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = new IntSet(((False: CBDD) /: s) {
    (bdd, i) =>
      val ibdd = CBDD(toBitVector(i)(int, boundedBits))
      bdd || ibdd
  })
  def apply[T](s: java.util.Set[T])(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = apply(s.asScala.toSet)
  def apply[T](ival: Interval[T])(implicit int: Integral[T], bounded: Bounded[T], boundedBits: BoundedBits[T]): IntSet[T] = {
    import int.{ mkNumericOps, mkOrderingOps }
    def smallerBV(fullLenBV: List[Boolean]) = CBDD(fullLenBV, False, True, True)
    def greaterBV(fullLenBV: List[Boolean]) = CBDD(fullLenBV, True, False, True)
    ival match {
      case EmptyIval => IntSet(Set[T]())
      case FilledIval(lo, hi) if (lo < int.zero) => {
        val greaterSet = if(hi >= int.zero) apply(FilledIval(int.zero, hi)) else IntSet[T]()
        val smallerSet = new IntSet(greaterBV(toBitVector(lo)) && smallerBV(toBitVector(int.min(-int.one, hi))))(int, bounded, boundedBits)
        greaterSet union smallerSet
      }
      case FilledIval(lo, hi) => new IntSet(smallerBV(toBitVector(hi)) && greaterBV(toBitVector(lo)))
    }
  }
  def apply[T <: FiniteOrderedIntegral[T]](ele: T): IntSet[T] = IntSet(Set[T](ele))(ele, ele, ele)
  /*def apply(i : Integer) : IntSet[Integer] = {
    val int = implicitly[Integral[Integer]]
    val bounded = implicitly[Bounded[Integer]]
    val boundedBits = implicitly[BoundedBits[Integer]]
    apply(i)(int, bounded, boundedBits)
  }*/
}