package cc.sven.tlike

import scala.collection.SetLike
import cc.sven.bdd._
import cc.sven.intset._
import cc.sven.bounded._
import cc.sven.interval._
import scala.collection.JavaConverters._

class BitWidthException(widthA : Int, widthB : Int) extends Exception {
  override def toString = widthB.toString + " does not match required " + widthA.toString
}
/* a set for types that wrap ints with a fixed bit width - needs type with fixed bit width that is greater than included */
class IntLikeSet[I, T](val bits : Int, val set : IntSet[I])
                      (implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, Pair[Int, I]], castIT : Castable[Pair[Int, I], T])
                      extends Set[T] with SetLike[T, IntLikeSet[I, T]] {  
  import Implicits._
  private def checkBitWidth[A, B](a : A, b : B)(implicit ab : DynBoundedBits[A], bb : DynBoundedBits[B]) {
    if(ab.dBits(a) != bb.dBits(b)) throw new BitWidthException(ab.dBits(a), bb.dBits(b))
  }
  override def equals(other : Any) = other match {
    case otherIntLike : IntLikeSet[I, T] => bits == otherIntLike.bits && set == otherIntLike.set
    case _ => super.equals(other)
  }
  override def hashCode() = (bits, set).hashCode()
  override def toString = if(isFull) "Set(ANYVAL)" else if(sizeGreaterThan(1000)) "Set(" + this.min + ", MANYVAL, " + this.max + ")" else super.toString
  override def empty : IntLikeSet[I, T] = new IntLikeSet[I, T](bits, IntSet[I]()(int, bounded, boundedBits))
  def -(ele : T) = {
    checkBitWidth(this, ele)
    val eleI = castTI(ele)._2
    new IntLikeSet[I, T](bits, set - eleI)
  }
  def remove(ele : T) = this - ele
  def +(ele : T) = {
    checkBitWidth(this, ele)
    val eleI = castTI(ele)._2
    new IntLikeSet[I, T](bits, set + eleI)
  }
  def add(ele : T) = this + ele
  def contains(ele : T) = {
    checkBitWidth(this, ele)
    val eleI = castTI(ele)
    set contains eleI._2
  }
  def unary_! = fromBWCBDD(!getBWCBDD)
  def invert = !this
  def ite(t : IntLikeSet[I, T], e : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    checkBitWidth(this, t)
    checkBitWidth(t, e)
    new IntLikeSet(bits, set.ite(t.set, e.set))
  }
  def intersect(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    new IntLikeSet[I, T](bits, set intersect that.set)
  }
  def &(that : IntLikeSet[I, T]) = this intersect that
  def union(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    new IntLikeSet[I, T](bits, set union that.set)
  }
  def |(that : IntLikeSet[I, T]) = this union that
  def max = castIT(bits, getBWCBDD match {
    case False => throw new UnsupportedOperationException
    case True => IntSet.fromBitVector(List.fill(boundedBits.bits - bits + 1)(false) ++ List.fill(bits - 1)(true))
    case Node(set, False) => {
      val trueMost = set.trueMost.get.padTo(bits - 1, true)
      IntSet.fromBitVector(List.fill(boundedBits.bits - bits)(false) ++ (true :: trueMost))(int, bounded, boundedBits)
    }
    case Node(_, uset)    => {
      val trueMost = uset.trueMost.get.padTo(bits - 1, true)
      IntSet.fromBitVector(List.fill(boundedBits.bits - bits + 1)(false) ++ trueMost)(int, bounded, boundedBits)
    }
  })
  def min = castIT(bits, getBWCBDD match {
    case False => throw new UnsupportedOperationException
    case True => IntSet.fromBitVector(List.fill(boundedBits.bits - bits)(false) ++ (true :: List.fill(bits - 1)(false)))
    case Node(False, uset) => {
      val falseMost = uset.falseMost.get.padTo(bits - 1, false)
      IntSet.fromBitVector(List.fill(boundedBits.bits - bits + 1)(false) ++ falseMost)(int, bounded, boundedBits)
    }
    case Node(set, _)    => {
      val falseMost = set.falseMost.get.padTo(bits - 1, false)
      IntSet.fromBitVector(List.fill(boundedBits.bits - bits)(false) ++ (true :: falseMost))(int, bounded, boundedBits)
    }
  })
  def sizeBigInt = set.cbdd.truePaths.map((x) => BigInt(1l << (boundedBits.bits - x.length))).sum
  override def size : Int = {
    val bint = sizeBigInt
    if(bint > Integer.MAX_VALUE) throw new IllegalArgumentException("size does not fit into an Int")
    bint.intValue
  }
  def sizeGreaterThan(value : BigInt) : Boolean = {
    import scala.math.BigInt._
    require(value >= 0)
    var size : BigInt = 0
    for(p <- set.cbdd.truePaths) {
      size += 2 pow (boundedBits.bits - p.length)
      if(size > value) return true
    }
    return false
  }
  def sizeGreaterThan(value : Int) : Boolean = sizeGreaterThan(value : BigInt)
  def randomElement() = castIT((bits, set.randomElement()))
  def subsetOf(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    set subsetOf that.set
  }
  override def isEmpty = set.isEmpty
  override def nonEmpty = set.nonEmpty
  def changeBitWidth(nbits : Int) = new IntLikeSet[I, T](nbits, set)
  private def getBWCBDD = set.cbdd.partialEval(List.fill(boundedBits.bits - bits)(false)) match {
    case Some(x) => x
    case _ => {
      assert(false, "Integrity failure")
      ???
    }
  }
  private def fromBWCBDD(bdd : CBDD) = new IntLikeSet[I, T](bits, new IntSet[I](CBDD(List.fill(boundedBits.bits - bits)(false), False, False, bdd)))
  def isFull = getBWCBDD match {
    case True => true
    case _ => false
  }
  def plus(that : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    val (norm, ov) = this.plusWithCarry(that)
    norm | ov
  }
  def plusWithCarry(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    val (norm, ov) = CBDD.plus(getBWCBDD, that.getBWCBDD, bits)
    (fromBWCBDD(norm), fromBWCBDD(ov))
  }
  def negate = fromBWCBDD(CBDD.negate(bits, getBWCBDD))
  def bAnd(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    new IntLikeSet[I, T](bits, set bAnd that.set)
  }
  def bOr(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    new IntLikeSet[I, T](bits, set bOr that.set)
  }
  def bXOr(that : IntLikeSet[I, T]) = {
    checkBitWidth(this, that)
    new IntLikeSet[I, T](bits, set bXOr that.set)
  }
  def bNot = fromBWCBDD(CBDD.bNot(getBWCBDD))
  def bShr(steps : Int) = {
    require(steps >= 0)
    fromBWCBDD(CBDD(List.fill(steps min bits)(false), False, False, getBWCBDD.take(bits - steps)))
  }
  def bShl(steps : Int) = {
    require(steps >= 0)
    fromBWCBDD(CBDD.bAnd(getBWCBDD.dropOr(steps min bits), CBDD( List.fill(bits - steps)(true) ++ List.fill(steps min bits)(false) )))
  }
  def bRor(steps : Int) = {
    require(steps >= 0)
    val steps_ = steps % bits
    val bdd = getBWCBDD
    val upper = CBDD.bAnd(bdd.dropOr(bits - steps_), CBDD(List.fill(steps_)(true) ++ List.fill(bits - steps_)(false)))
    val lower = CBDD(List.fill(steps_)(false), False, False, bdd.take(bits - steps_))
    //println(upper.truePaths.force, lower.truePaths.force, (CBDD.bOr(upper, lower)).truePaths.force)
    //println(fromBWCBDD(CBDD.bOr(upper, lower)).set.cbdd.truePaths.force)
    fromBWCBDD(CBDD.bOr(upper, lower))
  }
  def bRol(steps : Int) = bRor(bits - steps)
  def bSar(steps : Int) = {
    require(steps >= 0)
    val bdd = getBWCBDD
    val (negCBDD, posCBDD) = bdd match {
      case True => (True, True)
      case False => (False, False)
      case Node(set, uset) => (set, uset)
    }
    val toPrepend = (bits - 1) min steps
    val toTake = bits - steps - 1
    //println("Bits: " + bits + ", steps: " + steps + ", toPrepend: " + toPrepend + ", toTake: " + toTake + ", toPrepend + toTake: " + (toPrepend + toTake))
    val negRes = CBDD(true :: List.fill(toPrepend)(true), False, False, negCBDD.take(toTake))
    val posRes = CBDD(false :: List.fill(toPrepend)(false), False, False, posCBDD.take(toTake))
    fromBWCBDD(negRes || posRes)
  }
  //XXX how to deal with odering restriction?
  /*private*/ def toIvalSetT(depths : Int)(implicit ord : Ordering[T]) = toIvalSetI(depths).map{
    case FilledIval(lo, hi) => FilledIval(castIT(bits, lo), castIT(bits, hi))
  }
  def toIvalSetI(depths : Int) = (Set[Interval[I]]() /: getBWCBDD.take(depths).truePaths){
    (acc, path) =>
      path match {
        case List() => {
          val v1 = IntSet.fromBitVector(true :: List.fill(bits - 1)(false))
          val v2 = IntSet.fromBitVector(false :: List.fill(bits - 1)(true))
          acc + FilledIval(v1, v2)
        }
        case _ => {
          val plen = path.length
          val path1 = path ++ List.fill(bits - plen)(false)
          val path2 = path ++ List.fill(bits - plen)(true)
          val v1 = IntSet.fromBitVector(path1)
          val v2 = IntSet.fromBitVector(path2)
          acc + FilledIval(v1, v2)
        }
      }
  }
  def toIvalSetPrecise : Set[Interval[I]] = this.map{
    x =>
      val (b, v) = castTI(x)
      val bits_ = boundedBits.bits - b
      val v_ = IntSet.toBitVector(v).drop(bits_)
      val v__ = if(v_.head) List.fill(bits_)(true) ++ v_ else List.fill(bits_)(false) ++ v_
      val v___ = IntSet.fromBitVector(v__)
      FilledIval(v___, v___)
  }
  def getNegPos = getBWCBDD match {
    case Node(set, uset) => (fromBWCBDD(Node(set, False)), fromBWCBDD(Node(False, uset)))
    case x => (fromBWCBDD(Node(x, False)), fromBWCBDD(Node(False, x)))
  }
  /*
   * should have toivalset such that Set(-1) yields [-1 .. -1] even if depths is only 1
   *  -> go down bdd until first node with both sub-bdds non false
   */
  /*
   * As specified in RTLOperation.java, pentium.ssl mul always doubles
   * bitWidth. Furthermore, original implementation computes on long
   * and ignores overflow - we do the same...
   */
  def mul(elems : Int, depths_ : Int)(that : IntLikeSet[I, T]) = {
    import int.{ mkNumericOps, mkOrderingOps }
    import cc.sven.interval.Interval._
    val ivalInt = implicitly[Arith[Interval[I]]]
    import ivalInt.mkArithOps
    checkBitWidth(this, that)
    val depths = if(sizeGreaterThan(elems) || that.sizeGreaterThan(elems)) depths_ else bits
    val ivalSet1 = if(depths == bits) toIvalSetPrecise else toIvalSetI(depths)
    val ivalSet2 = if(depths == bits) that.toIvalSetPrecise else that.toIvalSetI(depths)
    /*println("ivalSet1: " + ivalSet1)
    println("ivalSet2: " + ivalSet2)*/
    val bits_ = bits * 2
    assert(bits_ <= implicitly[BoundedBits[I]].bits)
    val ivalRes = for{
      a <- ivalSet1
      b <- ivalSet2
    } yield {
      //(a * b)
      (a, b) match {
        case (EmptyIval, _) => EmptyIval
        case (_, EmptyIval) => EmptyIval
        case (FilledIval(lo1, hi1), FilledIval(lo2, hi2)) => {
          //force BigInt operation because fuck it - I want results!
          //this will have a special place int he hall of shame
          //XXX SCM : Change this horrible thing!
          val a = BigInt(lo1.toLong) * BigInt(lo2.toLong)
          val b = BigInt(lo1.toLong) * BigInt(hi2.toLong)
          val c = BigInt(hi1.toLong) * BigInt(lo2.toLong)
          val d = BigInt(hi1.toLong) * BigInt(hi2.toLong)
          val lo = a min b min c min d
          val hi = a max b max c max d
          val a_ = lo1 * lo2
          val b_ = lo1 * hi2
          val c_ = hi1 * lo2
          val d_ = hi1 * hi2
          val lo_ = a_ min b_ min c_ min d_
          val hi_ = a_ max b_ max c_ max d_
          val lo__ = if(BigInt(lo_.toLong) != lo) bounded.minBound else lo_
          val hi__ = if(BigInt(hi_.toLong) != hi) bounded.maxBound else hi_
          FilledIval(lo__, hi__)
        }
      }
    }
    //println(ivalSet1 + " * " + ivalSet2 + " == " + ivalRes)
    /*ivalRes.map{
      case EmptyIval => IntLikeSet[I, T](bits_)
      case FilledIval(lo, hi) => new IntLikeSet[I, T](bits_, new IntSet[I](CBDD(IntSet.toBitVector(lo), IntSet.toBitVector(hi))))
    }*/
    //def intLikeFromTo(lo : I, hi : I) = new IntLikeSet[I, T](bits_, new IntSet[I](CBDD(IntSet.toBitVector(lo), IntSet.toBitVector(hi))))
    /*def intLikeFromTo(lo : I, hi : I) = new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, hi)))
    (IntLikeSet[I, T](bits_) /: ivalRes){
      case (acc, EmptyIval) => acc
      case (acc, FilledIval(lo, hi)) if lo >= int.zero => acc union intLikeFromTo(lo, hi)
      case (acc, FilledIval(lo, hi)) => {
        val lower = intLikeFromTo(lo, -int.one)
        val upper = intLikeFromTo(int.zero, hi)
        acc union lower union upper
      }
    }*/
   (IntLikeSet[I, T](bits_) /: ivalRes){
     case (acc, EmptyIval) => acc
     case (acc, FilledIval(lo, hi)) => acc union IntLikeSet.range[I, T](bits_ min boundedBits.bits, lo, hi).changeBitWidth(bits_)
   }
  }
  def mulSingleton(op : T) : IntLikeSet[I, T] = {
    val (opBits, opI) = castTI(op)
    assert(opBits == bits)
    val opBools = IntSet.toBitVector(opI).drop(boundedBits.bits - bits)
    //only positive for now...
    require(!opBools.head)
    
    ???
  }
  def checkIntegrity() {
    def helper(cbdd : CBDD, depth : Int) : Boolean = cbdd match {
      case _ if depth == 0 => true
      case Node(False, uset) => helper(uset, depth - 1)
      case _ => false
    }
    assert(helper(set.cbdd, boundedBits.bits - bits), "Integrity failure in explicit check")
  }
  def iterator() = new IntLikeSetIterator(this)(castIT)
  def java = this.asJava
  def bitExtract(from : Int, to : Int) : IntLikeSet[I, T] = {
    require(from >= to && to >= 0)
    val toDrop = bits - from - 1
    val toTake = from - to + 1
    val toFill = bits - toTake
    def takeFkt(cbdd : CBDD) : CBDD = cbdd.take(toTake)
    def reduceFkt(a : CBDD, b : CBDD) = a || b
    val iSet = fromBWCBDD(CBDD(List.fill(toFill)(false), False, False, getBWCBDD.drop(toDrop, False, takeFkt, reduceFkt)))
    new IntLikeSet[I, T](toTake, iSet.set)
  }
  def signExtend(from : Int, to : Int) : IntLikeSet[I, T] = {
    require(from >= to && to >= 0)
    val nBits = bits max (from + 1)
    assert(nBits <= boundedBits.bits, "Inner type not large enough")
    val mask = CBDD(List.fill(boundedBits.bits - 1 - from)(false) ++ List.fill(from - to + 1)(true) ++ List.fill(to)(false))
    val (neg, pos) = getBWCBDD match {
      case True => (True, True)
      case False => (False, False)
      case Node(set, uset) => (Node(set, False), Node(False, uset))
    }
    val negBDD = fromBWCBDD(neg).set.cbdd
    val posBDD = fromBWCBDD(pos).set.cbdd
    //println(new IntSet[I](mask), new IntSet[I](negBDD), new IntSet[I](posBDD))
    val nBDD = negBDD match {
      case False => posBDD
      case _ => CBDD.bOr(negBDD, mask) || posBDD
    }
    new IntLikeSet[I, T](nBits, new IntSet[I](nBDD))
  }
  def zeroFill(from : Int, to : Int) : IntLikeSet[I, T] = {
    require(from >= to && to >= 0)
    val nBits = bits max (from + 1)
    val mask = CBDD(List.fill(boundedBits.bits - 1 - from)(true) ++ List.fill(from - to + 1)(false) ++ List.fill(to)(true))
    val nBDD = CBDD.bAnd(set.cbdd, mask)
    new IntLikeSet[I, T](nBits, new IntSet[I](nBDD))
  }
  def restrictGreaterOrEqual(that : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    require(!that.isEmpty)
    require(bits == that.bits)
    import int.mkNumericOps
    val max = if(bits == 1)
      new IntLikeSet[I, T](bits, IntSet[I](int.zero))
    else
      (new IntLikeSet[I, T](boundedBits.bits, IntSet[I](-int.one))).bitExtract(bits - 2, 0).changeBitWidth(bits)
    val allowedSet = IntLikeSet.range[I,T](that.min, max.max)
    intersect(allowedSet)
  }
  def restrictLessOrEqual(that : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    require(!that.isEmpty)
    require(bits == that.bits)
    import int.mkNumericOps
    val min = if(bits == 1)
      new IntLikeSet[I, T](bits, IntSet[I](int.one))
    else
      (new IntLikeSet[I, T](boundedBits.bits, IntSet[I](-int.one))).bitExtract(bits - 2, 0).changeBitWidth(bits).bNot
    val allowedSet = IntLikeSet.range[I, T](min.min, that.max)
    intersect(allowedSet)
  }
  def restrictGreater(that : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    require(!that.isEmpty)
    require(bits == that.bits)
    import int.mkNumericOps
    val max = if(bits == 1)
      new IntLikeSet[I, T](bits, IntSet[I](int.zero))
    else
      (new IntLikeSet[I, T](boundedBits.bits, IntSet[I](-int.one))).bitExtract(bits - 2, 0).changeBitWidth(bits)
    if(that.min == max.max) IntLikeSet[I, T](bits) else
    if(bits == 1) intersect(!(IntLikeSet[I, T](bits) + that.min)) else {
      val upper = IntSet.fromBitVector(List.fill(boundedBits.bits - bits)(false) ++ IntSet.toBitVector(castTI(that.min)._2 + int.one).drop(boundedBits.bits - bits))
      val upperSet = IntLikeSet[I, T](bits) + (castIT(bits, upper))
      restrictGreaterOrEqual(upperSet)
    }
  }
  def restrictLess(that : IntLikeSet[I, T]) : IntLikeSet[I, T] = {
    require(!that.isEmpty)
    require(bits == that.bits)
    import int.mkNumericOps
    val min = if(bits == 1)
      new IntLikeSet[I, T](bits, IntSet[I](int.one))
    else
      (new IntLikeSet[I, T](boundedBits.bits, IntSet[I](-int.one))).bitExtract(bits - 2, 0).changeBitWidth(bits).bNot
    if(that.max == min.min) IntLikeSet[I, T](bits) else
    if(bits == 1) intersect(!(IntLikeSet[I, T](bits) + that.max)) else {
      val lower = IntSet.fromBitVector(List.fill(boundedBits.bits - bits)(false) ++ IntSet.toBitVector(castTI(that.max)._2 - int.one).drop(boundedBits.bits - bits))
      val lowerSet = IntLikeSet[I, T](bits) + (castIT(bits, lower))
      restrictLessOrEqual(lowerSet)
    }
  }
}
object IntLikeSet {
  def apply[I, T](bits : Int)(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = new IntLikeSet(bits, IntSet[I]()(int, bounded, boundedBits))
  def apply[I, T](bits : Int, set : Set[T])(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = new IntLikeSet(bits, IntSet[I](set.map(castTI(_)._2))(int, bounded, boundedBits))
  def apply[I, T](set : Set[T])(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], tboundedBits : BoundedBits[T], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = apply(tboundedBits.bits, set)
  def applyJLong[T](bits : Int)(implicit dboundedBits : DynBoundedBits[T], castTI : Castable[T, cc.sven.misc.Pair[Integer, java.lang.Long]], castIT : Castable[cc.sven.misc.Pair[Integer, java.lang.Long], T]) : IntLikeSet[java.lang.Long, T] = {
    import cc.sven.misc.Pair
    implicit val castITT = new Castable[(Int, java.lang.Long), T] {
      def apply(p : (Int, java.lang.Long)) = castIT(Pair(p._1, p._2))
    }
    implicit val castTIT = new Castable[T, (Int, java.lang.Long)] {
      def apply(t : T) : (Int, java.lang.Long) = {
        val temp = castTI(t)
        (temp._1, temp._2)
      }
    }
    apply[java.lang.Long, T](bits)(cc.sven.integral.Implicits.jLongIsIntegral, cc.sven.bounded.Bounded.jLongIsBounded, cc.sven.bounded.BoundedBits.jLongIsBoundedBits, dboundedBits, castTIT, castITT)
  }
  //def apply[I, T](ival : FilledIval[T])(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = range[I, T](ival.lo, ival.hi)
  def apply[I, T](bits : Int, ival : Interval[T])(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = ival match {
    case EmptyIval => apply[I, T](bits)
    case FilledIval(lo, hi) => {
      require(dboundedBits.dBits(lo) == bits)
      require(dboundedBits.dBits(lo) == dboundedBits.dBits(hi))
      range[I, T](lo, hi)
    }
  }
  def range[I, T](lo : T, hi : T)(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = {
    val bits_ = dboundedBits.dBits(lo)
    require(bits_ > 0)
    require(bits_ == dboundedBits.dBits(hi))
    val (lobits, lo_) = castTI(lo)
    val (hibits, hi_) = castTI(hi)
    require(lobits == hibits)
    range[I, T](bits_, lo_, hi_)
  }
  def range[I, T](bits_ : Int, lo : I, hi : I)(implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) : IntLikeSet[I, T] = {
    import int.mkOrderingOps
    def isBitNeg(i : I) = IntSet.toBitVector(i).drop(boundedBits.bits - bits_).head
    (isBitNeg(lo), isBitNeg(hi)) match {
      case (false, true) if bits_ == 1 => range(bits_, hi, lo) //Cludge for booleans, order is reversed there in jakstab :(
      case (false, true) => throw new IllegalArgumentException
      case (true, false) if lo < int.zero => new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, hi)))
      case (true, false) => {
        val negOne = IntSet.fromBitVector(List.fill(boundedBits.bits - bits_)(false) ++ List.fill(bits_)(true))
        new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, negOne)) union IntSet[I](FilledIval(int.zero, hi)))
      }
      case _ => new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, hi)))
    }
    //Number is not negative
   /* if(!IntSet.toBitVector(lo).drop(boundedBits.bits - bits_).head)
      new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, hi)))
    else {
      val negOne = IntSet.fromBitVector(List.fill(boundedBits.bits - bits_)(false) ++ List.fill(bits_)(true))
      val zero = int.zero
      val lower = new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(lo, negOne min hi)))
      val upper = new IntLikeSet[I, T](bits_, IntSet[I](FilledIval(zero, hi)))
      lower union upper
    }*/
  }
  def rangeJLong[T](lo : T, hi : T)(implicit dboundedBits : DynBoundedBits[T], castTI : Castable[T, cc.sven.misc.Pair[Integer, java.lang.Long]], castIT : Castable[cc.sven.misc.Pair[Integer, java.lang.Long], T]) : IntLikeSet[java.lang.Long, T] = {
    import cc.sven.misc.Pair
    implicit val castITT = new Castable[(Int, java.lang.Long), T] {
      def apply(p : (Int, java.lang.Long)) = castIT(Pair(p._1, p._2))
    }
    implicit val castTIT = new Castable[T, (Int, java.lang.Long)] {
      def apply(t : T) : (Int, java.lang.Long) = {
        val temp = castTI(t)
        (temp._1, temp._2)
      }
    }
    range[java.lang.Long, T](lo, hi)(cc.sven.integral.Implicits.jLongIsIntegral, cc.sven.bounded.Bounded.jLongIsBounded, cc.sven.bounded.BoundedBits.jLongIsBoundedBits, dboundedBits, castTIT, castITT)
  }
}

object Implicits {
  implicit def intLikeSetIsDynBounded[I, T] : DynBoundedBits[IntLikeSet[I, T]] = new DynBoundedBits[IntLikeSet[I, T]] {
    def dBits(set : IntLikeSet[I, T]) : Int = set.bits
  }
}

class IntLikeSetIterator[I, T](ilsi : IntLikeSet[I, T])(implicit castIT : Castable[(Int, I), T]) extends Iterator[T] {
  val ilsiIter = ilsi.set.iterator()
  def hasNext() = ilsiIter.hasNext()
  def next() = castIT((ilsi.bits, ilsiIter.next()))
}