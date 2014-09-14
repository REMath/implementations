package cc.sven.constraint

import cc.sven.bounded._
import scala.collection.immutable.HashMap
import scala.collection.immutable.Set
import cc.sven.tlike._
//import org.scalacheck.Arbitrary
//import org.scalacheck.Gen

trait Constrainable[T, S[_]] {
  def range(lo : T, hi : T) : S[T]
  def intersect(a : S[T], b : S[T]) : S[T]
  def union(a : S[T], b : S[T]) : S[T]
  //def intersect[SS >: S[T]](a : SS, b : SS) : S[T]
  def isEmpty(a : S[T]) : Boolean
  def min(a : S[T]) : T
  def max(a : S[T]) : T
  def invert(a : S[T]) : S[T]
  def getPosNeg(a : S[T]) : (S[T], S[T])
}

object Constraint {
  implicit def intLikeSetIsConstrainable[I, T]
    (implicit int : Integral[I], bounded : Bounded[I], boundedBits : BoundedBits[I], dboundedBits : DynBoundedBits[T], castTI : Castable[T, (Int, I)], castIT : Castable[(Int, I), T]) =
    new Constrainable[T, ({type x[a]=IntLikeSet[I, a]})#x] {
      def range(lo : T, hi : T) = IntLikeSet.range[I, T](lo, hi)
      def intersect(a : IntLikeSet[I, T], b : IntLikeSet[I, T]) = a.intersect(b)
      def union(a : IntLikeSet[I, T], b : IntLikeSet[I, T]) = a.union(b)
      def isEmpty(a : IntLikeSet[I, T]) = a.isEmpty
      def min(a : IntLikeSet[I, T]) = a.min
      def max(a : IntLikeSet[I, T]) = a.max
      def invert(a : IntLikeSet[I, T]) = !a
      def getPosNeg(a : IntLikeSet[I, T]) = a.getNegPos
  }
 /* implicit val arbitraryConstrainable : Arbitrary[Constraint] = Arbitrary {
    def step(size : Int) = {/*println("step(" + size + ")");*/ size - 10}
    val genId = for(x <- Arbitrary.arbitrary[Int]) yield if(x == Int.MinValue) 1 else (x.abs % Int.MaxValue) + 1
    val genLT = for(id1 <- genId; id2 <- genId) yield LT(id1, id2)
    val genGT = for(id1 <- genId; id2 <- genId) yield GT(id1, id2)
    val genULT = for(id1 <- genId; id2 <- genId) yield ULT(id1, id2)
    val genUGT = for(id1 <- genId; id2 <- genId) yield UGT(id1, id2)
    val genLTE = for(id1 <- genId; id2 <- genId) yield LTE(id1, id2)
    val genGTE = for(id1 <- genId; id2 <- genId) yield GTE(id1, id2)
    val genULTE = for(id1 <- genId; id2 <- genId) yield ULTE(id1, id2)
    val genUGTE = for(id1 <- genId; id2 <- genId) yield UGTE(id1, id2)
    val genEquals = for(id1 <- genId; id2 <- genId) yield Equals(id1, id2)
    val genNEquals = for(id1 <- genId; id2 <- genId) yield NEquals(id1, id2)
    val genSimpleConstraint = Gen.oneOf(genLT, genGT, genULT, genUGT, genLTE, genGTE, genULTE, genUGTE, genEquals, genNEquals)
    
    def genConnective(size : Int) : Gen[Constraint] = if(size <= 0) genSimpleConstraint else Gen.frequency((1, genSimpleConstraint), (2, genAnd(step(size))), (2, genOr(step(size))), (2, genNot(step(size))))

    def genAnd(size : Int) = for(op1 <- genConnective(step(size)); op2 <- genConnective(step(size))) yield And(op1, op2)
    def genOr(size : Int) = for(op1 <- genConnective(step(size)); op2 <- genConnective(step(size))) yield Or(op1, op2)
    def genNot(size : Int) = for(op <- genConnective(step(size))) yield Not(op)
    
    Gen.sized(genConnective)
  }*/
  def createEq(left : Int, right : Int) : Constraint = Equals(left, right)
  def createNEq(left : Int, right : Int) : Constraint = NEquals(left, right)
  def createLt(left : Int, right : Int) : Constraint = LT(left, right)
  def createLte(left : Int, right : Int) : Constraint = LTE(left, right)
  def createGt(left : Int, right : Int) : Constraint = GT(left, right)
  def createGte(left : Int, right : Int) : Constraint = GTE(left, right) 
  def createULt(left : Int, right : Int) : Constraint = ULT(left, right)
  def createULte(left : Int, right : Int) : Constraint = ULTE(left, right)
  def createNot(constraint : Constraint) : Constraint = Not(constraint)
  def createAnd(left : Constraint, right : Constraint) : Constraint = And(left, right)
  def createOr(left : Constraint, right : Constraint) : Constraint = Or(left, right)
}

sealed trait Constraint {
  def getVarIds : Set[Int] = {
    def helper(iSet : Set[Int], c : Constraint) : Set[Int] = c match {
      case LT(l, r) => iSet + l + r
      case GT(l, r) => iSet + l + r
      case LTE(l, r) => iSet + l + r
      case GTE(l, r) => iSet + l + r
      case ULT(l, r) => iSet + l + r
      case UGT(l, r) => iSet + l + r
      case ULTE(l, r) => iSet + l + r
      case UGTE(l, r) => iSet + l + r
      case Equals(l, r) => iSet + l + r
      case NEquals(l, r) => iSet + l + r
      case Not(op) => helper(iSet, op)
      case And(l, r) => helper(helper(iSet, r), l)
      case Or(l, r) => helper(helper(iSet, r), l)
    }
    helper(Set[Int](), this)
  }
  def solveJLong[T](table : java.util.HashMap[Integer, IntLikeSet[java.lang.Long, T]])(implicit dBounded : DynBounded[T], dBoundedBits : DynBoundedBits[T], ord : Ordering[T], castTI : Castable[T, cc.sven.misc.Pair[Integer, java.lang.Long]], castIT : Castable[cc.sven.misc.Pair[Integer, java.lang.Long], T]) : java.util.HashMap[Integer, IntLikeSet[java.lang.Long, T]] = {
    import cc.sven.integral.Implicits._
    import scala.collection.JavaConverters._
    implicit val castTI_ = new Castable[T, (Int, java.lang.Long)]{
      def apply(t : T) = {
        val i = castTI(t)
        (i._1, i._2)
      }
    }
    implicit val castIT_ = new Castable[(Int, java.lang.Long), T]{
      def apply(i : (Int, java.lang.Long)) = castIT(cc.sven.misc.Pair(i._1, i._2))
    }
    implicit val constrainable = Constraint.intLikeSetIsConstrainable[java.lang.Long, T]
    val res = solve[T,({type x[a]=IntLikeSet[java.lang.Long, a]})#x](HashMap(table.asScala.toStream.map(x => (x._1 : Int, x._2)) : _*))
    new java.util.HashMap(res.map(x => (x._1 : Integer, x._2)).asJava)
  }
  def solve[T, S[_]](table : HashMap[Int, S[T]])(implicit dBounded : DynBounded[T], ord : Ordering[T], const : Constrainable[T, S]) : HashMap[Int, S[T]] = {
    import ord.mkOrderingOps
    val varIds = getVarIds
    //under each variable id of this, there needs to be a non-empty set in table
    require(varIds.forall((x) => !const.isEmpty(table(x))))
    //Build a state including all values
    val allFull = (HashMap.empty[Int, S[T]] /: varIds){
      (acc, id) =>
        val setVal = const.min(table(id))
        val min = dBounded.dMinBound(setVal)
        val max = dBounded.dMaxBound(setVal)
        acc + ((id, const.range(min, max)))
    }
    def stateInvert(state : HashMap[Int, S[T]]) : HashMap[Int, S[T]] = state.map{case (k, v) => (k, const.invert(v))}
    val allEmpty = stateInvert(allFull)
    def valid(leftmin : Option[T], leftid : Int, leftmax : Option[T], rightmin : Option[T], rightid : Int, rightmax : Option[T], underapprox : Boolean) : HashMap[Int, S[T]] = {
      val left = const.min(table(leftid))
      val right = const.min(table(rightid))
      val leftMinBound = dBounded.dMinBound(left)
      val leftMaxBound = dBounded.dMaxBound(left)
      val rightMinBound = dBounded.dMinBound(right)
      val rightMaxBound = dBounded.dMaxBound(right)
      val leftmin_ = leftMinBound max leftmin.getOrElse(leftMinBound)
      val leftmax_ = leftMaxBound min leftmax.getOrElse(leftMaxBound)
      val rightmin_ = rightMinBound max rightmin.getOrElse(rightMinBound)
      val rightmax_ = rightMaxBound min rightmax.getOrElse(rightMaxBound)
      val validLeft = const.range(leftmin_, leftmax_)
      val validRight = const.range(rightmin_, rightmax_)
      //println("leftmin: " + leftmin + ", leftid: " + leftid + ", leftmax: " + leftmax + ", rightmin: " + rightmin + ", rightmax: " + rightmax + ", underapprox: " + underapprox + ", validLeft: " + validLeft + ", validRight: " + validRight)
      (if(underapprox) allEmpty else allFull) + ((leftid, validLeft)) + ((rightid, validRight))
    }
    def buildAllValid(formula : Constraint, underapprox : Boolean) : HashMap[Int, S[T]] = (formula, underapprox) match {
      case (LTE(left, right), false) => valid(None, left, Some(const.max(table(right))), Some(const.min(table(left))), right, None, false)
      case (LTE(left, right), true) =>  valid(None, left, Some(const.min(table(right))), Some(const.max(table(left))), right, None, true)
      case (GTE(left, right), x) => buildAllValid(LTE(right, left), x)
      case (LT(left, right), x) => stateInvert(buildAllValid(GTE(left, right), !x))
      case (GT(left, right), x) => buildAllValid(LT(right, left), x)
      case (ULTE(left, right), false) => {
        val lval = table(left)
        val rval = table(right)
        val lWitness = const.min(lval)
        val rWitness = const.min(rval)
        //to relax safeguards - might be removed.
        require(dBounded.dMinBound(lWitness) == dBounded.dMinBound(rWitness))
        require(dBounded.dMaxBound(lWitness) == dBounded.dMaxBound(rWitness))
        val (lNeg, lPos) = const.getPosNeg(lval)
        val (rNeg, rPos) = const.getPosNeg(rval)
        //Check max dBounded safeguards - what if negative of one is more still pos in other?
        val lValid = if(const.isEmpty(rNeg))
            const.range(dBounded.dMinNotNeg(lWitness), const.max(rPos) min dBounded.dMaxBound(lWitness))
          else
            const.union(const.range(dBounded.dMinNotNeg(lWitness), dBounded.dMaxBound(lWitness)), const.range(const.min(rNeg) max dBounded.dMinBound(lWitness), dBounded.dMaxNeg(lWitness)))
        val rValid = if(const.isEmpty(lPos))
            const.range(dBounded.dMinBound(rWitness), const.max(lNeg) max dBounded.dMinBound(rWitness))
          else
            const.union(const.range(dBounded.dMinBound(rWitness), dBounded.dMaxNeg(rWitness)), const.range(const.min(lPos) max dBounded.dMinNotNeg(rWitness), dBounded.dMaxBound(rWitness)))
        allFull + ((left, lValid)) + ((right, rValid))
      }
      case (ULTE(left, right), true) => {
        val lval = table(left)
        val rval = table(right)
        val lWitness = const.min(lval)
        val rWitness = const.min(rval)
        //to relax safeguards - might be removed.
        require(dBounded.dMinBound(lWitness) == dBounded.dMinBound(rWitness))
        require(dBounded.dMaxBound(lWitness) == dBounded.dMaxBound(rWitness))
        val (lNeg, lPos) = const.getPosNeg(lval)
        val (rNeg, rPos) = const.getPosNeg(rval)
        val lValid = if(const.isEmpty(rPos))
            const.union(const.range(dBounded.dMinNotNeg(lWitness), dBounded.dMaxBound(lWitness)), const.range(const.min(rNeg), dBounded.dMaxNeg(lWitness)))
          else
            const.range(dBounded.dMinNotNeg(lWitness), const.min(rPos))
        val rValid = if(const.isEmpty(lNeg))
            const.union(const.range(dBounded.dMinBound(rWitness), dBounded.dMinNotNeg(rWitness)), const.range(const.max(lPos), dBounded.dMaxBound(rWitness)))
          else
            const.range(dBounded.dMinBound(rWitness), const.min(lNeg))
        allEmpty + ((left, lValid)) + ((right, rValid))
      }
      case (UGTE(left, right), x) => buildAllValid(ULTE(right, left), x)
      case (ULT(left, right), x) => stateInvert(buildAllValid(UGTE(left, right), !x))
      case (UGT(left, right), x) => buildAllValid(ULT(right, left), x)
      case (Equals(left, right), false) => {
        val res = const.intersect(table(left), table(right))
        allFull + ((left, res)) + ((right, res))
      }
      case (Equals(left, right), true) => {
        val res = const.intersect(table(left), table(right))
        //singleton
        if(!const.isEmpty(res) && const.min(res) == const.max(res))
          allEmpty + ((left, res)) + ((right, res))
        else
          allEmpty
      }
      case (NEquals(left, right), x) => stateInvert(buildAllValid(Equals(left, right), !x))
      case (Not(op), x) => stateInvert(buildAllValid(op, !x))
      case (And(left, right), x) => buildAllValid(left, x).merged(buildAllValid(right, x)){
        case ((k1, v1), (k2, v2)) =>
          (k1, const.intersect(v1, v2))
      }
      case (Or(left, right), x) => stateInvert(buildAllValid(And(Not(left), Not(right)), !x))
    }
    //println("buildAllValid(" + formula + ", " + underapprox + ") = " + res)
    //res
    //stub - should intersect table per value*/
    //XXX also be aware of empty sets! - return bottom (or do on java side)
    val vTable = buildAllValid(this, false)
    /*println("Constraint: " + this)
    println(" Table: " + table)
    println("vTable: " + vTable)*/
    table.merged(vTable){case ((i, x), (i_, y)) => (i, const.intersect(x, y))}
  }
}
final case class LT(left : Int, right : Int) extends Constraint
final case class GT(left : Int, right : Int) extends Constraint
final case class LTE(left : Int, right : Int) extends Constraint
final case class GTE(left : Int, right : Int) extends Constraint
final case class ULT(left : Int, right : Int) extends Constraint
final case class UGT(left : Int, right : Int) extends Constraint
final case class ULTE(left : Int, right : Int) extends Constraint
final case class UGTE(left : Int, right : Int) extends Constraint
final case class Equals(left : Int, right : Int) extends Constraint
final case class NEquals(left : Int, right : Int) extends Constraint
final case class Not(op : Constraint) extends Constraint
final case class And(left : Constraint, right : Constraint) extends Constraint
final case class Or(left : Constraint, right : Constraint) extends Constraint