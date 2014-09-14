package cc.sven.interval

import scala.math.{ Integral, Fractional }

sealed trait Interval[+T]
final class FilledIval[+T](val lo : T, val hi : T) extends Interval[T] {
  override def toString = "[" + lo + " .. " + hi + "]"
  override def equals(that : Any) = that match {
    /* Wow holy shit! I must have been drunk out of my mind!
     * The following bug took about 45 Minutes to find
     * I feel really bad...
     * It's raining outside.
     * It's grey.
     * More coffee...
    case ival : FilledIval[T] => ival.lo == ival.hi 
    */
    case ival : FilledIval[T] => lo == ival.lo && hi == ival.hi
    case _ => false
  }
  override def hashCode = (lo, hi).hashCode
}
object FilledIval {
  def apply[T](lo : T, hi : T)(implicit ord : Ordering[T]) : FilledIval[T] = {
    import ord.mkOrderingOps
    if(lo > hi) apply(hi, lo)(ord) else new FilledIval(lo, hi)
  }
  def unapply[T](ival : Interval[T]) = ival match {
    case EmptyIval => None
    case fival  : FilledIval[T] => Some(fival.lo, fival.hi)
  }
}
case object EmptyIval extends Interval[Nothing]

trait Arith[T] {
  def plus(a : T, b : T) : T
  def minus(a : T, b : T) : T
  def mul(a : T, b : T) : T
  def div(a : T, b : T) : T
  /*def mod(a : T, b : T) : T
  def %(a : T, b : T) : T = mod(a, b)*/
  def negate(a : T) : T
  implicit def mkArithOps(lhs : T) = new ArithOps(lhs) {
    def +(rhs : T) = plus(lhs, rhs)
    def -(rhs : T) = minus(lhs, rhs)
    def *(rhs : T) = mul(lhs, rhs)
    def /(rhs : T) = div(lhs, rhs)
    def unary_- = negate(lhs)
  }
}

abstract class ArithOps[T](lhs : T) {
  def +(rhs : T) : T
  def -(rhs : T) : T
  def *(rhs : T) : T
  def /(rhs : T) : T
  def unary_- : T
}

object Interval {
  implicit def arithFromIntegral[T](implicit int : Integral[T]) = new Arith[T] {
    def plus(a : T, b : T) : T = int.mkNumericOps(a) + b
    def minus(a : T, b : T) : T = int.mkNumericOps(a) - b
    def mul(a : T , b : T) : T = int.mkNumericOps(a) * b
    def div(a : T, b : T) : T = int.mkNumericOps(a) / b
    def negate(a : T) : T = int.negate(a)
  }
  implicit def intervalArith[T](implicit arith : Arith[T], order : Ordering[T]) = new Arith[Interval[T]] {
    import order.mkOrderingOps
    private def arithOp(op : (T, T) => T)(op1 : Interval[T], op2 : Interval[T]) : Interval[T] = (op1, op2) match {
      case (EmptyIval, _) => EmptyIval
      case (_, EmptyIval) => EmptyIval
      case (FilledIval(lo1, hi1), FilledIval(lo2, hi2)) => {
        val a = op(lo1, lo2)
        val b = op(lo1, hi2)
        val c = op(hi1, lo2)
        val d = op(hi1, hi2)
        FilledIval(a min b min c min d, a max b max c max d)
      }
    }
    def plus(a : Interval[T], b : Interval[T]) = arithOp(arith.plus)(a, b)
    def minus(a : Interval[T], b : Interval[T]) = arithOp(arith.minus)(a, b)
    def mul(a : Interval[T], b : Interval[T]) = arithOp(arith.mul)(a, b)
    def div(a : Interval[T], b : Interval[T]) = arithOp(arith.div)(a, b)
    def negate(a : Interval[T]) = a match {
      case EmptyIval => EmptyIval
      case FilledIval(lo, hi) => {
        val nlo = arith.negate(lo)
        val nhi = arith.negate(hi)
        FilledIval(nlo min nhi, nlo max nhi)
      }
    }
  }
}