package cc.sven.intset

import cc.sven.bounded._
import scala.collection.JavaConverters._;

trait FiniteOrderedIntegral[T] extends Integral[T] with Ordered[T] with Bounded[T] with BoundedBits[T] {
  def fromBitVector(bv : List[Boolean]) : T = {
    require(bv.length <= bits)
    IntSet.fromBitVector(bv)(this, this, this)
  }
  def fromBitVector(bv : java.util.List[Boolean]) : T = fromBitVector(bv.asScala.toList)
  def fromLong(l : Long) = IntSet.toBitVector(l)
}