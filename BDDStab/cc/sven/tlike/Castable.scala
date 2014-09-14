package cc.sven.tlike

import cc.sven.bounded.BoundedBits

trait Castable[A, B] {
  def apply(a : A) : B
}

object Castable {
  implicit def tToT[T] = new Castable[T, T] {
    def apply(t :T) : T = t
  }
  implicit def boundedBitsToCastableBW[T](implicit boundedBits : BoundedBits[T]) = new Castable[T, (Int, T)] {
    def apply(t : T) : (Int, T) = (boundedBits.bits, t)
  }
  //XXX change this such that it works for signed - then iterator would work again
  implicit def BWCastable[T] = new Castable[(Int, T), T] {
    def apply(p : (Int, T)) : T = p._2
  }
  /*implicit class As[A, B](a : A)(implicit castb : Castable[A, B]) {
    def as[C](implicit eq : C =:= B) = castb.cast(a)
  }*/
}