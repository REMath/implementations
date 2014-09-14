package cc.sven.misc

import cc.sven.tlike._
import cc.sven.bounded._

object Misc {
  def cartesianProduct[A, B](as : Set[A], bs : Set[B]) : Set[(A, B)] = for{
    a <- as
    b <- bs
  } yield (a, b)
  
  def longBittedOp(normalop : (Int, Long, Long) => Long, intlikeop : (IntLikeSet[Long, NBitLong], IntLikeSet[Long, NBitLong]) => IntLikeSet[Long, NBitLong]) : (Set[Long], Set[Long], Int) => Boolean =
      (a : Set[Long], b : Set[Long], bits : Int) => {
      val longBits = implicitly[BoundedBits[Long]].bits
      val bits_ = NBitLong.boundBits(bits)
      val aBounded = a.map(NBitLong.bound(_, bits_))
      val bBounded = b.map(NBitLong.bound(_, bits_))
      val a_ = (IntLikeSet[Long, NBitLong](bits_) /: aBounded)((acc, x) => acc + NBitLong(bits_, x))
      val b_ = (IntLikeSet[Long, NBitLong](bits_) /: bBounded)((acc, x) => acc + NBitLong(bits_, x))
      val ref = cartesianProduct(aBounded, bBounded).map((x) => NBitLong.signContract(bits_, normalop(bits_, x._1, x._2)))
      val us = intlikeop(a_, b_)
      val castIT = implicitly[Castable[(Int, Long), NBitLong]]
      val ref_ = ref.map((x : Long) => castIT((bits_, x)))
      val res = us == ref_
      if(!res) println("inputa_: " + a_ + ", inputb_: " + b_ + ", bits: " + bits_ + ", us: " + us + ", ref: " + ref_ + ", result: " + res)
      res
      }
}