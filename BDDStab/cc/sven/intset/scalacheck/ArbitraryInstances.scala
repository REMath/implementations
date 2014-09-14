package cc.sven.intset.scalacheck

import org.scalacheck.Arbitrary
import org.scalacheck.Gen
import cc.sven.tlike._
import cc.sven.constraint._

object ArbitraryInstances {
  implicit val arbitraryNBitLong : Arbitrary[NBitLong] = Arbitrary {
    for{
      long <- Arbitrary.arbitrary[Long]
      bits <- Arbitrary.arbitrary[Int]
      val bits_ = NBitLong.boundBits(bits)
    } yield NBitLong(bits_, NBitLong.bound(long, bits_))
  }
  def arbitraryNBitLong(bits : Int) : Arbitrary[NBitLong] = Arbitrary {
    for(long <- Arbitrary.arbitrary[Long]) yield NBitLong(bits, NBitLong.bound(long, bits))
  }
  implicit val arbitraryConstrainable : Arbitrary[Constraint] = Arbitrary {
    def step(size : Int) = {/*println("step(" + size + ")");*/ size - 10}
    val genId = for(x <- Arbitrary.arbitrary[Int]) yield if(x == Int.MinValue) 1 else (x.abs % Int.MaxValue) + 1
    val genLT = for(id1 <- genId; id2 <- genId) yield LT(id1, id2)
    val genGT = for(id1 <- genId; id2 <- genId) yield GT(id1, id2)
    val genLTE = for(id1 <- genId; id2 <- genId) yield LTE(id1, id2)
    val genGTE = for(id1 <- genId; id2 <- genId) yield GTE(id1, id2)
    val genEquals = for(id1 <- genId; id2 <- genId) yield Equals(id1, id2)
    val genNEquals = for(id1 <- genId; id2 <- genId) yield NEquals(id1, id2)
    val genSimpleConstraint = Gen.oneOf(genLT, genGT, genLTE, genGTE, genEquals, genNEquals)
    
    def genConnective(size : Int) : Gen[Constraint] = if(size <= 0) genSimpleConstraint else Gen.frequency((1, genSimpleConstraint), (2, genAnd(step(size))), (2, genOr(step(size))), (2, genNot(step(size))))

    def genAnd(size : Int) = for(op1 <- genConnective(step(size)); op2 <- genConnective(step(size))) yield And(op1, op2)
    def genOr(size : Int) = for(op1 <- genConnective(step(size)); op2 <- genConnective(step(size))) yield Or(op1, op2)
    def genNot(size : Int) = for(op <- genConnective(step(size))) yield Not(op)
    
    Gen.sized(genConnective)
  }
}