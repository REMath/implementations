package cc.sven.bounded

//class for Java interop
class JIntIsBounded extends Bounded[Int] {
  val maxBound = Int.MaxValue
  val minBound = Int.MinValue
  val maxNeg = -1
  val minNotNeg = 0
}