package cc.sven.bounded

//class for Java interop
class JLongIsBounded extends Bounded[Long] {
  val maxBound = Long.MaxValue
  val minBound = Long.MinValue
  val maxNeg = -1l
  val minNotNeg = 0l
}