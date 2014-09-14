package cc.sven.bounded

//class for Java interop
class JJLongIsBounded extends Bounded[java.lang.Long] {
  val maxBound = Long.box(Long.MaxValue)
  val minBound = Long.box(Long.MinValue)
  val maxNeg = Long.box(-1)
  val minNotNeg = Long.box(0)
}