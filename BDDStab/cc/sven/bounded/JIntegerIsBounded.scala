package cc.sven.bounded

//class for Java interop
class JIntegerIsBounded extends Bounded[Integer] {
  val maxBound = new Integer(Integer.MAX_VALUE)
  val minBound = new Integer(Integer.MIN_VALUE)
  val maxNeg = new Integer(-1)
  val minNotNeg = new Integer(0)
}