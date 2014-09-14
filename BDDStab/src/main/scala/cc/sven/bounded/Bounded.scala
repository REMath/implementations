package cc.sven.bounded

object Bounded {
  implicit val intIsBounded = new JIntIsBounded
  implicit val integerIsBounded = new JIntegerIsBounded
  implicit val longIsBounded = new JLongIsBounded
  implicit val jLongIsBounded = new JJLongIsBounded
}

trait Bounded[T] {
  val maxBound: T
  val minBound: T
  val maxNeg : T
  val minNotNeg : T
}