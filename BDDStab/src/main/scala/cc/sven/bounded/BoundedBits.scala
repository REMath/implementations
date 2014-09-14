package cc.sven.bounded

object BoundedBits {
  implicit val intIsBoundedBits = new JIntIsBoundedBits
  implicit val integerIsBoundedBits = new JIntegerIsBoundedBits
  implicit val longIsBoundedBits = new JLongIsBoundedBits
  implicit val jLongIsBoundedBits = new JJLongIsBoundedBits
}

trait BoundedBits[T] {
  val bits: Int
}