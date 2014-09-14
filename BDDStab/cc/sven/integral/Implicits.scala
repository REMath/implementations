package cc.sven.integral

object Implicits {
  implicit val integerIsIntegral = new JIntegerIsIntegral
  implicit val integerIsOrdering = new JIntegerOrdering
  implicit val longIsIntegral = new JLongIsIntegral
  implicit val longIsOrdering = new JLongOrdering
  implicit val jLongIsIntegral = new JJLongIsIntegral
  implicit val jLongIsOrdering = new JJLongIsOrdering
}