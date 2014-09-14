package cc.sven.bounded

object DynBoundedBits {
  implicit def boundedBitsToDynBoundedBits[T](implicit boundedBits : BoundedBits[T]) : DynBoundedBits[T] = new DynBoundedBits[T] {
    def dBits(t : T) : Int = boundedBits.bits
  }
}

trait DynBoundedBits[T] {
  def dBits(t : T) : Int
}