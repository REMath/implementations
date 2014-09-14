package cc.sven.bounded

object DynBounded {
  implicit def boundedToDynBounded[T](implicit bounded : Bounded[T]) : DynBounded[T] = new DynBounded[T] {
    def dMaxBound(t : T) : T = bounded.maxBound
    def dMinBound(t : T) : T = bounded.minBound
    def dMaxNeg(t : T) : T = bounded.maxNeg
    def dMinNotNeg(t : T) : T = bounded.minNotNeg
  }
}

trait DynBounded[T] {
  def dMaxBound(t : T) : T
  def dMinBound(t : T) : T
  def dMaxNeg(t : T) : T
  def dMinNotNeg(t : T) : T
}