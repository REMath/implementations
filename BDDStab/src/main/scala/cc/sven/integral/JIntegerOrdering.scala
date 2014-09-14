package cc.sven.integral

class JIntegerOrdering extends Ordering[Integer] {
  def compare(x: Integer, y: Integer): Int = x.intValue compare y.intValue
}