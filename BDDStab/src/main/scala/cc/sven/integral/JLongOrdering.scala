package cc.sven.integral

class JLongOrdering {
  def compare(x: Long, y: Long): Int = x.longValue compare y.longValue
}