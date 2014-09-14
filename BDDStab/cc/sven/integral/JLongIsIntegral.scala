package cc.sven.integral

class JLongIsIntegral extends JLongOrdering with Integral[Long] {
  def plus(x: Long, y: Long): Long = x.longValue + y
  def minus(x: Long, y: Long): Long = x.longValue - y
  def times(x: Long, y: Long): Long = x.longValue * y
  def quot(x: Long, y: Long): Long = x.longValue / y
  def rem(x: Long, y: Long): Long = x.longValue % y
  def negate(x: Long): Long = -x.longValue
  def fromInt(x: Int): Long = x
  def toInt(x: Long): Int = x.intValue
  def toLong(x: Long): Long = x
  def toFloat(x: Long): Float = x.longValue.toFloat
  def toDouble(x: Long): Double = x.longValue.toDouble
}