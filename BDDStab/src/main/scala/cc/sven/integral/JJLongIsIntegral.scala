package cc.sven.integral

class JJLongIsIntegral extends JJLongIsOrdering with Integral[java.lang.Long] {
  def plus(x: java.lang.Long, y: java.lang.Long): java.lang.Long = x.longValue + y
  def minus(x: java.lang.Long, y: java.lang.Long): java.lang.Long = x.longValue - y
  def times(x: java.lang.Long, y: java.lang.Long): java.lang.Long = x.longValue * y
  def quot(x: java.lang.Long, y: java.lang.Long): java.lang.Long = x.longValue / y
  def rem(x: java.lang.Long, y: java.lang.Long): java.lang.Long = x.longValue % y
  def negate(x: java.lang.Long): java.lang.Long = -x.longValue
  def fromInt(x: Int): java.lang.Long = x
  def toInt(x: java.lang.Long): Int = x.intValue
  def toLong(x: java.lang.Long): Long = x
  def toFloat(x: java.lang.Long): Float = x.longValue.toFloat
  def toDouble(x: java.lang.Long): Double = x.longValue.toDouble
}