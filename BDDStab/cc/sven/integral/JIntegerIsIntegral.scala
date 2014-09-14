package cc.sven.integral

class JIntegerIsIntegral extends JIntegerOrdering with Integral[Integer] {
  def plus(x: Integer, y: Integer): Integer = x.intValue + y
  def minus(x: Integer, y: Integer): Integer = x.intValue - y
  def times(x: Integer, y: Integer): Integer = x.intValue * y
  def quot(x: Integer, y: Integer): Integer = x.intValue / y
  def rem(x: Integer, y: Integer): Integer = x.intValue % y
  def negate(x: Integer): Integer = -x.intValue
  def fromInt(x: Int): Integer = x
  def toInt(x: Integer): Int = x
  def toLong(x: Integer): Long = x.intValue
  def toFloat(x: Integer): Float = x.intValue.toFloat
  def toDouble(x: Integer): Double = x.intValue.toDouble
}