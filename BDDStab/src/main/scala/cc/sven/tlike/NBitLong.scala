package cc.sven.tlike

import cc.sven.bounded._
//import org.scalacheck.Arbitrary

class NBitLong(val bits : Int, private val value : Long) {
  import scala.math.BigInt.int2bigInt
  require(value < (2 pow bits))
  def getValue = NBitLong.signExtend(bits, value)
  override def equals(that : Any) = that match {
    case that : NBitLong => bits == that.bits && value == that.value
    case _ => false
  }
  override def hashCode = (bits, value).hashCode
  override def toString = {
    "|" + bits.toString + ":" + NBitLong.signExtend(bits, value).toString + "|"
  }
}
object NBitLong {
  def signExtend(bits : Int, value : Long) : Long = {
    val longBits = implicitly[BoundedBits[Long]].bits
    val signMask = 1l << (bits - 1)
    val extendedValue = if((signMask & value) == 0) value else {
      val extendMask : Long = (0l /: List.range(bits, longBits))((acc, p) => acc | (1l << p))
      value | extendMask
    }
    extendedValue
  }
  def signContract(bits : Int, value : Long) : Long = {
    val longBits = implicitly[BoundedBits[Long]].bits
    val mask : Long = (0l /: List.range(0, bits))((acc, p) => acc | (1l << p))
    value & mask
  }
  def boundBits(bits : Int) = if(bits == Long.MinValue) 1 else (bits.abs % implicitly[BoundedBits[Long]].bits) + 1
  def bound(x : Long, bits : Int) = {
    val max = NBitLong.signContract(bits - 1, -1l)
    val min = NBitLong.signExtend(bits, (1l << bits - 1))
    if(x == max || x == min) x else if(x >= 0) x % (max + 1) else x % (min - 1)
  }
  def apply(bits : Int, value : Long) = {
    val min = signExtend(bits, (1l << bits - 1))
    val max = signContract(bits - 1, -1)
    val longBits = implicitly[BoundedBits[Long]].bits
    //println("bits: " + bits, "min: " + min, "max: " + max, "value: " + value)
    require(bits <= longBits && value <= max && value >= min)
    new NBitLong(bits, signContract(bits, value))
  }
  def apply(value : Long) : NBitLong = {
    val longBits = implicitly[BoundedBits[Long]].bits
    apply(longBits, value)
  }
  class NBitLongIsOrderedC extends Ordering[NBitLong] {
    def compare(a : NBitLong, b : NBitLong) : Int = implicitly[Ordering[Long]].compare(a.getValue, b.getValue)
  }
  implicit val NBitLongIsOrdered = new NBitLongIsOrderedC
  implicit object NBitLongIsDynBoundedBits extends DynBoundedBits[NBitLong] {
    def dBits(nbl : NBitLong) = nbl.bits
  }
  implicit object NBitLongIsDynBounded extends DynBounded[NBitLong] {
    import scala.math.BigInt.int2bigInt
    def dMaxBound(nbl : NBitLong) = apply(nbl.bits, ((2 pow (nbl.bits - 1)) - 1).longValue)
    def dMinBound(nbl : NBitLong) = apply(nbl.bits, (-(2 pow (nbl.bits - 1))).longValue)
    def dMaxNeg(nbl : NBitLong) = apply(nbl.bits, -1l)
    def dMinNotNeg(nbl : NBitLong) = apply(nbl.bits, 0l)
  }
  implicit object NBitLongIsIntegral extends NBitLongIsOrderedC with Integral[NBitLong] {
    def plus(x : NBitLong, y : NBitLong) : NBitLong = {
      require(x.bits == y.bits)
      new NBitLong(x.bits, signContract(x.bits, x.value + y.value))
    }
    def minus(x : NBitLong, y : NBitLong) : NBitLong = {
      require(x.bits == y.bits)
      new NBitLong(x.bits, signContract(x.bits, x.value - y.value))
    }
    def times(x : NBitLong, y : NBitLong) : NBitLong = {
      require(x.bits == y.bits)
      new NBitLong(x.bits, signContract(x.bits, x.value * y.value))
    }
    def quot(x : NBitLong, y : NBitLong) : NBitLong = {
      require(x.bits == y.bits)
      new NBitLong(x.bits, signContract(x.bits, x.value / y.value))
    }
    def rem(x : NBitLong, y : NBitLong) : NBitLong = {
      require(x.bits == y.bits)
      new NBitLong(x.bits, signContract(x.bits, x.value % y.value))
    }
    def negate(x : NBitLong) : NBitLong = new NBitLong(x.bits, signContract(x.bits, -x.getValue))
    def fromInt(x : Int) : NBitLong = {
      val boundedBits = implicitly[BoundedBits[Int]]
      apply(boundedBits.bits, x.toLong)
    }
    def toInt(x : NBitLong) : Int = x.getValue.toInt
    def toLong(x : NBitLong) : Long = x.getValue
    def toFloat(x : NBitLong) : Float = x.getValue.toFloat
    def toDouble(x : NBitLong) : Double = x.getValue.toDouble
  }
  implicit object NBitLongIsLongCastable extends Castable[NBitLong, (Int, Long)] {
    def apply(x : NBitLong) : (Int, Long) = (x.bits, x.value)
  }
  implicit object NBitLongIsNBitLongCastable extends Castable[(Int, Long), NBitLong] {
    def apply(x : (Int, Long)) : NBitLong = new NBitLong(x._1, x._2)
  }/*
  implicit val arbitraryNBitLong : Arbitrary[NBitLong] = Arbitrary {
    for{
      long <- Arbitrary.arbitrary[Long]
      bits <- Arbitrary.arbitrary[Int]
      val bits_ = boundBits(bits)
    } yield NBitLong(bits_, bound(long, bits_))
  }
  def arbitraryNBitLong(bits : Int) : Arbitrary[NBitLong] = Arbitrary {
    for(long <- Arbitrary.arbitrary[Long]) yield NBitLong(bits, bound(long, bits))
  }*/
}