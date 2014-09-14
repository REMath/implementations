package cc.sven.bench

import cc.sven.intset._
import cc.sven.misc.Misc._

object Bench extends testing.Benchmark {
  println("building data")
  def generateData(num : Int) = {
    var i = 0
    var n = num
    var res = !IntSet[Int]()
    var set = Set[Int]()
    while(i < num) {
      val random = res.randomElement()
      res -= random
      set += random
      i += 1
    }
    res = !res
    println("Controlset size: " + set.size.toString)
    println("IntSet size: " + res.sizeBigInt.toString)
    //set
    res
  }
  val data = generateData(1000)
  println("running banchmark")
  def run {
    //val res = cartesianProduct(data, data).map((x) => x._1 + x._2)
    //println("Intset size: " + res.size)
    val res = data plus data
    println("Intset size: " + res.sizeBigInt)
  }
}