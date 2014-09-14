package cc.sven.misc

//For use from java side... they do not have that... stupid...
//XXX export scala's version?
class Pair[A, B](a : A, b : B) {
  def _1 = a
  def _2 = b
}
object Pair {
  def apply[A, B](a : A, b : B) = new Pair(a, b)
}

object Implicits {
  def pairToTuple2[A, B](p : Pair[A, B]) : (A, B) = (p._1, p._2)
  def tuple2ToPair[A, B](p : (A, B)) : Pair[A, B] = Pair(p._1, p._2)
}