package cc.sven.memoized

import com.google.common.cache.CacheBuilder
import collection.JavaConversions._
import java.util.concurrent.TimeUnit

class Memoized[-D <: AnyRef, +R <: AnyRef](cache: scala.collection.concurrent.Map[D, R], f: D => R) extends (D => R) {
  def this(f: D => R) = this(mapAsScalaConcurrentMap(
    CacheBuilder.newBuilder()
      .softValues()
      /*XXX check this, especially with combination of maximum size, what about weak keys? then, caching only works for arguments that exist?
       * what happens to the keys if soft value is collected? - are automatically evicted according to documentation
       * play around with configuration - what is most efficient?
       */
      .maximumSize(10000)
      .expireAfterAccess(10, TimeUnit.MINUTES)
      .build().asMap()), f)
  def apply(x: D): R = cache.getOrElseUpdate(x, f(x))
}

object Memoized {
  def apply[D <: AnyRef, R <: AnyRef](f: D => R) = new Memoized[D, R](f)
  def apply[D <: AnyRef, R <: AnyRef](f: (D, D => R) => R) = {
    var recF: D => R = null
    recF = new Memoized[D, R](f(_, recF(_)))
    recF
  }
}