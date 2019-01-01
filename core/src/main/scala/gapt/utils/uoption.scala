package gapt.utils
import language.higherKinds

/**
 * Unboxed option type similar to `Option[T]`.
 *
 * Note that `USome(UNone()) == UNone()` and `USome(null) == UNone()`.
 */
class UOption[+T]( private val t: T ) extends AnyVal {
  def isDefined: Boolean = !isEmpty
  def isEmpty: Boolean = t == null
  def unsafeGet: T = t
  def get: T = if ( isDefined ) unsafeGet else throw new NoSuchElementException
  def getOrElse[S >: T]( t: => S ): S = if ( isDefined ) unsafeGet else t
  def map[S]( f: T => S ): UOption[S] = if ( isDefined ) USome( f( unsafeGet ) ) else UNone()
  def flatMap[S]( f: T => UOption[S] ): UOption[S] = if ( isDefined ) f( unsafeGet ) else UNone()
  def foreach( f: T => Unit ): Unit = if ( isDefined ) f( unsafeGet )
  def toOption: Option[T] = if ( isDefined ) Some( unsafeGet ) else None
}

object UOption {
  def apply[T]( t: T ): UOption[T] = new UOption( t )
  def ofOption[T]( t: Option[T] ): UOption[T] =
    if ( t.isDefined ) USome( t.get ) else UNone()
}

object USome {
  def apply[T]( t: T ): UOption[T] = new UOption( t )
  def unapply[T]( t: UOption[T] ): UOption[T] = t
}

object UNone {
  def apply[T](): UOption[T] =
    new UOption[Null]( null ).asInstanceOf[UOption[T]]
}

