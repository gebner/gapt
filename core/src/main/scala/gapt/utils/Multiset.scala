package gapt.utils

class PosInt private ( val toInt: Int ) extends AnyVal {
  def *( n: PosInt ): PosInt = new PosInt( toInt * n.toInt )
  def +( n: PosInt ): PosInt = new PosInt( toInt + n.toInt )
  def ==( n: Int ): Boolean = toInt == n

  def isEmpty = false
  def get = toInt
}
object PosInt {
  implicit def apply( n: Int ): PosInt = {
    require( n > 0 )
    new PosInt( n )
  }
  def unapply( n: PosInt ): PosInt = n
}

case class Multiset[T]( countingMap: Map[T, PosInt] = Map[T, PosInt]() ) extends ( T => Int ) {
  def apply( t: T ): Int = countingMap.get( t ).fold( 0 )( _.toInt )

  def +( that: Multiset[T] ): Multiset[T] =
    Multiset( Map() ++
      ( this.countingMap.keySet union that.countingMap.keySet ).view.
      map( k => k -> ( this( k ) + that( k ) ) ) )

  def toSeq: Seq[T] =
    countingMap.view.flatMap {
      case ( t, n ) => List.fill( n.toInt )( t )
    }.toList

  override def toString(): String =
    countingMap.map {
      case ( k, PosInt( 1 ) ) => k.toString
      case ( k, n )           => s"$k^$n"
    }.mkString( "{", ",", "}" )
}
