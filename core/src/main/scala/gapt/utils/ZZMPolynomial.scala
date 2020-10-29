package gapt.utils

/** Multivariate polynomial over the integers with variables from V. */
case class ZZMPolynomial[V] private ( coeffsMap: Map[Multiset[V], Int] ) {
  def coeff( v: Multiset[V] ): Int = coeffsMap.getOrElse( v, 0 )

  def +( that: ZZMPolynomial[V] ): ZZMPolynomial[V] = ZZMPolynomial {
    for ( m <- this.coeffsMap.keySet union that.coeffsMap.keySet )
      yield m -> ( this.coeff( m ) + that.coeff( m ) )
  }

  def *( that: ZZMPolynomial[V] ): ZZMPolynomial[V] = ZZMPolynomial {
    for ( ( m1, c1 ) <- this.coeffsMap.view; ( m2, c2 ) <- that.coeffsMap.view )
      yield ( m1 + m2 ) -> ( c1 * c2 )
  }
}

object ZZMPolynomial {
  implicit def fromScalar[V]( n: Int ): ZZMPolynomial[V] =
    ZZMPolynomial( Map( Multiset[V]() -> n ) )

  implicit def fromVariable[V]( v: V ): ZZMPolynomial[V] =
    ZZMPolynomial( Map( Multiset[V]( Map( v -> 1 ) ) -> 1 ) )

  def apply[V]( coeffs: Iterable[( Multiset[V], Int )] ): ZZMPolynomial[V] =
    new ZZMPolynomial( ( Map() ++ coeffs.view.
      groupBy( _._1 ).
      view.mapValues( _.map( _._2 ).sum ) ).
      filter( _._2 != 0 ) )
}
