package gapt.examples.prime

import gapt.expr._
import gapt.expr.formula.{ All, Iff }
import gapt.proofs.ceres.CERES
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.expansion.ETWeakQuantifier
import gapt.proofs.lk.transformations.{ eliminateDefinitions, indexCutAtoms, skolemizeLK }
import gapt.proofs.lk.util.AtomicExpansion
import gapt.provers.vampire.Vampire
import gapt.utils.{ Multiset, ZZMPolynomial }

object furstenbergWitnessCERES {

  def apply( n: Int ): ( Expr, ImmutableContext ) = {
    val primeInst = furstenberg( n )
    implicit val ctx = primeInst.ctx.newMutable

    ctx.addSkolemSym( le"λk_4 ∃m (k_4:nat) = ((m:nat) + (1:nat): nat)", "pred" )
    ctx.addSkolemSym( le"λm_16 ∃l (PRIME(l:nat) ∧ DIV(l, m_16:nat))", "primediv_of" )

    val p0 = eliminateDefinitions( skolemizeLK( primeInst.proof, proofTheoretic = false ) )

    val p = indexCutAtoms.removingEquality( AtomicExpansion( p0 ) )
    val p6 = CERES.expansionProof( p, prover = Vampire.extendToManySortedViaErasure )

    val Seq( Seq( witness ) ) = p6.expansionSequent.antecedent.collect {
      case ETWeakQuantifier( All( _, Iff( _, _ ) ), insts ) =>
        insts.keys.toSeq.filter {
          case App( Const( "p", _, _ ), _ ) => false
          case _                            => true
        }
    }

    def lowerBound( p: ZZMPolynomial[Expr] ): Int =
      p.coeffsMap.map { case ( _, c ) => require( c >= 0 ); c }.sum

    def toMPolynomial( e: Expr ): ZZMPolynomial[Expr] =
      e match {
        case App( Const( "p", _, _ ), _ ) => e
        case Apps( Const( "*", _, _ ), Seq( a, b ) ) =>
          toMPolynomial( a ) * toMPolynomial( b )
        case Apps( Const( "+", _, _ ), Seq( a, b ) ) =>
          toMPolynomial( a ) + toMPolynomial( b )
        case Apps( Const( "pred", _, _ ), Seq( a ) ) =>
          val sub = toMPolynomial( a )
          require( lowerBound( sub ) >= 1, s"not positive: $sub\ncould be: ${lowerBound( sub )}" )
          sub + ( -1 )
        case Apps( Const( "s", _, _ ), Seq( a ) ) =>
          toMPolynomial( a ) + 1
        case Const( "0", _, _ ) => 0
      }
    def toExprN( n: Int ): Expr =
      if ( n == 0 ) le"0"
      else if ( n < 0 ) le"pred ${toExprN( n + 1 )}"
      else le"s ${toExprN( n - 1 )}"
    def toExprM( m: Multiset[Expr] ): Expr =
      m.toSeq.reduceOption( ( a, b ) => le"$a * $b" ).getOrElse( le"s(0)" )
    def toExprP( p: ZZMPolynomial[Expr] ): Expr =
      p.coeffsMap.map {
        case ( mon, 1 ) => toExprM( mon )
        case ( mon, v ) => le"${toExprN( v )} * ${toExprM( mon )}"
      }.reduceOption( ( a, b ) => le"$a + $b" ).getOrElse( le"0" )

    val witness2 = witness match {
      case App( c @ Const( "primediv_of", _, _ ), arg ) =>
        App( c, toExprP( toMPolynomial( arg ) ) )
    }

    ( witness2, ctx.toImmutable )
  }
}
