package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr.{HOLAtom, Substitution, syntacticMatching, clauseSubsumption}
import at.logic.gapt.proofs.{ Ant, Suc, Sequent, HOLSequent }
import at.logic.gapt.proofs.expansion._
import collection.mutable

object ResolutionToExpansionProof {

  def apply( p: ResolutionProof ): ExpansionProofWithCut = {
    def f( p: ResolutionProof, subst: Substitution )(es: ExpansionSequent ): ExpansionProofWithCut = ( p match {
      case Inp( sequent )                 => ExpansionProof( es.swapped )
      case Refl( _ ) | EqAx( _, _, _, _ ) => ExpansionProof( Sequent() )
      case Taut( formula )                => ExpansionProofWithCut( Seq( ETImp( es( Ant( 0 ) ), es( Suc( 0 ) ) ) ), Sequent() )

      case Fac( p1, i1, i2 )              => f( p1, subst )( p.occConnectors( 0 ).parent( es ) )
      case Subst( p1, subst_ ) =>
        subst( f( p1, subst compose subst_ )( es ) )

      case TopL( p1, i )    => f(p1,subst)( es.insertAt( i, ETTop( true ) ) )
      case BottomR( p1, i ) => f(p1,subst)( es.insertAt( i, ETBottom( false ) ) )
      case NegL( p1, i )    => f(p1,subst)( es.delete( es.indices.last ).insertAt( i, ETNeg( es.elements.last ) ) )
      case NegR( p1, i )    => f(p1,subst)( es.delete( es.indices.head ).insertAt( i, ETNeg( es.elements.head ) ) )
      case AndL( p1, i ) =>
        val Seq( i1, i2 ) = es.indices.take( 2 )
        f(p1,subst)( es.delete( i1, i2 ).insertAt( i, ETAnd( es( i1 ), es( i2 ) ) ) )
      case OrR( p1, i ) =>
        val Seq( i1, i2 ) = es.indices.takeRight( 2 )
        f(p1,subst)( es.delete( i1, i2 ).insertAt( i, ETOr( es( i1 ), es( i2 ) ) ) )
      case ImpR( p1, i ) =>
        val i1 = es.indices.head
        val i2 = es.indices.last
        f(p1,subst)( es.delete( i1, i2 ).insertAt( i, ETImp( es( i1 ), es( i2 ) ) ) )
      case p @ AndR( p1, i, w ) =>
        f(p1,subst)( es.delete( es.indices.last ).insertAt(
          i,
          if ( !w ) ETAnd( es.elements.last, ETWeakening( p.right, false ) )
          else ETAnd( ETWeakening( p.left, false ), es.elements.last )
        ) )
      case p @ OrL( p1, i, w ) =>
        f(p1,subst)( es.delete( es.indices.head ).insertAt(
          i,
          if ( !w ) ETOr( es.elements.head, ETWeakening( p.right, true ) )
          else ETOr( ETWeakening( p.left, true ), es.elements.head )
        ) )
      case p @ ImpL( p1, i, true ) =>
        f(p1,subst)( es.delete( es.indices.head ).insertAt( i, ETImp( ETWeakening( p.left, false ), es.elements.head ) ) )
      case p @ ImpL( p1, i, false ) =>
        f(p1,subst)( es.delete( es.indices.last ).insertAt( i, ETImp( es.elements.last, ETWeakening( p.right, true ) ) ) )

      case p @ WeakQ( p1, i, v ) =>
        f(p1,subst)( p.occConnectors( 0 ).parent( es ).updated( i, ETWeakQuantifier( subst(p1.conclusion( i )), Map( subst( v ) -> es( p.mainIndices.head ) ) ) ) )
      case p @ Sk( p1, i, skt ) =>
        f(p1,subst)( p.occConnectors( 0 ).parent( es, ETSkolemQuantifier( p1.conclusion( i ), skt, es( p.mainIndices.head ) ) ) )

      case Res( p1, i1, p2, i2 ) =>
        val resAtom = p1.conclusion( i1 )
        val ep1 = f(p1,subst)( p.occConnectors( 0 ).parent( es, ETAtom( subst(resAtom), false ) ) )
        val ep2 = f(p2,subst)( p.occConnectors( 1 ).parent( es, ETAtom( subst(resAtom), true ) ) )

        eliminateMerges( ExpansionProofWithCut(
          ep1.cuts ++ ep2.cuts,
          Sequent( ( ep1.expansionSequent ++ ep2.expansionSequent ).elements.groupBy { e => e.shallow -> e.polarity }.mapValues { es => ETMerge( es ) }.toSeq.map { pe => pe._2 -> pe._1._2 } )
        ) )
    } ) ensuring { _ => true }

    f( p, Substitution() )( Sequent() )
  }

}
