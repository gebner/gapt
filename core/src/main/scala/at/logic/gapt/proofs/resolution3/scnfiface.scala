package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ Definition, ProjectionFromEndSequent, Justification }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.DefinitionElimination

object justificationsToResolution {
  def apply( endSequent: HOLSequent, clause: HOLClause, justification: Justification, definitions: Map[HOLAtomConst, LambdaExpression] ): ResolutionProof = justification match {
    case ProjectionFromEndSequent( proj, indexInES ) =>
      val p = Inp( if ( indexInES isSuc ) endSequent( indexInES ) +: Sequent() else Sequent() :+ endSequent( indexInES ) )
      expansionTree2Res( proj.elements.head, Def( p, p.conclusion.indices.head, proj.elements.head.shallow ), p.conclusion.indices.head )
    case Definition( newAtom, expansion ) =>
      //      expansionTree2Res( expansion, Def(
      //        Taut( expansion.shallow ),
      //        if ( expansion.polarity ) Suc( 0 ) else Ant( 0 ),
      //        newAtom
      //      ),
      //        if ( expansion.polarity ) Ant( 0 ) else Suc( 0 ) )

      var p = expansionTree2Res( expansion, Def( Taut( newAtom ), if ( expansion.polarity ) Ant( 0 ) else Suc( 0 ), DefinitionElimination( definitions.toMap )( newAtom ) ),
        if ( expansion.polarity ) Ant( 0 ) else Suc( 0 ) )
      for ( ( by @ Apps( d: HOLAtomConst, args ), i ) <- clause.zipWithIndex if definitions contains d if by != newAtom ) {
        val j = p.conclusion.indexOfPol( BetaReduction.betaNormalize( definitions( d )( args: _* ) ), i.isSuc )
        p = Def( p, j, by )
      }
      p
  }

  def expansionTree2Res( et: ExpansionTree, p: ResolutionProof, idx: SequentIndex ): ResolutionProof = ( ( et, idx ) match {
    case ( ETAtom( _, _ ), _ )       => p

    case ( ETTop( _ ), idx: Ant )    => TopL( p, idx )
    case ( ETBottom( _ ), idx: Suc ) => BottomR( p, idx )
    case ( ETNeg( aux ), idx: Ant )  => expansionTree2Res( aux, NegL( p, idx ), Suc( p.conclusion.succedent.size ) )
    case ( ETNeg( aux ), idx: Suc )  => expansionTree2Res( aux, NegR( p, idx ), Ant( 0 ) )
    case ( ETAnd( l, r ), idx: Ant ) =>
      val p1 = AndL( p, idx )
      val p2 = expansionTree2Res( l, p1, Ant( 0 ) )
      expansionTree2Res( r, p2, p2.conclusion.indexOfInAnt( p1.right ) )
    case ( ETOr( l, r ), idx: Suc ) =>
      val p1 = OrR( p, idx )
      val p2 = expansionTree2Res( l, p1, p1.conclusion.indexOfInSuc( p1.left ) )
      expansionTree2Res( r, p2, p2.conclusion.indexOfInSuc( p1.right ) )
    case ( ETImp( l, r ), idx: Suc ) =>
      val p1 = ImpR( p, idx )
      val p2 = expansionTree2Res( l, p1, Ant( 0 ) )
      expansionTree2Res( r, p2, p2.conclusion.indexOfInSuc( p1.right ) )
    case ( ETAnd( l, ETWeakening( _, _ ) | ETTop( _ ) ), idx: Suc ) =>
      expansionTree2Res( l, AndR( p, idx, false ), Suc( p.conclusion.succedent.size - 1 ) )
    case ( ETAnd( ETWeakening( _, _ ) | ETTop( _ ), r ), idx: Suc ) =>
      expansionTree2Res( r, AndR( p, idx, true ), Suc( p.conclusion.succedent.size - 1 ) )
    case ( ETOr( l, ETWeakening( _, _ ) ), idx: Ant ) =>
      expansionTree2Res( l, OrL( p, idx, false ), Ant( 0 ) )
    case ( ETOr( ETWeakening( _, _ ), r ), idx: Ant ) =>
      expansionTree2Res( r, OrL( p, idx, true ), Ant( 0 ) )
    case ( ETImp( l, ETWeakening( _, _ ) ), idx: Ant ) =>
      expansionTree2Res( l, ImpL( p, idx, false ), Suc( p.conclusion.succedent.size ) )
    case ( ETImp( ETWeakening( _, _ ), r ), idx: Ant ) =>
      expansionTree2Res( r, ImpL( p, idx, true ), Ant( 0 ) )

    case ( ETWeakQuantifier( sh, inst ), _ ) if inst.size == 1 =>
      val ( v: Var, child ) = inst.head
      val p_ = WeakQ( p, idx, v )
      expansionTree2Res( child, p_, p_.mainIndices.head )

    case ( ETSkolemQuantifier( sh, skt, child ), _ ) =>
      val p_ = Sk( p, idx, skt )
      expansionTree2Res( child, p_, p_.mainIndices.head )
  } ) ensuring { _ => true }
}