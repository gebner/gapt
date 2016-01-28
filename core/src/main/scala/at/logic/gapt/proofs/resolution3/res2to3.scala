package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr.{ LambdaExpression, HOLAtomConst }
import at.logic.gapt.expr.hol.structuralCNF.Justification
import at.logic.gapt.proofs.{ resolution => res2, HOLSequent, HOLClause, Ant }
import collection.mutable

object res2to3 {

  def apply( p: res2.ResolutionProof, endSequent: HOLSequent, justifications: Map[HOLClause, Justification], definitions: Map[HOLAtomConst, LambdaExpression] ): ResolutionProof = {
    val ic = for ( ( cls, just ) <- justifications ) yield res2.InputClause( cls ) ->
      justificationsToResolution( endSequent, cls, just, definitions )
    apply( p, ic )
  }

  def apply( p: res2.ResolutionProof, ic: res2.InputClause => ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[res2.ResolutionProof, ResolutionProof]()

    def f( p: res2.ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case p: res2.InputClause            => ic( p )
      case res2.TautologyClause( atom )   => Taut( atom )
      case res2.ReflexivityClause( term ) => Refl( term )
      case res2.Instance( p1, subst )     => Subst( f( p1 ), subst )
      case res2.Factor( p1, i1, i2 ) =>
        val q1 = f( p1 )
        val js = q1.conclusion.indicesWhere { _ == p1.conclusion( i1 ) }.filter { _ sameSideAs i1 }
        Fac( q1, js( 0 ), js( 1 ) )
      case res2.Resolution( p1, i1, p2, i2 ) =>
        val q1 = f( p1 )
        val q2 = f( p2 )
        Res( q1, q1.conclusion.indexOfInSuc( p1.conclusion( i1 ) ),
          q2, q2.conclusion.indexOfInAnt( p2.conclusion( i2 ) ) )
      case p @ res2.Paramodulation( p1, i1, p2, i2, pos, ltr ) =>
        val q1 = f( p1 )
        val q2 = f( p2 )

        val q0 = EqAx( p1.conclusion( i1 ), p2.conclusion( i2 ), pos, ltr )
        val q3 = Res( q1, q1.conclusion.indexOfInSuc( q0.equation ), q0, Ant( 0 ) )
        Res( q2, q2.conclusion.indexOfInSuc( q0.formula ), q3, q3.conclusion.indexOfInAnt( q0.formula ) )
    } ) ensuring { res => res.conclusion multiSetEquals p.conclusion }

    f( p )
  }

}
