package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr.{ HOLFormula, LambdaExpression, HOLAtomConst }
import at.logic.gapt.proofs.{ Ant, Suc, OccConnector }
import at.logic.gapt.proofs.lk.DefinitionElimination
import collection.mutable

object eliminateDefsRes {

  def apply( p: ResolutionProof, defs: Map[HOLAtomConst, LambdaExpression] ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ( ResolutionProof, OccConnector[HOLFormula] )]()
    val delim = DefinitionElimination( defs.toMap )

    def f( p: ResolutionProof ): ( ResolutionProof, OccConnector[HOLFormula] ) = memo.getOrElseUpdate( p, p match {
      case Inp( seq )   => ( Inp( seq ), OccConnector( p.conclusion ) )
      case Refl( term ) => ( Refl( term ), OccConnector( p.conclusion ) )
      case Taut( form ) =>
        val q = Taut( delim( form ) )
        ( q, OccConnector( q.conclusion, p.conclusion, q.conclusion.indicesSequent map { Seq( _ ) } ) )
      case p: EqAx =>
        val q = p.copy( formula = delim( p.formula ) )
        ( q, OccConnector( q.conclusion, p.conclusion, q.conclusion.indicesSequent map { Seq( _ ) } ) )
      case Subst( p1, subst ) =>
        val ( q1, o1 ) = f( p1 )
        val q = Subst( q1, subst )
        ( q, OccConnector( q.conclusion, p.conclusion, o1.parentsSequent ) )
      case Fac( p1, i1, i2 ) =>
        val ( q1, o1 ) = f( p1 )
        val q = Fac( q1, o1 child i1, o1 child i2 )
        ( q, q.occConnectors( 0 ) * o1 * p.occConnectors( 0 ).inv )
      case Res( p1, i1, p2, i2 ) =>
        val ( q1, o1 ) = f( p1 )
        val ( q2, o2 ) = f( p2 )
        val q = Res( q1, o1.child( i1 ).asInstanceOf[Suc], q2, o2.child( i2 ).asInstanceOf[Ant] )
        ( q, q.occConnectors( 0 ) * o1 * p.occConnectors( 0 ).inv + q.occConnectors( 1 ) * o2 * p.occConnectors( 1 ).inv )
      case Def( p1, i1, _ ) =>
        val ( q1, o1 ) = f( p1 )
        ( q1, o1 * p.occConnectors( 0 ).inv )
      case p: OneFormulaRule =>
        val ( q1, o1 ) = f( p.subProof )
        val q = p.copyInference( q1, o1 child p.idx )
        val o = q.occConnectors( 0 ) * o1 * p.occConnectors( 0 ).inv
        ( q, o.copy( parentsSequent = ( q.mainIndices zip p.mainIndices ).foldLeft( o.parentsSequent )( ( ps, n ) => ps.updated( n._1, Seq( n._2 ) ) ) ) )
    } ) ensuring { res =>
      res._2.parentsSequent foreach { ps =>
        require( ps.size == 1 )
      }
      for ( ( f, i ) <- res._1.conclusion.zipWithIndex; j = res._2 parent i; g = delim( p.conclusion( j ) ) )
        require( g == f )
      true
    }

    f( p )._1
  }

}
