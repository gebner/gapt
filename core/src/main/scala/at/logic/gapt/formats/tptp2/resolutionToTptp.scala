package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution._

object resolutionToTptp {
  def fofOrCnf( label: String, role: FormulaRole, inf: ResolutionProof, annotations: Option[Annotations] ): TptpInput = {
    val disj = if ( inf.assertions.isEmpty ) inf.conclusion.toDisjunction
    else inf.conclusion.toDisjunction | inf.assertions.toDisjunction
    if ( inf.conclusion.forall( _.isInstanceOf[HOLAtom] ) ) {
      val ( _, disj_ ) = tptpToString.renameVars( freeVariables( disj ).toSeq, disj )
      CnfFormula( label, role, disj, annotations )
    } else {
      FofFormula( label, role, disj.asInstanceOf[FOLFormula], annotations )
    }
  }

  def convertInference( labelMap: Map[ResolutionProof, String], inf: ResolutionProof ): TptpInput = {
    val label = labelMap( inf )
    inf match {
      case Input( sequent ) =>
        fofOrCnf( label, Axiom, inf, None )

      case AvatarComponentIntro( comp @ AvatarNonGroundComp( splAtom, defn, vars ) ) =>
        fofOrCnf( label, Definition, inf, Some( Annotations(
          InternalSource( "avatar_non_ground_component", Seq() ),
          Seq()
        ) ) )

      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile( _ == '_' )
        fofOrCnf( label, Plain, inf, Some( Annotations( InferenceRecord( inferenceName, Seq(),
          p.immediateSubProofs.map( sp => ParentInfo( DagSource( labelMap( sp ) ), Seq() ) ) ), Seq() ) ) )
    }
  }

  def apply( proof: ResolutionProof ): Seq[TptpInput] = {
    val labelMap = ( for ( ( p, i ) <- proof.dagLike.postOrder.zipWithIndex ) yield p -> s"p$i" ).toMap
    proof.dagLike.postOrder map { convertInference( labelMap, _ ) }
  }
}
