package at.logic.gapt.proofs.lksk

import at.logic.gapt.expr.BetaReduction.{ betaNormalize => normalize }
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.substitution.Substitution
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk.{ ProofTransformationUtils, applySubstitution => LKapplySubstitution }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk.{ BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.lksk._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

object applySubstitution extends at.logic.gapt.utils.logging.Logger {
  import at.logic.gapt.proofs.lk.ProofTransformationUtils.computeMap

  def toLabelledSequent( so: OccSequent ) = new LabelledOccSequent(
    so.antecedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ),
    so.succedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] )
  )

  def apply( proof: LKProof, subst: Substitution ): ( LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence] ) =
    proof match {
      case Axiom( so: LabelledOccSequent ) => {
        val ant_occs = so.l_antecedent
        val succ_occs = so.l_succedent
        val seq = HOLSequent( ant_occs.map( fo => normalize( subst( fo.formula ) ) ), succ_occs.map( fo => normalize( subst( fo.formula ) ) ) )
        val labels_ant = ant_occs.map( fo => fo.skolem_label.map( t => subst( t ) ) ).toList
        val labels_succ = succ_occs.map( fo => fo.skolem_label.map( t => subst( t ) ) ).toList
        val ( a, ( antecedent, succedent ) ) = Axiom.createDefault( seq, Tuple2( labels_ant, labels_succ ) )

        require( antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one" )
        require( succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one" )
        val map = Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]() ++
          ( ant_occs zip antecedent ) ++ ( succ_occs zip succedent )

        ( a, map )
      }
      case WeakeningLeftRule( p, s, m ) => {
        val new_parent = apply( p, subst )
        val new_proof = WeakeningLeftRule.createDefault( new_parent._1, subst( m.formula ), m.skolem_label.map( e => normalize( subst.apply( e ) ) ) )
        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Tuple2( m, new_proof.prin.head ) )
      }
      case WeakeningRightRule( p, s, m ) => {
        val new_parent = apply( p, subst )
        val new_proof = WeakeningRightRule.createDefault( new_parent._1, subst( m.formula ), m.skolem_label.map( e => normalize( subst.apply( e ) ) ) )
        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Tuple2( m, new_proof.prin.head ) )
      }
      case ForallSkLeftRule( p, s, a, m, t ) => {
        val new_parent = apply( p, subst )
        val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2( a ), normalize( subst( m.formula ) ), normalize( subst( t ) ), !m.skolem_label.contains( t ) )

        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkRightRule( p, s, a, m, t ) => {
        val new_parent = apply( p, subst )
        val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2( a ), normalize( subst( m.formula ) ), normalize( subst.apply( t ) ), !m.skolem_label.contains( t ) )

        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallSkRightRule( p, s, a, m, t ) => {
        val new_parent = apply( p, subst )
        val new_proof = ForallSkRightRule( new_parent._1, new_parent._2( a ), normalize( subst( m.formula ) ), normalize( subst.apply( t ) ) )
        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkLeftRule( p, s, a, m, t ) => {
        val new_parent = apply( p, subst )
        val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2( a ), normalize( subst( m.formula ) ), normalize( subst.apply( t ) ) )
        val es = toLabelledSequent( p.root )
        ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      // casting is necessary, since Map is not covariant
      case UnaryLKProof( _, p, _, _, _ ) => LKapplySubstitution.handleRule(
        proof,
        apply( p, subst ).asInstanceOf[( LKProof, Map[FormulaOccurrence, FormulaOccurrence] )] :: Nil, subst
      ).asInstanceOf[( LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence] )]
      case BinaryLKProof( _, p1, p2, _, _, _, _ ) =>
        LKapplySubstitution.handleRule( proof, ( apply( p1, subst ) :: apply( p2, subst ) :: Nil ).asInstanceOf[List[( LKProof, Map[FormulaOccurrence, FormulaOccurrence] )]], subst ).asInstanceOf[( LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence] )]
    }
}
