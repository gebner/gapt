package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ SequentConnector, Sequent, SequentIndex }
import at.logic.gapt.utils.NameGenerator

object containsEqualityReasoning {
  /**
   * @param proof An LKProof.
   * @return true iff this proof contains a reflexivity axiom or an equational inference
   */
  def apply( proof: LKProof ): Boolean =
    proof.subProofs.exists {
      case ReflexivityAxiom( _ )           => true
      case EqualityLeftRule( _, _, _, _ )  => true
      case EqualityRightRule( _, _, _, _ ) => true
      case _                               => false
    }
}

object containsDefinitionRules {
  def apply( proof: LKProof ): Boolean =
    proof.subProofs.exists {
      case DefinitionLeftRule( _, _, _ ) | DefinitionRightRule( _, _, _ ) => true
      case _ => false
    }
}

object freeVariablesLK {
  def apply( p: LKProof ): Set[Var] = p match {
    case StrongQuantifierRule( subProof, aux, eigen, quant, isSuc ) =>
      apply( subProof ) - eigen
    case InductionRule( cases, main, term ) =>
      freeVariables( p.conclusion ) ++ freeVariables( term ) ++ ( cases flatMap { c =>
        apply( c.proof ) -- c.eigenVars
      } )
    case _ =>
      freeVariables( p.conclusion ) ++ p.immediateSubProofs.flatMap( apply )
  }
}

object groundFreeVarsLK {
  def getMap( p: LKProof ) = {
    val nameGen = rename.awayFrom( containedNames( p ) )
    for ( v @ Var( n, t ) <- freeVariablesLK( p ) ) yield v -> Const( nameGen fresh n, t )
  }

  def apply( p: LKProof ): LKProof = Substitution( getMap( p ) )( p )

  def wrap[I, O]( p: LKProof )( f: LKProof => I )( implicit ev: Replaceable[I, O] ): O = {
    val grounding = getMap( p )
    TermReplacement.hygienic( f( Substitution( grounding )( p ) ), grounding.map( _.swap ).toMap )
  }
}

object cutFormulas {
  def apply( proof: LKProof ) = proof.treeLike.postOrder.flatMap(
    {
      case CutRule( p, o, _, _ ) => List( p.conclusion( o ) )
      case _                     => List()
    }
  ).toSet
}

object isRegular {
  /**
   * Tests for regularity by checking whether all eigenvariables are distinct.
   *
   * @param proof An LKProof.
   * @return true iff proof is regular.
   */
  def apply( proof: LKProof ): Boolean = {
    val eigenVars = for ( Eigenvariable( v ) <- proof.treeLike.postOrder ) yield v
    eigenVars == eigenVars.distinct
  }
}

/**
 * Proof regularization
 *
 */
object regularize {
  /**
   * Renames all eigenvariables in a proof so that it becomes regular.
   *
   * @param proof An LKProof.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof ): LKProof =
    new regularize( rename.awayFrom( freeVariablesLK( proof ) ) ).apply( proof, () )
}

class regularize( nameGen: NameGenerator ) extends LKVisitor[Unit] {

  protected override def visitForallRight( proof: ForallRightRule, arg: Unit ) = {
    val ForallRightRule( subProof, aux, eigen, quant ) = proof
    val eigenNew = nameGen.fresh( eigen )
    val ( subProofNew, subConnector ) = recurse( Substitution( eigen -> eigenNew )( subProof ), () )
    val proofNew = ForallRightRule( subProofNew, aux, eigenNew, quant )
    ( proofNew, proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv )
  }

  protected override def visitExistsLeft( proof: ExistsLeftRule, arg: Unit ) = {
    val ExistsLeftRule( subProof, aux, eigen, quant ) = proof
    val eigenNew = nameGen.fresh( eigen )
    val ( subProofNew, subConnector ) = recurse( Substitution( eigen -> eigenNew )( subProof ), () )
    val proofNew = ExistsLeftRule( subProofNew, aux, eigenNew, quant )
    ( proofNew, proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv )
  }

  protected override def visitInduction( proof: InductionRule, arg: Unit ) = {
    val InductionRule( cases, main, term ) = proof

    val newQuant = nameGen.fresh( proof.quant )

    val newCasesConnectors = cases map { c =>
      val renaming = for ( ev <- c.eigenVars ) yield ev -> nameGen.fresh( ev )
      val ( subProofNew, subConnector ) = recurse( Substitution( renaming )( c.proof ), () )
      c.copy( proof = subProofNew, eigenVars = c.eigenVars map renaming.toMap ) -> subConnector
    }

    val ( casesNew, subConnectors ) = newCasesConnectors.unzip
    val proofNew = InductionRule( casesNew, proof.formula, term )
    val subConnectors_ = for ( ( c1, c2, c3 ) <- ( proofNew.occConnectors, subConnectors, proof.occConnectors ).zipped ) yield c1 * c2 * c3.inv
    val connector = if ( subConnectors_.isEmpty ) SequentConnector( proofNew.endSequent ) else subConnectors_.reduceLeft( _ + _ )

    ( proofNew, connector )
  }

}
