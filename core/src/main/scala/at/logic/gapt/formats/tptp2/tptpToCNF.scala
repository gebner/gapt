package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.formats.tptp2.definitions.TptpFile
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.resolution.{ Clausifier, Input, ResolutionProof }
import at.logic.gapt.utils.NameGenerator

object tptpToCNF {
  def apply( tptpFile: TptpFile ): Set[ResolutionProof] = {
    val clausifier = new Clausifier( propositional = false, structural = true,
      nameGen = new NameGenerator( Set() ) // FIXME
    )

    tptpFile foreach {
      case TptpFormulaInput( "cnf", _, _, formula, _ ) =>
        CNFp.toClauseList( formula ) match {
          case Seq( clause ) => clausifier expand Input( clause )
        }
      case TptpFormulaInput( _, _, "conjecture", formula, _ ) =>
        clausifier expand Input( formula +: Sequent() )
      case TptpFormulaInput( _, _, _, formula, _ ) =>
        clausifier expand Input( Sequent() :+ formula )
      case input => throw new IllegalArgumentException( input.toString )
    }

    clausifier.cnf.toSet
  }

}
