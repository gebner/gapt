package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr.{ FOLFormula, freeVariables }
import at.logic.gapt.formats.tptp2.definitions.TptpFile
import at.logic.gapt.proofs.HOLSequent

object sequentToTPTP {
  def apply( sequent: HOLSequent ): TptpFile = {
    require( freeVariables( sequent ).isEmpty )

    val file = Seq.newBuilder[TptpInput]

    sequent.antecedent.zipWithIndex foreach {
      case ( formula: FOLFormula, i ) =>
        file += FofFormula( s"ant_$i", Axiom, formula, None )
    }

    if ( sequent.succedent.size <= 1 ) {
      sequent.succedent foreach {
        case formula: FOLFormula =>
          file += FofFormula( "conjecture", Conjecture, formula, None )
      }
    } else {
      sequent.succedent.zipWithIndex foreach {
        case ( formula: FOLFormula, i ) =>
          file += FofFormula( s"suc_$i", Axiom, -formula, None )
      }
    }

    file.result()
  }

}
