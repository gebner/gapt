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
        file += TptpFormulaInput( "fof", s"ant_$i", "axiom", formula, None )
    }

    if ( sequent.succedent.size <= 1 ) {
      sequent.succedent foreach {
        case formula: FOLFormula =>
          file += TptpFormulaInput( "fof", "suc_0", "conjecture", formula, None )
      }
    } else {
      sequent.succedent.zipWithIndex foreach {
        case ( formula: FOLFormula, i ) =>
          file += TptpFormulaInput( "fof", s"suc_$i", "axiom", -formula, None )
      }
    }

    file.result()
  }

}
