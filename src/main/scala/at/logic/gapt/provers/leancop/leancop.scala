package at.logic.gapt.provers.leancop

import java.io.{ ByteArrayOutputStream, StringReader }

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr.{ Const, FOLHeadType, constants }
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.provers.renameConstantsToSafeNames
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._

class LeanCoPProver extends Prover with ExternalProgram {

  override def isValid( s: FSequent ): Boolean =
    getExpansionSequent( s ).isDefined

  override def getExpansionSequent( s: FSequent ): Option[ExpansionSequent] =
    withRenamedConstants( s ) { seq =>
      require( seq.succedent.size == 1 )

      val tptp = TPTPFOLExporter.tptp_proof_problem_split( seq )
      val leanCopOutput = withTempFile.fromString( tptp ) { tptpFile =>
        Seq( "leancop", tptpFile ) !!
      }

      // extract the part between the %----- delimiters
      val tptpProof = leanCopOutput.split( "\n" ).
        dropWhile( !_.startsWith( "%" ) ).drop( 1 ).
        takeWhile( !_.startsWith( "%" ) ).
        mkString( "\n" )

      LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) )
    }

  override def getLKProof( seq: FSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean = ( Seq( "which", "leancop" ) #> new ByteArrayOutputStream ! ) == 0

  private def withRenamedConstants( seq: FSequent )( f: FSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, _, invertRenaming ) = renameConstantsToSafeNames( seq )
    f( renamedSeq ) map { renamedExpSeq =>
      NameReplacement( renamedExpSeq, invertRenaming )
    }
  }
}
