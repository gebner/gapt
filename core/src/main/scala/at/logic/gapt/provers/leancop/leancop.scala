package at.logic.gapt.provers.leancop

import java.io.{ IOException, StringReader }

import at.logic.gapt.expr.{ All, Eq, Substitution, TermReplacement }
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.{ ETWeakQuantifierBlock, ExpansionProof, ExpansionProofToLK }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution.{ expansionProofFromInstances, structuralCNF }
import at.logic.gapt.provers.{ OneShotProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess }
import at.logic.gapt.utils.ScalazHelpers._

object LeanCoP extends LeanCoP
class LeanCoP extends OneShotProver with ExternalProgram {
  private val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent ): Boolean =
    getExpansionProof( s ).isDefined

  override def getExpansionProof( s: HOLSequent ): Option[ExpansionProof] =
    withRenamedConstants( s ) { seq =>
      val cnf = structuralCNF( s ).map( c => univclosure( c.conclusion.toDisjunction ) -> c ).toMap

      val tptp = TPTPFOLExporter.tptp_proof_problem_split( cnf.keys ++: Sequent() )
      val leanCopOutput = runProcess.withTempInputFile( Seq( "leancop" ), tptp )

      // extract the part between the %----- delimiters
      val tptpProof = leanCopOutput.split( nLine ).
        dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
        takeWhile( !_.startsWith( "%-" ) ).
        mkString( nLine )

      LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) ) map { es =>
        val hasEquality = cnf.values.flatMap( _.conclusion.elements ).exists {
          case Eq( _, _ ) => true
          case _          => false
        }

        val substs = for {
          ETWeakQuantifierBlock( shallow, insts ) <- es.elements
          ( formula @ All.Block( vars, _ ), clause ) <- cnf
          if formula == shallow
        } yield clause.conclusion.asInstanceOf[HOLClause] ->
          insts.keys.map( s => Substitution( vars zip s ) ).toSet

        expansionProofFromInstances( substs.toMap, cnf.values.toSet, !hasEquality )
      }
    }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    getExpansionProof( seq ) map { ExpansionProofToLK( _ ).get }

  override val isInstalled: Boolean = try runProcess.withExitValue( Seq( "leancop" ) )._1 == 2
  catch { case _: IOException => false }

  private def withRenamedConstants( seq: HOLSequent )( f: HOLSequent => Option[ExpansionProof] ): Option[ExpansionProof] = {
    val ( renamedSeq, _, invertRenaming ) = renameConstantsToFi( seq )
    f( renamedSeq ) map { TermReplacement( _, invertRenaming toMap ) }
  }
}
