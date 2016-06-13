package at.logic.gapt.provers.eprover

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess, withTempFile }

object EProver extends EProver
class EProver extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        //        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val tptpIn = toTPTP( labelledCNF )
        val output = runProcess.withTempInputFile( Seq( "eproof", "--tptp3-format" ), tptpIn )
        val lines = output.split( "\n" )
        if ( lines.contains( "# SZS status Unsatisfiable" ) )
          RefutationSketchToResolution( TptpProofParser.parse(
            lines.filterNot( _ startsWith "# " ).mkString( "\n" ),
            labelledCNF mapValues { Seq( _ ) }
          ) ).toOption
        else None
      }
    )

  private def toTPTP( formula: LambdaExpression ): String = formula match {
    case Bottom()                  => "$false"
    case Or( a, b )                => s"${toTPTP( a )} | ${toTPTP( b )}"
    case Eq( a, b )                => s"${toTPTP( a )}=${toTPTP( b )}"
    case Neg( Eq( a, b ) )         => s"${toTPTP( a )}!=${toTPTP( b )}"
    case Neg( atom )               => s"~${toTPTP( atom )}"
    case FOLAtom( name, Seq() )    => name
    case FOLAtom( name, args )     => s"$name(${args map toTPTP mkString ","})"
    case FOLVar( name )            => name
    case FOLConst( name )          => name
    case FOLFunction( name, args ) => s"$name(${args map toTPTP mkString ","})"
  }

  def renameVars( formula: LambdaExpression ): LambdaExpression =
    Substitution( freeVariables( formula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"X$i" )
      } )( formula )
  private def toTPTP( clause: FOLClause ): String =
    toTPTP( renameVars( clause.toDisjunction ) )

  private def toTPTP( cnf: Map[String, FOLClause] ): String =
    cnf.map {
      case ( label, clause ) =>
        s"cnf($label, axiom, ${toTPTP( clause )})."
    }.mkString( sys.props( "line.separator" ) )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "eproof", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
