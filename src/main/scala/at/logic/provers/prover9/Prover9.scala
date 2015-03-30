/**
 * Interface to the Prover9 first-order theorem prover.
 * Needs the command-line tools prover9, prooftool and tptp_to_ladr
 * to work.
 */

package at.logic.provers.prover9

import at.logic.algorithms.lk.applyReplacement
import at.logic.algorithms.resolution._
import at.logic.algorithms.rewriting.NameReplacement
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.{ CutRule, Axiom }
import at.logic.calculi.resolution._
import at.logic.calculi.resolution.robinson.{ InitialClause, RobinsonResolutionProof }
import at.logic.language.fol._
import at.logic.language.hol.containsStrongQuantifier
import at.logic.parsing.ivy.IvyParser
import at.logic.parsing.ivy.IvyParser.{ IvyStyleVariables, PrologStyleVariables, LadrStyleVariables }
import at.logic.parsing.ivy.conversion.IvyToRobinson
import at.logic.parsing.language.prover9._
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.provers.Prover
import at.logic.provers.prover9.commands.InferenceExtractor
import java.io._
import at.logic.utils.logging.Logger
import org.slf4j.LoggerFactory

import scala.sys.process._
import scala.collection.immutable.HashMap
import scala.io.Source
import scala.util.matching.Regex

class Prover9Exception( msg: String ) extends Exception( msg )

object Prover9 extends at.logic.utils.logging.Logger {

  def isValid( seq: FSequent ): Boolean = {
    val proofProblem = TPTPFOLExporter.tptp_proof_problem( seq )

    val ladr = "tptp_to_ladr" #< new ByteArrayInputStream( proofProblem.getBytes ) !!

    isValid( ladr )._1
  }

  private def outputContainsProof( output: String ): Boolean = {
    val proof_str = "============================== PROOF ================================="
    Source.fromString( output ).getLines.exists( line => line.startsWith( proof_str ) )
  }

  private def isValid( p9_input: String ): ( Boolean, String ) = {
    val outputBuf = Seq.newBuilder[String]
    val errBuf = Seq.newBuilder[String]
    val ret = "prover9" #< new ByteArrayInputStream( p9_input.getBytes ) ! ProcessLogger( line => outputBuf += line, err => errBuf += err )
    val output = outputBuf.result() mkString "\n"
    ret match {
      case 0 => // prover9 ran successfully
        return ( true, output )
      case 1 => throw new Prover9Exception( "A fatal error occurred (user's syntax error or Prover9's bug)." )
      case 2 => {
        trace( "Prover9 ran out of things to do (sos list exhausted)." )
        // Sometimes, prover9 returns with this exit code even though
        // a proof has been found.
        //
        // Hence we look through the proof for evidence that prover9 found a proof
        ( outputContainsProof( output ), output )
      }
      case 3 => {
        throw new Prover9Exception( "The max_megs (memory limit) parameter was exceeded." )
      }
      case 4 => {
        throw new Prover9Exception( "The max_seconds parameter was exceeded." )
      }
      case 5 => {
        throw new Prover9Exception( "The max_given parameter was exceeded." )
      }
      case 6 => {
        throw new Prover9Exception( "The max_kept parameter was exceeded." )
      }
      case 7 => {
        throw new Prover9Exception( "A Prover9 action terminated the search." )
      }
      case 101 => throw new Prover9Exception( "Prover9 received an interrupt signal." )
      case 102 => throw new Prover9Exception( "Prover9 crashed, most probably due to a bug." )
    }
  }

  /**
   * Proves a sequent through Prover9 (which refutes the corresponding set of clauses).
   */
  def prove( seq: FSequent ): Option[RobinsonResolutionProof] =
    {
      val proofProblem = TPTPFOLExporter.tptp_proof_problem( seq )

      val ladr = "tptp_to_ladr" #< new ByteArrayInputStream( proofProblem.getBytes ) !!

      // also pass along a CNF of the negated sequent so that
      // the proof obtained by prover9 can be fixed to have
      // as the clauses the clauses of this CNF (and not e.g.
      // these clauses modulo symmetry)
      val cs = Some( CNFn( seq.toFormula ).map( _.toFSequent ) )

      runP9OnLADR( ladr, cs )
    }

  private def refuteNamed( named_sequents: List[Tuple2[String, FSequent]] ): Option[RobinsonResolutionProof] =
    {
      val refutationProblem = TPTPFOLExporter.tptp_problem_named( named_sequents )
      val ladr = "tptp_to_ladr" #< new ByteArrayInputStream( refutationProblem.getBytes ) !!;
      runP9OnLADR( ladr, Some( named_sequents.map( p => p._2 ) ) )
    }

  private def runP9OnLADR( str_ladr: String, clauses: Option[Seq[FSequent]] = None ): Option[RobinsonResolutionProof] = {
    // find out which symbols have been renamed
    // this information should eventually be used when
    // parsing the prover9 proof
    val regexp = new Regex( """%\s*\(arity (\d+)\)\s*'(.*?)'\s*(ladr\d+)""" )

    val symbol_map = str_ladr.split( System.getProperty( "line.separator" ) ).foldLeft( new HashMap[String, ( Int, String )] )( ( m, l ) =>
      l match {
        case regexp( arity, orig, repl ) => m.updated( repl, ( arity.toInt, orig ) )
        case _                           => m
      } )

    isValid( str_ladr ) match {
      case ( true, output ) =>
        val p9proof = parseProver9( output )
        val tp9proof = NameReplacement( p9proof._1, symbol_map )
        val ret = if ( clauses != None ) fixDerivation( tp9proof, clauses.get ) else tp9proof
        Some( ret )
      case _ => None
    }
  }

  /**
   * Refutes a set of clauses, given as a List[FSequent].
   */
  def refute( sequents: List[FSequent] ): Option[RobinsonResolutionProof] =
    refuteNamed( sequents.zipWithIndex.map( p => ( "sequent" + p._2, p._1 ) ) )

  def refute( filename: String ): Option[RobinsonResolutionProof] =
    runP9OnLADR( Source.fromFile( filename ).mkString )

  def refuteTPTP( fn: String ): Option[RobinsonResolutionProof] = {
    val ladr = "tptp_to_ladr" #< new FileInputStream( fn ) !!

    runP9OnLADR( ladr )
  }

  /* Takes the output of prover9, extracts a resolution proof, the original endsequent and the clauses. */
  def parseProver9( p9_out: String ): ( RobinsonResolutionProof, FSequent, FSequent ) = {
    val ivy_out = "prooftrans" #< new ByteArrayInputStream( p9_out.getBytes ) #| "prooftrans ivy" !!

    val iproof = IvyParser( ivy_out, IvyStyleVariables )
    val rproof = IvyToRobinson( iproof )

    val fs = InferenceExtractor.viaLADR( p9_out )
    val clauses = InferenceExtractor.clausesViaLADR( p9_out )
    ( rproof, fs, clauses )
  }

  def parseProver9LK( p9_out: String, forceSkolemization: Boolean = false ): LKProof = {

    val ( proof, endsequent, clauses ) = Prover9.parseProver9( p9_out )

    if ( !forceSkolemization && !containsStrongQuantifier( endsequent ) ) {

      val ant = endsequent.antecedent.map( x => univclosure( x.asInstanceOf[FOLFormula] ) )
      val suc = endsequent.succedent.map( x => existsclosure( x.asInstanceOf[FOLFormula] ) )
      val closure = FSequent( ant, suc )

      val clause_set = CNFn( endsequent.toFormula ).map( c =>
        FSequent( c.neg.map( f => f.asInstanceOf[FOLFormula] ), c.pos.map( f => f.asInstanceOf[FOLFormula] ) ) )

      val res_proof = fixDerivation( proof, clause_set )

      RobinsonToLK( res_proof, closure )

    } else {

      val fclauses: Set[FClause] = proof.nodes.map {
        case InitialClause( clause ) => clause.toFClause
        case _                       => FClause( Nil, Nil )
      }.filter( ( x: FClause ) => x match {
        case FClause( Nil, Nil ) => false;
        case _                   => true
      } )
      val clauses = fclauses.map( c => univclosure( Or(
        c.neg.map( f => Neg( f.asInstanceOf[FOLFormula] ) ).toList ++
          c.pos.map( f => f.asInstanceOf[FOLFormula] ).toList ) ) )
      val clauses_ = clauses.partition( _ match {
        case Neg( _ ) => false;
        case _        => true
      } )
      //val cendsequent = FSequent(clauses.toList, Nil)
      val cendsequent2 = FSequent( clauses_._1.toList, clauses_._2.map( _ match {
        case Neg( x ) => x
      } ).toList )

      RobinsonToLK( proof, cendsequent2 )

    }
  }

  def isInstalled(): Boolean = {
    if ( !isLadrToTptpInstalled() ) {
      warn( "ladr_to_tptp not found!" )
      return false
    }
    if ( !isProver9Installed() ) {
      warn( "prover9 not found!" )
      return false
    }
    if ( !isProoftransInstalled() ) {
      warn( "prooftrans not found!" )
      return false
    }
    if ( !isTptpToLadrInstalled() ) {
      warn( "tptp_to_ladr not found!" )
      return false
    }
    true
  }

  private def isLadrToTptpInstalled(): Boolean = callBinary( "ladr_to_tptp" ) == 1
  private def isTptpToLadrInstalled(): Boolean = callBinary( "tptp_to_ladr" ) == 0
  private def isProver9Installed(): Boolean = callBinary( "prover9" ) == 2
  private def isProoftransInstalled(): Boolean = callBinary( "prooftrans" ) == 1

  private def callBinary( name: String ): Int = {
    val err = StringBuilder.newBuilder
    val out = StringBuilder.newBuilder
    val logger = ProcessLogger( line => out ++= line, line => err ++= line )
    try {
      val pio = name run logger
      pio.exitValue()
    } catch {
      case e: Exception =>
        -1
    }
  }

}

class Prover9Prover extends Prover with at.logic.utils.logging.Logger {
  def getRobinsonProof( seq: FSequent ) = Prover9.prove( seq )

  /**
   * Return an LK proof of seq.
   *
   * Note: We interpret free variables as constants. This
   * makes sense from the proof point-of-view (as opposed to
   * the refutational point-of-view).
   * If we don't do this, prover9 substitutes for the variables
   * in the formula (i.e. it proves the existential closure, not
   * the universal closure, as expected).
   *
   * TODO: the ground/unground code should be in Prover9.prove, and
   * the replacement applied to the resolution proof already (not the
   * LK proof, as we do it here.) To do this, a applyReplacement for
   * resolution proofs needs to be written.
   */
  def getLKProof( seq: FSequent ): Option[LKProof] =
    {
      val ( gseq, map ) = ground( seq )

      getRobinsonProof( gseq ) match {
        case Some( proof ) => {
          trace( " got a robinson proof from prover9, translating " )
          Some( unground( RobinsonToLK( proof, gseq ), map ) )
        }
        case None => {
          trace( " proving with prover9 failed " )
          None
        }
      }
    }

  // Grounds a sequent by replacing variables by new constants.
  private def ground( seq: FSequent ): ( FSequent, Map[FOLVar, FOLConst] ) = {
    // FIXME: cast of formula of sequent!
    val free = seq.antecedent.flatMap(
      f => freeVariables( f.asInstanceOf[FOLFormula] ) ).toSet ++
      seq.succedent.flatMap( f => freeVariables( f.asInstanceOf[FOLFormula] ) ).toSet
    // FIXME: make a better association between the consts and the vars.
    //val map = free.zip( free.map( v => new FOLConst( new CopySymbol( v.name ) ) ) ).toMap
    val map = free.zip( free.map( v => new FOLConst( v.sym ) ) ).toMap
    trace( "grounding map in prover9: " )
    trace( map.toString )
    // FIXME: cast of formula of sequent!
    val subst = Substitution( map )
    val ret = FSequent( seq.antecedent.map( f => subst( f.asInstanceOf[FOLFormula] ) ),
      seq.succedent.map( f => subst( f.asInstanceOf[FOLFormula] ) ) )
    ( ret, map )
  }

  private def unground( p: LKProof, map: Map[FOLVar, FOLConst] ) =
    applyReplacement( p, map.map( x => x.swap ) )._1

  /* TODO: should use this when grounding instead of ConstantStringSymbol
           to avoid name clashes. Can't seem to get equality to work,
           though.

  case class CopySymbol( val s: SymbolA ) extends ConstantSymbolA {
    override def toString() = s.toString
    def toCode() = "CopySymbol( " + s.toCode + " )"
    def compare(that: SymbolA) = that match {
      case CopySymbol( s2 ) => s.compare( s2 )
    }
    override def unique = "CopySymbol" 
  }
*/

  override def isValid( seq: FSequent ): Boolean = Prover9.isValid( seq )
}
