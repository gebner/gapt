package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.Definition
import at.logic.gapt.expr.hol.{ structuralCNF, existsclosure }
import at.logic.gapt.proofs.resolution.simplifyResolutionProof
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class justificationsToResolutionTest extends Specification {
  def test( es: HOLSequent ) = {
    val ( cnf, justs, defs ) = structuralCNF( es, generateJustifications = true, propositional = false )

    for ( ( cls, just ) <- justs ) {
      val p = justificationsToResolution( es, cls, just, defs )
      //      println( cls )
      //      println( p )
    }

    val Some( p ) = Escargot getRobinsonProof cnf
    val q = res2to3( simplifyResolutionProof( p ), es, justs.toMap, defs )
    println( q )

    val q_ = eliminateDefsRes( q, defs )
    println( q_ )
    val e = ResolutionToExpansionProof( q_ )
    println( e )
    println( e.deep )
    ok
  }

  "simple" in {
    test( existsclosure(
      "P(c,z)" +:
        "P(x,g(z)) -> P(f(x),z) & R(y)" +:
        "P(x,z) -> Q(x)" +:
        Sequent()
        :+ "Q(f(f(x)))"
        map parseFormula
    ) )
  }

  "complicated formula with structural CNF" in {
    val x = FOLVar( "x" )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val as = ( 0 to 12 ) map { i => FOLAtomConst( s"a$i", 1 ) }
    val endSequent = thresholds.atMost.oneOf( as map { a => Ex( x, a( x ) ) } ) +: Sequent() :+ ( as( 0 )( c ) --> -as( 1 )( d ) )

    test( endSequent )
  }

  "quantified definitions" in {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val as = ( 0 to 2 ) map { i => All( x, Ex( y, FOLAtom( s"a$i", x, y, z ) ) ) }
    val endSequent = Sequent() :+ ( All( z, thresholds.exactly.oneOf( as ) ) <-> All( z, naive.exactly.oneOf( as ) ) )

    test( endSequent )
  }

}
