package at.logic.gapt.provers.tactics

import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.prooftool
import at.logic.gapt.expr.FOLVar
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.expr.hol.{ existsclosure, univclosure }
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import org.specs2.mutable._

class TacticsTest extends Specification {
  "demo" in {
    val es = "P(x)" +: Sequent() :+ "P(x) | Q(y)" map parseFormula map univclosure.apply
    val p = new TacticsProver( es ) {
      intros
      elim( "b0" )
      apply( "a0", "b0l" )
      printState
    }.constructProof
    //    prooftool(p)
    //    Thread.sleep(100000)
    ok
  }

  "factorial" in {
    val n = 4

    val es =
      ( "f(0) = s(0)" +: "f(s(x)) = s(x)*f(x)" +:
        "g(x,0) = x" +: "g(x,s(y)) = g(x*s(y),y)" +:
        "x*s(0) = x" +: "s(0)*x = x" +:
        "(x*y)*z = x*(y*z)" +:
        Sequent()
        :+ "g(s(0), xn) = f(xn)"

        map parseFormula
        map ( univclosure( _ ), FOLSubstitution( FOLVar( "xn" ) -> Utils.numeral( n ) ).apply ) )

    val p = new TacticsProver( es ) {
      rewrite( "a1", in = "b0" )
      repeat {
        rewrite( "a1", in = "b0" )
        rewrite( "a6", in = "b0", flip = true )
      }
      rewrite( "a0", in = "b0" )
      rewrite( "a4", in = "b0" )
      repeat { rewrite( "a3", in = "b0" ) }
      rewrite( "a2", in = "b0" )
      rewrite( "a5", in = "b0" )
      refl
    }.constructProof

    new InstanceTermEncoding( p.root.toHOLSequent ).encode( LKToExpansionProof( p ) ) foreach println

    ok
  }

  "pigeonhole" in {
    val es = (
      "s(x) <= y -> x <= y" +:
      "f(x) = 0 | f(x) = s(0)" +:
      "x <= M(x,y)" +: "y <= M(x,y)" +:
      Sequent()
      :+ "s(x) <= y & f(x) = f(y)"

      map parseFormula
      map ( univclosure( _ ), existsclosure( _ ) )
    )
    val p = new TacticsProver( es ) {
      cut( parseFormula( "(all x (exists y (x <= y & f(y) = 0)))" ) )
      cut( parseFormula( "(all x (exists y (x <= y & f(y) = s(0))))" ) )

      intros
      inst( "c0", Seq( parseTerm( "M(x1,x2)" ) ) )
      inst( "c1", Seq( parseTerm( "M(x1,x2)" ) ) )
      forget( "a0" )
      printState
      prover9

      inst( "c1", keep = true, Seq( parseTerm( "0" ) ) )
      intros
      inst( "c1_", Seq( parseTerm( "s(x3)" ) ) )
      intros
      forget( "a1", "a2", "a3" )
      prover9

      inst( "c0", keep = true, Seq( parseTerm( "0" ) ) )
      intros
      inst( "c0_", Seq( parseTerm( "s(x6)" ) ) )
      intros
      forget( "a1", "a2", "a3" )
      printState
      prover9
    }.constructProof
    ok
  }
}