package at.logic.gapt.proofs.nd
import at.logic.gapt.proofs.nd.tactics._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, HOLSequent, NDSequent, Sequent, SequentMatchers }
import org.specs2.mutable.Specification

class NDTacticsTest extends Specification with SequentMatchers {

  def verifyLemma( goal: Formula )( tac: Tactic[Nothing] ) =
    Lemma( goal )( tac ).conclusion must_== Sequent() :+ goal

  "simple" in {
    verifyLemma( hof"a & b -> a" ) {
      intros next assumption
    }

    verifyLemma( hof"a | (a & b) -> a" ) {
      intros >> elim( hof"a | (a & b)" ) >> assumption
    }

    verifyLemma( hof"p 0 -> !x (p x -> p (s x)) -> p (s (s 0))" ) {
      intros next
        tactics.have( hof"!x (p x -> p (s (s x)))" ).from {
          intros >> tactics.have( hof"p (s x)" ) >> assumption
        } next
        assumption
    }
  }

  "induction" in {
    implicit var ctx = Context.default
    ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"'+': nat>nat>nat"

    verifyLemma( hof"!(x:nat) 0+x = x" ) {
      intros next induction( "x" ).cases {
        case "0" => sorry
        case "s" =>
          suffices( hof"s(0+x_0)=x_0" ).from( assumption ) next
            assumption
      }
    }
  }

}
