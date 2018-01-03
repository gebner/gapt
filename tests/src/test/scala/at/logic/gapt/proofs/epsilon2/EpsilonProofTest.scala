package at.logic.gapt.proofs.epsilon2

import at.logic.gapt.examples.{ Pi2Pigeonhole, Pi3Pigeonhole }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion.deskolemizeET
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class EpsilonProofTest extends Specification with SatMatchers {

  "linear example" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"c:i"; ctx += hoc"f:i>i"; ctx += hoc"P:i>o"
    ctx += Context.SkolemFun( hoc"sk:i", le"!x (P x -> P (f x))" )
    val p = EpsilonProof(
      Vector(
        le"sk" -> le"c",
        le"sk" -> le"f c",
        le"sk" -> le"f (f c)",
        le"sk" -> le"f (f (f c))" ),
      epsilonized = hos"P c, P sk -> P (f sk) :- P (f (f (f (f c))))",
      shallow = hos"P c, !x (P x -> P (f x)) :- P (f (f (f (f c))))" )
    ctx.check( p )
    p.deep must beValidSequent
  }

  "quantifier blocks" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"P:i>i>i>o"
    ctx += hoc"f:i>i"; ctx += hoc"g:i>i"; ctx += hoc"h:i>i"
    Escargot getEpsilonProof hof"∀x∀y∀z P(x,y,z) ⊃ ∃x∃y∃z P(f x, g y, h z)" must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

  "deskolemization" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"P:i>i>i>o"
    Escargot getEpsilonProof hof"∀x∃y∀z P(x,y,z) ⊃ ∃z∀x∃y P(x,y,z)" must beLike {
      case Some( p ) =>
        ctx.check( p )
        p.deep must beValidSequent
    }
  }

  "eigenvariables" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"P:i>i>i>o"
    val formula = hof"∀x∃y∀z P(x,y,z) ⊃ ∃z∀x∃y P(x,y,z)"
    val Some( expansion ) = Escargot.getExpansionProof( formula )
    val desk = deskolemizeET( expansion )
    val p = ExpansionProofToEpsilon( desk )
    ctx.check( p )
    p.deep must beValidSequent
  }

  "many sorted 1" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Context.InductiveType( ty"nat", hoc"0 : nat", hoc"s : nat > nat" )
    ctx += hoc"P: nat > o"
    Escargot.getEpsilonProof( hof"!x (P x -> P (s x)) -> P 0 -> P (s (s 0))" ) must beLike {
      case Some( p ) =>
        ctx.check( p )
        p.deep must beValidSequent
    }
  }

  "many sorted 2" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Context.InductiveType( ty"list ?a", hoc"nil : list ?a", hoc"cons : ?a > list ?a > list ?a" )
    ctx += hoc"P: list ?a > o"
    ctx += Context.Sort( "i" ) // TODO(gabriel): escargot fails when proving the goal with list ?a
    val f = hof"!xs!x (P xs -> P (cons x xs)) -> P nil -> !x P (cons x nil : list i)"
    Escargot.getEpsilonProof( f ) must beLike {
      case Some( p ) =>
        ctx.check( p )
        p.deep must beValidSequent
    }
  }

  "cuts 2" in {
    implicit val ctx: MutableContext = Pi2Pigeonhole.ctx.newMutable
    val p = LKProofToEpsilon( Pi2Pigeonhole.proof )
    ctx.check( p )
    p.deep must beEValidSequent
  }

  "cuts 3" in {
    implicit val ctx: MutableContext = Pi3Pigeonhole.ctx.newMutable
    val p = LKProofToEpsilon( Pi3Pigeonhole.proof )
    ctx.check( p )
    p.deep must beEValidSequent
  }

  "first 1" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"P:i>i>o"
    ctx += hoc"f:i>i"; ctx += hoc"g:i>i"; ctx += hoc"h:i>i"; ctx += hoc"c:i"

    import at.logic.gapt.proofs.gaptic._
    val lk = Proof( hols"h: !x (P x (f x) | P x (g x) | P x (h x)) :- ?x?y?z?w (P x y & P y z & P z w)" ) {
      cut( "c", hof"!x?y P x y" )
      forget( "g" ); escargot.withDeskolemization
      forget( "h" ); escargot.withDeskolemization
    }

    val p = LKProofToEpsilon( lk )
    p.deep must beValidSequent
    ctx.check( p )
    val p2 = reduceEpsilons( p )
    ctx.check( p2 )
    p2.deep must beValidSequent
  }

  "first 2" in {
    implicit val ctx: MutableContext = Pi2Pigeonhole.ctx.newMutable
    val p = LKProofToEpsilon( Pi2Pigeonhole.proof )
    p.deep must beEValidSequent
    val p2 = reduceEpsilons( p )
    ctx.check( p2 )
    p2.deep must beEValidSequent
  }

  "first 3" in {
    implicit val ctx: MutableContext = Pi3Pigeonhole.ctx.newMutable
    val p = LKProofToEpsilon( Pi3Pigeonhole.proof )
    p.deep must beEValidSequent
    val p2 = reduceEpsilons( p )
    ctx.check( p2 )
    p2.deep must beEValidSequent
  }

}
