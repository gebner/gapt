package gapt.provers.slakoning

import gapt.expr._
import org.specs2.mutable._

class SlakoningTest extends Specification {

  "lem 1" in {
    Slakoning.getNDProof(
      hos"""
            !x (p x | ~ p x) :- ~ ~ p c -> p c
         """ ) must beSome
  }

  "lem" in { Slakoning.getNDProof( hos":- p | ~p" ) must beNone }
  "dne lem" in { Slakoning.getNDProof( hos":- ~ ~(p | ~p)" ) must beSome }
  "linear" in {
    Slakoning.getNDProof(
      hos"""
              !x P(x,0),
              !x!y (!z P(f(x,z),y) -> P(x,s(y)))
              :- !x P(x,s(s(s(0))))
          """ ) must beSome
  }

}
