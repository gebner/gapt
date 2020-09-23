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

  "quant alt" in {
    Slakoning.getNDProof( hos":- !y ?x (p x & q y) <-> ?x !y (p x & q y)" ) must beSome
  }

  "quant alt 2" in {
    Slakoning.getNDProof( hos":- ?x !y ?z (p x & q y & r z) <-> ?z !y ?x (p x & q y & r z)" ) must beSome
  }

  "php" in {
    Slakoning.getNDProof(
      hos"""
            o11 | o12,
            o21 | o22,
            o31 | o32
            :- (o11 & o21) | (o11 & o31) | (o21 & o31) | (o12 & o22) | (o12 & o32) | (o22 & o32)
        """ ) must beSome
  }

  "syn074mwe" in {
    Slakoning.getNDProof(
      hos"""
            !x !y (bigf x y -> y = b)
            :- ?x ?w !y (bigf x y -> y = w)
        """ ) must beSome
  }

  "syn415mwe" in {
    Slakoning.getNDProof(
      hos""" :-
             ?u !v (f v -> u = v) ->
             true & !y !z (f y & f z -> y = z)
        """ ) must beSome
  }

}
