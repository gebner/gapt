package at.logic.gapt.examples.induction

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.expr._

object double extends TacticsProof {

  ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"d: nat>nat"

  val axs =
    hols"""
          p0: !x x+0 = x,
          ps: !x!y x+s(y) = s(x+y),
          d0: d 0 = 0,
          ds: !x d (s x) = s (s (d x))
          :-
        """

  //  ctx += Context.InductiveType( ty"seq", hoc"nil: seq", hoc"snoc: seq>nat>seq" )

  ctx += hoc"'<': nat>nat>o"
  val cansolSeb = le"^x^y !(S:nat) ((0<y -> x+0=x & d(0)=0) & (S<y -> x+s(S)=s(x+S) & d(s(S))=s(s(d(S)))))"

  Lemma( axs ++ hols":- d x = x + x" ) {
    cut( "c", hof"$cansolSeb x x" ).onAll( unfold() in "c" ); decompose; escargot
  }

}