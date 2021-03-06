package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_01 extends TacticsProof {
  ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"S: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"d: nat>nat"

  val sequent =
    hols"""
          d0: d 0 = 0,
          ds: !x d (S x) = S (S (d x)),
          p0: !y 0 + y = y,
          ps: !x!y S x + y = S (x + y)
          :-
          !x d x = x + x
        """

  val proof = Lemma( sequent ) {
    cut( "lem", hof"!x !y x + S y = S (x + y)" ); forget( "g" )
    allR; allR
    induction( hov"x:nat" )
    rewrite.many ltr "p0" in "lem"; refl // IB
    rewrite.many ltr ( "ps", "IHx_0" ); refl // IS

    allR
    induction( hov"x:nat" )
    rewrite.many ltr ( "p0", "d0" ); refl // IB
    rewrite.many ltr ( "ps", "ds", "lem", "IHx_0" ); refl // IS
  }

  val singleInduction = Lemma( sequent ) {
    cut( "lem", hof"!x!y (x + S y = S (x + y) & d x = x + x)" ); forget( "g" )
    allR; induction( hov"x:nat" ).onAll( allR andThen destruct( "lem" ) )
    rewrite.many ltr "p0"; refl
    rewrite.many ltr ( "d0", "p0" ); refl
    rewrite.many ltr "ps"; allL( "IHx_0", le"y:nat" ); quasiprop
    rewrite.many ltr ( "ps", "ds" ); allL( "IHx_0", le"x_0:nat" ); quasiprop
    allR; allL( "lem", le"x:nat", le"x:nat" ); quasiprop
  }
}
