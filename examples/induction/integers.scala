package gapt.examples.induction

import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._
import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.provers.spass.SPASS

object integers extends TacticsProof {
  ctx += InductiveType( "int", hoc"0: int", hoc"s: int>int", hoc"p: int>int" )
  val intTh =
    hols"""
          sp: ∀x s(p(x)) = x,
          ps: ∀x p(s(x)) = x :-
        """

  ctx += hoc"'+': int>int>int"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  val addRTh =
    hols"""
          a0: ∀x x+0 = x,
          as: ∀x ∀y x+s(y)=s(x+y),
          ap: ∀x ∀y x+p(y)=p(x+y) :-
        """

  //  val addZeroLeft = Lemma( intTh ++ addRTh ++ hols":- ∀x 0+x = x" ) { treeGrammarInduction.verbose }

  val addLTh =
    hols"""
          a0: ∀x 0+x = x,
          as: ∀x ∀y s(x)+y=s(x+y),
          ap: ∀x ∀y p(x)+y=p(x+y) :-
        """

  //  val addComm = Lemma( intTh ++ addRTh ++ addLTh ++ hols":- ∀x ∀y x+y = y+x" ) {
  //    allR; treeGrammarInduction.canSolSize( 1 ).verbose
  //  }

  val addAssocSpecialCase = Lemma( intTh ++ addRTh ++ addLTh ++ hols":- ∀x x+(x+x)=(x+x)+x" ) {
    treeGrammarInduction
      .equationalTheory( hof"0+x=x", hof"x+0=x" )
      .instanceProver( SPASS.extendToManySortedViaPredicates )
      .quantTys()
      .canSolSize( 2 )
      .verbose
  }
}