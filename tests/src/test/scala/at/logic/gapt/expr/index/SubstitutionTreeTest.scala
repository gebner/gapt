package at.logic.gapt.expr.index
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.formulaToSequent
import at.logic.gapt.grammars.recSchemToVTRATG
import at.logic.gapt.proofs.expansion.FOLInstanceTermEncoding
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class SubstitutionTreeTest extends Specification {

  "demo" in {
    //    val terms = Seq(le"f a b", le"f a c", le"f a (g b)", le"f a (g c)")
    //    val terms = (0 to 5).map(i => le"r 0 ${Numeral(i)} ${Numeral(i)}")
//    val terms = FOLInstanceTermEncoding( Escargot getExpansionProof formulaToSequent.pos(hof"!x!y!z x*(y*z) = (x*y)*z & !x x * e = x & !x x * i x = e -> !x ?y x*y*x=e") get )._1
    val terms = FOLInstanceTermEncoding(at.logic.gapt.examples.poset.proof.cycleImpliesEqual4)._1
    var tree = SubstitutionTree.empty[LambdaExpression]( Ti )
    for ( term <- terms ) {
      tree += ( term, term )
    }
    println( org.kiama.output.PrettyPrinter.pretty_any( tree ) )
    for ( term <- terms ) {
      tree( term ) must contain( term )
    }
    println(tree.toRecSchem)
    println(recSchemToVTRATG(tree.toRecSchem))
    ok
  }

}
