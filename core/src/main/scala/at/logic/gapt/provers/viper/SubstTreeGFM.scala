package at.logic.gapt.provers.viper
import java.nio.file.{ Files, Paths }

import at.logic.gapt.expr._
import at.logic.gapt.expr.index.SubstitutionTree
import at.logic.gapt.grammars.RecursionScheme
import at.logic.gapt.proofs.FiniteContext

class SubstTreeGFM(
    paramTys:     Seq[Ty],
    instanceType: Ty,
    context:      FiniteContext
) extends InductiveGrammarFindingMethod {
  override def find( taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): RecursionScheme = {
    var substTree = SubstitutionTree.empty[( LambdaExpression, Seq[LambdaExpression] )]( instanceType )
    for ( x @ ( ps, t ) <- taggedLanguage ) {
      val repl = ( for ( ( p, i ) <- ps.zipWithIndex ) yield p -> Const( s"_z$i", p.exptype ) ) ++
        freeVariables( ps ).map( v => v -> Const( "_x", v.exptype ) )
      substTree += ( TermReplacement( t, repl.toMap ), x.swap )
    }
    println( org.kiama.output.PrettyPrinter.pretty_any( substTree ) )
    println( substTree.toRecSchem )
    Files.write( Paths.get( "substtree.dot" ), substTree.toGraphviz.getBytes )
    ???
  }
}
