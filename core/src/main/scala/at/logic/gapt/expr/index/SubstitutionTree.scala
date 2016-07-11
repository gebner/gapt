package at.logic.gapt.expr.index
import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ RecursionScheme, leastGeneralGeneralization }

import scala.collection.mutable

case class SubstitutionTree[A](
    vars:     Seq[Var],
    children: Map[Seq[LambdaExpression], SubstitutionTree[A]],
    leaves:   Seq[A]
) {
  def vecLen = vars.size
  for ( ( ts, _ ) <- children ) {
    require( ts.size == vecLen )
    for ( ( v, t ) <- ( vars, ts ).zipped )
      require( v.exptype == t.exptype )
  }

  def foreach( term: LambdaExpression )( func: A => Unit ): Unit = foreach( Seq( term ) )( func )
  def foreach( terms: Seq[LambdaExpression] )( func: A => Unit ): Unit = {
    leaves.foreach( func )
    for {
      ( childTerms, child ) <- children
      subst <- syntacticMatching( childTerms zip terms toList )
    } child.foreach( subst( child.vars ) )( func )
  }

  def apply( term: LambdaExpression ): Seq[A] = {
    val buffer = Seq.newBuilder[A]
    foreach( term )( buffer += _ )
    buffer.result()
  }

  def +( term: LambdaExpression, elem: A ): SubstitutionTree[A] = this + ( Seq( term ), elem )
  def +( terms: Seq[LambdaExpression], elem: A ): SubstitutionTree[A] = {
    if ( terms == vars ) return copy( leaves = leaves :+ elem )
    for {
      ( childTerms, child ) <- children
      subst <- syntacticMatching( childTerms zip terms toList )
    } return copy( children = children.updated( childTerms, child + ( subst( child.vars ), elem ) ) )
    for {
      ( childTerms, child ) <- children
      ( lgg, subst1, subst2 ) = leastGeneralGeneralization( childTerms, terms )
      if lgg.exists( !_.isInstanceOf[Var] )
      if lgg.forall( !_.isInstanceOf[Var] ) // !!!
      newChildVars = subst1.keys.toSeq.sortBy( _.name )
      newChild = SubstitutionTree( newChildVars, Map(
        newChildVars.map( subst1 ) -> child,
        newChildVars.map( subst2 ) -> SubstitutionTree( Seq(), Map(), Seq( elem ) )
      ), Seq() )
    } return copy( children = children - childTerms + ( lgg -> newChild ) )
    copy( children = children + ( terms -> SubstitutionTree( Seq(), Map(), Seq( elem ) ) ) )
  }

  def toRecSchem: RecursionScheme = {
    import at.logic.gapt.grammars._

    val nameGen = rename.awayFrom( containedNames( this ) )
    val Seq( ty ) = vars.map( _.exptype )
    val axiom = Const( nameGen.fresh( "A" ), ty )
    val rules = Set.newBuilder[Rule]

    def process( node: SubstitutionTree[A] ): LambdaExpression =
      if ( node.vars.isEmpty ) {
        axiom
      } else {
        val res = node.children.map { case ( ts, c ) => ( process( c ), ts ) }
        val nt = Const( nameGen.freshWithIndex( "B" ), FunctionType( ty, node.vars.map( _.exptype ) ) )
        for ( ( lhs, ts ) <- res ) rules += Rule( lhs, nt( ts: _* ) )
        nt( node.vars: _* )
      }

    for ( ( Seq( t ), c ) <- children ) rules += Rule( process( c ), t )

    RecursionScheme( axiom, rules.result() )
  }

  def toGraphviz = {
    val out = new StringBuilder
    out ++= "digraph T {\n"
    out ++= "  rankdir = LR;\n"

    val indices = Stream.from( 0 ).iterator
    def write( t: Seq[LambdaExpression], n: SubstitutionTree[A] ): Int = {
      val i = indices.next()
      //      out ++= s"""  $i [label="${t.toString.replace( "\n", "" )}"];"""
      out ++= s"""  $i [label="${t.mkString( ", " )}"];"""
      out += '\n'
      for ( ( ts, c ) <- n.children )
        out ++= s"  $i -> ${write( ts, c )};\n"
      i
    }
    write( vars, this )

    out ++= "}\n"
    out.result()
  }
}
object SubstitutionTree {
  def empty[A]( ty: Ty ) = SubstitutionTree[A]( Seq( Var( "x", ty ) ), Map(), Seq() )

  def apply( exprs: Traversable[LambdaExpression] ): SubstitutionTree[LambdaExpression] = {
    var tree = empty[LambdaExpression]( exprs.headOption.fold[Ty]( Ti )( _.exptype ) )
    for ( expr <- exprs ) tree += ( expr, expr )
    tree
  }
}
