package at.logic.gapt.expr.substitution

import at.logic.gapt.expr._

import scala.annotation.implicitNotFound
import scala.collection.GenTraversable

/*
 * A substitution is a mapping from variables to lambda-expressions which differs from the identity
 * on finitely many variables. Therefore:
 *  1) each variable is mapped to only one lambda expression
 *  2) the order of the variable-mappings is irrelevant
 *  3) all variable-mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
 *
 * As the lambda calculus contains variable binders, substitution can only be defined up to alpha-equivalence.
 * When applying a substitution, bound variables are renamed if needed.
 */
class Substitution( val map: Map[Var, LambdaExpression] ) {

  // Require that each variable is substituted by a term of the same type
  for ( s <- map ) require(
    s._1.exptype == s._2.exptype,
    "Error creating substitution: variable " + s._1 + " has type " + s._1.exptype +
      " but subterm " + s._2 + " has type " + s._2.exptype
  )

  def apply[T, U]( x: T )( implicit ev: Substitutable[T, U] ): U = ev.applySubstitution( this, x )

  // TODO: why lists? why not sets?
  def domain: List[Var] = map.keys.toList
  def range: List[Var] = map.foldLeft( List[Var]() )( ( acc, data ) => freeVariables( data._2 ).toList ++ acc )

  def ::( sub: ( Var, LambdaExpression ) ) = new Substitution( map + sub )
  def ::( otherSubstitution: Substitution ) = new Substitution( map ++ otherSubstitution.map )

  override def hashCode = map.hashCode
  override def equals( a: Any ) = a match {
    case s: Substitution => map.equals( s.map )
    case _               => false
  }

  // an identity function maps all variables to themselves
  def isIdentity = map.filterNot( ( p: ( Var, LambdaExpression ) ) => p._1 == p._2 ).isEmpty

  // make sure the overriden keys are of the applying sub
  // note: compose is in function application notation i.e. (sigma compose tau) apply x = sigma(tau(x)) = x.tau.sigma
  def compose( sub: Substitution ): Substitution = Substitution( map ++ sub.map.map( x => ( x._1, apply( x._2 ) ) ) )

  //REMARK: this does not imply the substitution is injective
  def isRenaming = map.forall( p => p._2.isInstanceOf[Var] )

  //TODO: implement
  def isInjectiveRenaming = throw new Exception( "Not yet implemented!" )

  override def toString() = map.map( x => x._1 + " -> " + x._2 ).mkString( "Substitution(", ",", ")" )

}

object Substitution {
  def apply( subs: GenTraversable[( Var, LambdaExpression )] ): Substitution = new Substitution( Map() ++ subs )
  def apply( subs: ( Var, LambdaExpression )* ): Substitution = new Substitution( Map() ++ subs )
  def apply( variable: Var, expression: LambdaExpression ): Substitution = new Substitution( Map( variable -> expression ) )
  def apply( map: Map[Var, LambdaExpression] ): Substitution = new Substitution( map )
  def apply() = new Substitution( Map() )

  implicit def SubstitutableSeq[T, U]( ev: Substitutable[T, U] ): Substitutable[Seq[T], Seq[U]] = new Substitutable[Seq[T], Seq[U]] {
    override def applySubstitution( sub: Substitution, seq: Seq[T] ): Seq[U] = seq map { ev.applySubstitution( sub, _ ) }
  }

  implicit def SubstitutableList[T, U]( ev: Substitutable[T, U] ): Substitutable[List[T], List[U]] = new Substitutable[List[T], List[U]] {
    override def applySubstitution( sub: Substitution, seq: List[T] ): List[U] = seq map { ev.applySubstitution( sub, _ ) }
  }
}

class FOLSubstitution( val folmap: Map[FOLVar, FOLTerm] ) extends Substitution( folmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  def apply[T, U]( x: T )( implicit ev: FOLSubstitutable[T, U] ): U = ev.applyFOLSubstitution( this, x )

  def compose( sub: FOLSubstitution ): FOLSubstitution = FOLSubstitution( folmap ++ sub.folmap.map( x => ( x._1, apply( x._2 ) ) ) )
}
object FOLSubstitution {
  def apply( subs: GenTraversable[( FOLVar, FOLTerm )] ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( subs: ( FOLVar, FOLTerm )* ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( variable: FOLVar, term: FOLTerm ): FOLSubstitution = new FOLSubstitution( Map( variable -> term ) )
  def apply( map: Map[FOLVar, FOLTerm] ): FOLSubstitution = new FOLSubstitution( map )
  def apply() = new FOLSubstitution( Map() )

  implicit def FOLSubstitutableSeq[T, U]( implicit ev: FOLSubstitutable[T, U] ): FOLSubstitutable[Seq[T], Seq[U]] = new FOLSubstitutable[Seq[T], Seq[U]] {
    override def applyFOLSubstitution( sub: FOLSubstitution, seq: Seq[T] ): Seq[U] = seq map { ev.applyFOLSubstitution( sub, _ ) }
  }

  implicit def FOLSubstitutableList[T, U]( implicit ev: FOLSubstitutable[T, U] ): FOLSubstitutable[List[T], List[U]] = new FOLSubstitutable[List[T], List[U]] {
    override def applyFOLSubstitution( sub: FOLSubstitution, seq: List[T] ): List[U] = seq map { ev.applyFOLSubstitution( sub, _ ) }
  }
}

