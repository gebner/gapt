package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent

import scala.annotation.implicitNotFound

/**
 * Created by sebastian on 11/3/15.
 */
package object substitution {

  @implicitNotFound( "No member of type class Substitutable found for types ${T}, ${U}" )
  trait Substitutable[-T, +U] extends FOLSubstitutable[T, U] {
    def applySubstitution( sub: Substitution, x: T ): U
    override def applyFOLSubstitution( sub: FOLSubstitution, x: T ): U = applySubstitution( sub, x )
  }

  implicit object SubstitutableHOLFormula extends Substitutable[HOLFormula, HOLFormula] {
    override def applySubstitution( sub: Substitution, f: HOLFormula ): HOLFormula = SubstitutableLambdaExpression.applySubstitution( sub, f ).asInstanceOf[HOLFormula]
  }

  implicit object SubstitutableLambdaExpression extends Substitutable[LambdaExpression, LambdaExpression] {
    override def applySubstitution( sub: Substitution, t: LambdaExpression ): LambdaExpression = t match {
      case v: Var                               => sub.map.getOrElse( v, v )
      case c: Const                             => c
      case App( a, b )                          => App( applySubstitution( sub, a ), applySubstitution( sub, b ) )
      case Abs( v, s ) if sub.domain contains v => applySubstitution( Substitution( sub.map - v ), t )
      case Abs( v, s ) if sub.range contains v =>
        // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
        val newV = rename( v, ( freeVariables( s ) ++ sub.range ).toList )
        applySubstitution( sub, Abs( newV, applySubstitution( Substitution( v -> newV ), s ) ) )
      case Abs( v, s ) => Abs( v, applySubstitution( sub, s ) )
    }
  }

  implicit def SubstitutableSeq[T, U]( implicit ev: Substitutable[T, U] ): Substitutable[Seq[T], Seq[U]] = new Substitutable[Seq[T], Seq[U]] {
    override def applySubstitution( sub: Substitution, seq: Seq[T] ): Seq[U] = seq map { ev.applySubstitution( sub, _ ) }
  }

  implicit def SubstitutableList[T, U]( implicit ev: Substitutable[T, U] ): Substitutable[List[T], List[U]] = new Substitutable[List[T], List[U]] {
    override def applySubstitution( sub: Substitution, list: List[T] ): List[U] = list map { ev.applySubstitution( sub, _ ) }
  }

  implicit def SubstitutableSequent[T, U]( implicit ev: Substitutable[T, U] ): Substitutable[Sequent[T], Sequent[U]] = new Substitutable[Sequent[T], Sequent[U]] {
    override def applySubstitution( sub: Substitution, sequent: Sequent[T] ): Sequent[U] = sequent map { ev.applySubstitution( sub, _ ) }
  }

  @implicitNotFound( "No member of type class FOLSubstitutable found for types ${T}, ${U}" )
  trait FOLSubstitutable[-T, U] {
    def applyFOLSubstitution( sub: FOLSubstitution, x: T ): U
  }

  implicit object FOLSubstitutableFOLExpression extends FOLSubstitutable[FOLExpression, FOLExpression] {
    override def applyFOLSubstitution( sub: FOLSubstitution, x: FOLExpression ): FOLExpression = SubstitutableLambdaExpression.applySubstitution( sub, x ).asInstanceOf[FOLExpression]
  }

  implicit object FOLSubstitutableFOLTerm extends FOLSubstitutable[FOLTerm, FOLTerm] {
    override def applyFOLSubstitution( sub: FOLSubstitution, x: FOLTerm ): FOLTerm = SubstitutableLambdaExpression.applySubstitution( sub, x ).asInstanceOf[FOLTerm]
  }

  implicit object FOLSubstitutableFOLFormula extends FOLSubstitutable[FOLFormula, FOLFormula] {
    override def applyFOLSubstitution( sub: FOLSubstitution, x: FOLFormula ): FOLFormula = SubstitutableLambdaExpression.applySubstitution( sub, x ).asInstanceOf[FOLFormula]
  }

  implicit object FOLSubstitutableFOLAtom extends FOLSubstitutable[FOLAtom, FOLAtom] {
    override def applyFOLSubstitution( sub: FOLSubstitution, x: FOLAtom ): FOLAtom = SubstitutableLambdaExpression.applySubstitution( sub, x ).asInstanceOf[FOLAtom]
  }

  implicit def FOLSubstitutableSeq[T, U]( implicit ev: FOLSubstitutable[T, U] ): FOLSubstitutable[Seq[T], Seq[U]] = new FOLSubstitutable[Seq[T], Seq[U]] {
    override def applyFOLSubstitution( sub: FOLSubstitution, seq: Seq[T] ): Seq[U] = seq map { ev.applyFOLSubstitution( sub, _ ) }
  }

  implicit def FOLSubstitutableList[T, U]( implicit ev: FOLSubstitutable[T, U] ): FOLSubstitutable[List[T], List[U]] = new FOLSubstitutable[List[T], List[U]] {
    override def applyFOLSubstitution( sub: FOLSubstitution, list: List[T] ): List[U] = list map { ev.applyFOLSubstitution( sub, _ ) }
  }

  implicit def FOLSubstitutableSequent[T, U]( implicit ev: FOLSubstitutable[T, U] ): FOLSubstitutable[Sequent[T], Sequent[U]] = new FOLSubstitutable[Sequent[T], Sequent[U]] {
    override def applyFOLSubstitution( sub: FOLSubstitution, sequent: Sequent[T] ): Sequent[U] = sequent map { ev.applyFOLSubstitution( sub, _ ) }
  }

}
