/*
 * naiveIncompleteMatchingAlgorithm.scala
 *
 */

package at.logic.algorithms.matching

import at.logic.language.hol._
import at.logic.language.lambda._

import scala.App

object NaiveIncompleteMatchingAlgorithm {

  def matchTerm( term: HOLExpression, posInstance: HOLExpression ): Option[Substitution] =
    matchTerm( term, posInstance, freeVariables( posInstance ) )

  // restrictedDomain: variables to be treated as constants.
  def matchTerm( term: HOLExpression, posInstance: HOLExpression, restrictedDomain: List[Var] ): Option[Substitution] =
    holMatch( term, posInstance )( restrictedDomain )

  def holMatch( s: HOLExpression, t: HOLExpression )( implicit restrictedDomain: List[Var] ): Option[Substitution] =
    ( s, t ) match {
      case ( App( s_1, s_2 ), App( t_1, t_2 ) ) => merge( holMatch( s_1, t_1 ), holMatch( s_2, t_2 ) )
      case ( s: Var, t: HOLExpression ) if !restrictedDomain.contains( s ) && s.exptype == t.exptype => Some( Substitution( s, t ) )
      case ( v1: Var, v2: Var ) if v1 == v2 => Some( Substitution() )
      case ( v1: Var, v2: Var ) if v1 != v2 => None
      case ( c1: Const, c2: Const ) if c1 == c2 => Some( Substitution() )
      case ( Abs( v1, e1 ), Abs( v2, e2 ) ) => holMatch( e1, e2 ) //TODO: add sub v2 <- v1 on e2 and check
      case _ => None
    }

  def merge( s1: Option[Substitution], s2: Option[Substitution] ): Option[Substitution] = ( s1, s2 ) match {
    case ( Some( ss1 ), Some( ss2 ) ) => {
      if ( !ss1.map.forall( s1 =>
        ss2.map.forall( s2 =>
          s1._1 != s2._1 || s1._2 == s2._2 ) ) )
        None
      else {
        val new_list = ss2.map.filter( s2 => ss1.map.forall( s1 => s1._1 != s2._1 ) )
        Some( Substitution( ss1.map ++ new_list ) )
      }
    }
    case ( None, _ ) => None
    case ( _, None ) => None
  }
}
