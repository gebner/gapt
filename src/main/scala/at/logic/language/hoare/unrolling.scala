package at.logic.language.hoare

import at.logic.calculi.lk.base.FSequent
import at.logic.language.fol._
import at.logic.language.fol.Utils.numeral
import at.logic.language.hol.{ AllVar, Equation, And }
import at.logic.language.lambda.{ Var, Substitution }

object unrollLoop {
  def apply( p: Program, actualN: Int ): Program = p match {
    case ForLoop( i, n, b ) => Sequence(
      ( 0 until actualN ).map( actualI =>
        substVariables( b, Map( i -> numeral( actualI ), n -> numeral( actualN ) ) ) ) )
  }
}

case class SimpleInductionProblem( val gamma: Seq[FOLFormula], val alphaVar: Var, val B: FOLFormula ) {
  def sequent = FSequent( gamma, List( B ) )

  def instanceSequent( n: Int ) = {
    val instSubst = Substitution( alphaVar, numeral( n ) )
    FSequent( gamma map ( instSubst( _ ) ), List( instSubst( B ) ) )
  }
}

case class SimpleLoopProblem( val loop: ForLoop, val gamma: Seq[FOLFormula], val precondition: FOLFormula, val postcondition: FOLFormula ) {
  val programVariables = usedVariables( loop.body ).distinct diff List( loop.indexVar, loop.limit )

  def stateFunctionSymbol( programVariable: Var ): String = programVariable match { case FOLVar( sym ) => s"sigma_$sym" }

  def varsAtTime( i: FOLTerm ): List[( Var, FOLTerm )] =
    programVariables map { v => v -> FOLFunction( stateFunctionSymbol( v ), List( i ) ) }

  def pi: FOLFormula =
    Substitution( varsAtTime( loop.indexVar ) )(
      weakestPrecondition( loop.body,
        And( varsAtTime( FOLFunction( "s", List( loop.indexVar ) ) ) map {
          case ( v, s ) => Equation( s, v )
        } ) ) )

  def Pi: FOLFormula = AllVar( loop.indexVar, pi )

  def A: FOLFormula = Substitution( varsAtTime( numeral( 0 ) ) )( precondition )
  def B: FOLFormula = Substitution( varsAtTime( loop.limit ) )( postcondition )

  def associatedSip = SimpleInductionProblem( gamma ++ List( Pi, A ), loop.limit, B )

  // TODO: instantiate Pi
  def instanceSequent( n: Int ) = associatedSip.instanceSequent( n )
}
