package at.logic.language.hoare

import at.logic.language.fol._
import at.logic.language.hol.{Neg, Imp, And}
import at.logic.language.lambda.{Substitution, Var, freeVariables}

object usedVariables {
  def apply( p: Program ): List[Var] = p match {
    case Assign( x, t )     => x :: freeVariables( t )
    case IfElse( c, a, b )  => freeVariables( c ) ++ usedVariables( a ) ++ usedVariables( b )
    case ForLoop( i, n, b ) => i :: n :: usedVariables( b )
    case Skip()             => Nil
    case Sequence( a, b )   => usedVariables( a ) ++ usedVariables( b )
  }
}

object mapVariableNames {
  def apply( p: Program, f: String => String ): Program =
    substVariables( p, ( x: Var ) => FOLVar( f( x.name ) ) )
}

object substVariables {
  def apply( p: Program, f: Map[Var, FOLExpression] ): Program =
    apply( p, ( x: Var ) => f.getOrElse( x, x ) )

  def apply( p: Program, f: Var => FOLExpression ): Program = p match {
    case Assign( x, t )     => Assign( f( x ).asInstanceOf[Var], apply( t, f ) )
    case IfElse( c, a, b )  => IfElse( apply( c, f ), apply( a, f ), apply( b, f ) )
    case ForLoop( i, n, b ) => ForLoop( f( i ).asInstanceOf[Var], f( n ).asInstanceOf[Var], apply( b, f ) )
    case Skip()             => Skip()
    case Sequence( a, b )   => Sequence( apply( a, f ), apply( b, f ) )
  }

  def apply( t: FOLTerm, f: Var => FOLExpression ): FOLTerm = makeSubstitution( t, f )( t )

  private def makeSubstitution( t: FOLExpression, f: Var => FOLExpression ) =
    Substitution( freeVariables( t ) map ( ( x: Var ) => x -> f( x ) ) )
}

object LoopFree {
  def unapply( p: Program ): Option[Program] = p match {
    case Assign( _, _ )                            => Some( p )
    case IfElse( _, LoopFree( _ ), LoopFree( _ ) ) => Some( p )
    case Skip()                                    => Some( p )
    case Sequence( LoopFree( _ ), LoopFree( _ ) )  => Some( p )
    case _                                         => None
  }
}

object weakestPrecondition {
  def apply( p: Program, f: FOLFormula ): FOLFormula = p match {
    case Assign( x, t )    => Substitution( x, t )( f )
    case IfElse( c, a, b ) => And( Imp( c, weakestPrecondition( a, f ) ), Imp( Neg( c ), weakestPrecondition( b, f ) ) )
    case Skip()            => f
    case Sequence( a, b )  => weakestPrecondition( a, weakestPrecondition( b, f ) )
  }
}