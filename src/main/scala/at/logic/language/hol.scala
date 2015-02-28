/*
 * hol.scala
 */

package at.logic.language.hol

import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.replacements.getAtPosition
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.hol.HOLPosition._

class HOLExpressionHelper( val exp: LambdaExpression ) extends AnyVal {

  def arity: Int = exp match {
    case Var( _, _ ) | Const( _, _ )               => 0
    case Neg( _ ) | AllVar( _, _ ) | ExVar( _, _ ) => 1
    case BinaryConnective( _, _ )                  => 2
    case Atom( _, args )                           => args.length
    case Function( _, args, _ )                    => args.length
    case Abs( _, _ )                               => 1
    case _                                         => throw new Exception( "Unhandled HOLExpression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: HOLPosition ): HOLExpression = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: HOLPosition ): Option[HOLExpression] = exp.get( toLambdaPosition( exp )( pos ) )

  /**
   * Tests whether this expression has a subexpression at a given position.
   *
   * @param pos The position to be tested.
   * @return Whether this(pos) is defined.
   */
  def isDefinedAt( pos: HOLPosition ): Boolean = toLambdaPositionOption( exp )( pos ) match {
    case Some( _ ) => true
    case None      => false
  }

  /**
   * Finds all positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find( other: HOLExpression ): List[HOLPosition] = getPositions( exp, _ == other )

}

object ImplicitConversions {
  implicit def expressionToHol( exp: LambdaExpression ): HOLExpressionHelper = new HOLExpressionHelper( exp )
  implicit def holToExpression( exp: HOLExpressionHelper ): LambdaExpression = exp.exp
}

trait LogicalConstant

object BottomC extends Const( BottomSymbol, To ) with LogicalConstant
object TopC extends Const( TopSymbol, To ) with LogicalConstant
object NegC extends Const( NegSymbol, To -> To ) with LogicalConstant
object AndC extends Const( AndSymbol, To -> ( To -> To ) ) with LogicalConstant
object OrC extends Const( OrSymbol, To -> ( To -> To ) ) with LogicalConstant
object ImpC extends Const( ImpSymbol, To -> ( To -> To ) ) with LogicalConstant

class EqC( val e: TA ) extends Const( EqSymbol, e -> ( e -> To ) )
object EqC {
  def apply( e: TA ) = new EqC( e )
  def unapply( exp: LambdaExpression ) = exp match {
    case eqC: EqC                          => Some( eqC.e )

    // FIXME: FOLAtom("=", List(x,y)) is actually used...
    case c: Const if c.sym.toString == "=" => Some( null )

    case _                                 => None
  }
}

// We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
object Neg {
  def apply( sub: LambdaExpression ): LambdaExpression = App( NegC, sub )
  def unapply( expression: LambdaExpression ): Option[LambdaExpression] = expression match {
    case App( NegC, sub ) => Some( sub )
    case _                => None
  }
}

object And {
  def apply( fs: List[LambdaExpression] ): LambdaExpression = fs match {
    case Nil     => TopC
    case f :: fs => fs.foldLeft( f )( ( d, f ) => And( d, f ) )

  }
  def apply( left: LambdaExpression, right: LambdaExpression ): LambdaExpression = App( App( AndC, left ), right )
  def unapply( expression: LambdaExpression ) = expression match {
    case App( App( AndC, left ), right ) => Some( left, right )
    case _                               => None
  }
}

object Or {
  def apply( fs: List[LambdaExpression] ): LambdaExpression = fs match {
    case Nil     => BottomC
    case f :: fs => fs.foldLeft( f )( ( d, f ) => Or( d, f ) )
  }
  def apply( left: LambdaExpression, right: LambdaExpression ) = App( App( OrC, left ), right )
  def unapply( expression: HOLExpression ) = expression match {
    case App( App( OrC, left ), right ) => Some( left, right )
    case _                              => None
  }
}

object Imp {
  def apply( left: LambdaExpression, right: LambdaExpression ) =
    App( App( ImpC, left ), right ).asInstanceOf[LambdaExpression]
  def unapply( expression: HOLExpression ) = expression match {
    case App( App( ImpC, left ), right ) => Some( left, right )
    case _                               => None
  }
}

object Equation {
  def apply( left: LambdaExpression, right: LambdaExpression ) = {
    require( left.exptype == right.exptype )
    App( App( EqC( left.exptype ), left ), right )
  }
  def unapply( expression: HOLExpression ) = expression match {
    case App( App( EqC( _ ), left ), right ) => Some( left, right )
    case _                                   => None
  }
}

object FunctionLike {
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): LambdaExpression = args match {
    case Nil     => head
    case t :: tl => Function( App( head, t ), tl )
  }

  def unapply( e: LambdaExpression ): Option[( LambdaExpression, List[LambdaExpression] )] = e match {
    case v: Var                          => Some( ( v, Nil ) )
    case c: Const                        => Some( ( c, Nil ) )
    case App( FunctionLike( x, y ), e2 ) => Some( ( x, y :+ e2 ) )
    case _                               => None
  }
}

object Function {
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): LambdaExpression = FunctionLike( head, args )

  def unapply( expression: LambdaExpression ) = expression match {
    case FunctionLike( _: LogicalConstant, _ ) => None
    case FunctionLike( head, args ) if expression.exptype != To =>
      Some( ( head, args, expression.exptype ) )
    case _ => None
  }
}

// HOL formulas of the form P(t_1,...,t_n)
object Atom {
  def apply( head: LambdaExpression ): LambdaExpression = Atom( head, List() )
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): LambdaExpression = FunctionLike( head, args )

  def unapply( expression: LambdaExpression ) = expression match {
    // Bottom and top are atoms
    case c @ ( TopC | BottomC ) => Some( c, Nil )
    case FunctionLike( _: LogicalConstant, _ ) => None
    case FunctionLike( head @ ( Var( _, _ ) | Const( _, _ ) ), args ) if expression.exptype == To => Some( ( head, args ) )
    case _ => None
  }
}

class ExQ( val e: TA ) extends Const( ExistsSymbol, ( e -> To ) -> To ) with LogicalConstant
class AllQ( val e: TA ) extends Const( ForallSymbol, ( e -> To ) -> To ) with LogicalConstant

object ExQ {
  def apply( e: TA ) = new ExQ( e )
  def unapply( exp: LambdaExpression ) = exp match {
    case exQ: ExQ => Some( exQ.e )
    case _        => None
  }
}

object AllQ {
  def apply( e: TA ) = new AllQ( e )
  def unapply( exp: LambdaExpression ) = exp match {
    case allQ: AllQ => Some( allQ.e )
    case _          => None
  }
}

object ExVar {
  def apply( variable: Var, sub: LambdaExpression ) = App( ExQ( variable.exptype ), Abs( variable, sub ) )
  // TODO: eta-expand?
  def unapply( expression: HOLExpression ) = expression match {
    case App( ExQ( _ ), Abs( variable, sub ) ) => Some( variable, sub )
    case _                                     => None
  }
}

object AllVar {
  def apply( variable: Var, sub: LambdaExpression ) = App( AllQ( variable.exptype ), Abs( variable, sub ) )
  // TODO: eta-expand?
  def unapply( expression: LambdaExpression ) = expression match {
    case App( AllQ( _ ), Abs( variable, sub ) ) => Some( variable, sub )
    case _                                      => None
  }
}

/**
 * A block of existential quantifiers.
 *
 */
object ExVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply( vars: List[Var], sub: LambdaExpression ): LambdaExpression = vars match {
    case Nil     => sub
    case v :: vs => ExVar( v, ExVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ): Option[( List[Var], LambdaExpression )] = expression match {
    case ExVar( v, ExVarBlock( vs, sub ) ) => Some( v :: vs, sub )
    case ExVar( v, sub )                   => Some( List( v ), sub )
    case _                                 => None
  }
}

/**
 * A block of universal quantifiers.
 *
 */
object AllVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply( vars: List[Var], sub: LambdaExpression ): LambdaExpression = vars match {
    case Nil     => sub
    case v :: vs => AllVar( v, AllVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ): Option[( List[Var], LambdaExpression )] = expression match {
    case AllVar( v, AllVarBlock( vs, sub ) ) => Some( v :: vs, sub )
    case AllVar( v, sub )                    => Some( List( v ), sub )
    case _                                   => None
  }
}