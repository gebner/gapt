/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language.lambda

import symbols._
import types._

// Collects all methods that operate on LambdaExpressions
abstract class LambdaExpression {

  // Expression type [should it be here?]
  def exptype: TA

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ): Boolean

  // Alpha equality
  def alphaEquals( a: Any, subs: Map[Var, Var] ): Boolean

  /**
   * Tests whether this Expression has a subexpression at the given position.
   *
   * @param p
   * @return
   */
  def isDefinedAt( p: LambdaPosition ): Boolean

  /**
   * Returns the subexpression at the given position, if it exists.
   *
   * @param p
   * @return
   */
  def get( p: LambdaPosition ): Option[LambdaExpression]

  def apply( p: LambdaPosition ): LambdaExpression = get( p ) match {
    case Some( e ) => e
    case None      => throw new IllegalArgumentException( "Expression " + this + "is not defined at position " + p + "." )
  }

  import at.logic.language.hol.logicSymbols._
  import at.logic.language.hol._
  import at.logic.language.fol._
  override def toString: String = this match {
    case AllVar( Var( name, Ti ), sub ) => s"$ForallSymbol$name. $sub"
    case AllVar( Var( name, ty ), sub ) => s"$ForallSymbol$name:$ty. $sub"
    case ExVar( Var( name, Ti ), sub )  => s"$ExistsSymbol$name. $sub"
    case ExVar( Var( name, ty ), sub )  => s"$ExistsSymbol$name:$ty. $sub"
    case And( x, y )                    => s"($x $AndSymbol $y)"
    case Or( x, y )                     => s"($x $OrSymbol $y)"
    case Imp( x, y )                    => s"($x $ImpSymbol $y)"
    case Neg( x )                       => s"$NegSymbol$x"
    case BottomC                        => s"$BottomSymbol"
    case TopC                           => s"$TopSymbol"

    case Equation( x, y )               => s"$x = $y"
    case FOLFunction( name, Nil )       => s"$name"
    case FOLAtom( name, Nil )           => s"$name"
    case FOLFunction( name, args )      => s"$name(${args.mkString( ", " )})"
    case FOLAtom( name, args )          => s"$name(${args.mkString( ", " )})"

    case Var( name, ty )                => name
    case Const( name, ty )              => name
    case Abs( Var( name, ty ), sub )    => s"λ$name:$ty. $sub"
    case App( x, y )                    => s"($x $y)"
  }

}

// Defines the elements that generate lambda-expressions: variables,
// applications and abstractions (and constants).

class Var( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  // The name of the variable should be obtained with this method.
  def name: String = sym.toString

  override def equals( a: Any ) = alphaEquals( a, Map[Var, Var]() )

  // Syntactic equality: two variables are equal if they have the same name and the same type
  def syntaxEquals( e: LambdaExpression ) = e match {
    case Var( n, t ) => ( n == name && t == exptype )
    case _           => false
  }

  // Alpha-equality
  // Two free variables are *not* alpha-equivalent if they don't have the same
  // name and type or if they are not in the substitution list because of a
  // binding.
  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Var( n, t ) if !subs.contains( this )    => ( n == name && t == exptype )
    case v: Var if subs( this ).syntaxEquals( v ) => true
    case _                                        => false
  }

  // Printing
  //  override def toString() = "Var(" + name + "," + exptype + ")"

  /* hash code needs to be equal modulo alpha equality. ignoring the variable name might reduce the efficency of HashMap,
     but it fulfills the contract that : x equals y implies x.hashCode == y.hashCode
   */
  override def hashCode() = 41 * "Var".hashCode + exptype.hashCode

  def isDefinedAt( pos: LambdaPosition ) = pos.isEmpty
  def get( pos: LambdaPosition ) = if ( pos.isEmpty ) Some( this ) else None
}
object Var {
  def apply( name: String, exptype: TA ): Var = Var( StringSymbol( name ), exptype )
  def apply( name: String, exptype: String ): Var = Var( StringSymbol( name ), Type( exptype ) )
  def apply( sym: SymbolA, exptype: TA ): Var = new Var( sym, exptype )
  def apply( sym: SymbolA, exptype: String ): Var = Var( sym, Type( exptype ) )
  def unapply( e: LambdaExpression ) = e match {
    case v: Var => Some( v.name, v.exptype )
    case _      => None
  }
}

class Const( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  // The name of the variable should be obtained with this method.
  def name: String = sym.toString

  override def equals( a: Any ) = alphaEquals( a, Map[Var, Var]() )

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ) = e match {
    case Const( n, t ) => ( n == name && t == exptype )
    case _             => false
  }

  // Alpha-equality
  // Two constants are *not* alpha-equivalent if they don't have the same name and type.
  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Const( n, t ) => n == name && t == exptype
    case _             => false
  }

  // Printing
  //  override def toString() = "Const(" + name + "," + exptype + ")"

  override def hashCode() = ( 41 * name.hashCode ) + exptype.hashCode

  def isDefinedAt( pos: LambdaPosition ) = pos.isEmpty
  def get( pos: LambdaPosition ) = if ( pos.isEmpty ) Some( this ) else None
}
object Const {
  def apply( name: String, exptype: TA ): Const = Const( StringSymbol( name ), exptype )
  def apply( name: String, exptype: String ): Const = Const( StringSymbol( name ), Type( exptype ) )
  def apply( sym: SymbolA, exptype: TA ): Const = new Const( sym, exptype )
  def apply( sym: SymbolA, exptype: String ): Const = Const( sym, Type( exptype ) )
  def unapply( e: LambdaExpression ) = e match {
    case c: Const => Some( c.name, c.exptype )
    case _        => None
  }
}

class App( val function: LambdaExpression, val arg: LambdaExpression ) extends LambdaExpression {

  // Making sure that if f: t1 -> t2 then arg: t1
  require( {
    function.exptype match {
      case ->( in, out ) => {
        if ( in == arg.exptype ) true
        else false
      }
      case _ => false
    }
  }, "Types don't fit while constructing application " + function + " " + arg )

  // Application type (if f: t1 -> t2 and arg: t1 then t2)
  def exptype: TA = {
    function.exptype match {
      case ->( in, out ) => out
    }
  }

  override def equals( a: Any ) = alphaEquals( a, Map[Var, Var]() )

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ) = e match {
    case App( a, b ) => ( a.syntaxEquals( function ) && b.syntaxEquals( arg ) && e.exptype == exptype )
    case _           => false
  }

  // Alpha-equality
  // An application is alpha-equivalent if its terms are alpha-equivalent.
  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case App( e1, e2 ) => e1.alphaEquals( function, subs ) && e2.alphaEquals( arg, subs )
    case _             => false
  }

  // Printing
  //  override def toString() = "App(" + function + "," + arg + ")"

  override def hashCode() = ( 41 * function.hashCode ) + arg.hashCode

  def isDefinedAt( pos: LambdaPosition ) = if ( pos.isEmpty ) true else {
    val rest = pos.tail
    pos.head match {
      case 1 => function isDefinedAt rest
      case 2 => arg isDefinedAt rest
      case _ => false
    }
  }
  def get( pos: LambdaPosition ) = if ( pos.isEmpty ) Some( this ) else {
    val rest = pos.tail
    pos.head match {
      case 1 => function.get( rest )
      case 2 => arg.get( rest )
      case _ => None
    }
  }
}
object App {
  def apply( f: LambdaExpression, a: LambdaExpression ) = new App( f, a )
  // create an n-ary application with left-associative parentheses
  def apply( function: LambdaExpression, arguments: List[LambdaExpression] ): LambdaExpression = arguments match {
    case Nil     => function
    case x :: ls => apply( App( function, x ), ls )
  }
  def unapply( e: LambdaExpression ) = e match {
    case a: App => Some( ( a.function, a.arg ) )
    case _      => None
  }
}

class Abs( val variable: Var, val term: LambdaExpression ) extends LambdaExpression {

  // Abstraction type construction based on the types of the variable and term
  def exptype: TA = ->( variable.exptype, term.exptype )

  override def equals( a: Any ) = alphaEquals( a, Map[Var, Var]() )

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ) = e match {
    case Abs( v, exp ) => v.syntaxEquals( variable ) && exp.syntaxEquals( term ) && e.exptype == exptype
    case _             => false
  }

  // Alpha-equality
  // Two abstractions are alpha-equivalent if the terms are equivalent up to the
  // renaming of variables.
  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Abs( v, t ) =>
      if ( v.exptype == variable.exptype ) {
        t.alphaEquals( term, subs + ( variable -> v ) + ( v -> variable ) )
      } else false
    case _ => false
  }

  // Printing
  //  override def toString() = "Abs(" + variable + "," + term + ")"

  /* hash code needs to be equal modulo alpha equality. ignoring the variable name might reduce the efficency of HashMap,
     but it fulfills the contract that : x equals y implies x.hashCode == y.hashCode
   */
  override def hashCode() = 41 * "Abs".hashCode + term.hashCode

  def isDefinedAt( pos: LambdaPosition ) =
    if ( pos.isEmpty ) true
    else if ( pos.head == 1 ) term isDefinedAt pos.tail
    else false

  def get( pos: LambdaPosition ) =
    if ( pos.isEmpty ) Some( this )
    else if ( pos.head == 1 ) term.get( pos.tail )
    else None
}
object Abs {
  def apply( v: Var, t: LambdaExpression ) = new Abs( v, t )
  def apply( variables: List[Var], expression: LambdaExpression ): LambdaExpression = variables match {
    case Nil     => expression
    case x :: ls => Abs( x, apply( ls, expression ) )
  }
  def unapply( e: LambdaExpression ) = e match {
    case a: Abs => Some( ( a.variable, a.term ) )
    case _      => None
  }
}
