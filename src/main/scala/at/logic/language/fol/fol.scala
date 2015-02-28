/*
 * fol.scala
 */

package at.logic.language.fol

import at.logic.language.lambda.{Var, LambdaExpression, Const}
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._

object FOLVar {
  def apply(name: String): Var = FOLVar(StringSymbol(name))
  def apply(sym: SymbolA): Var = Var(sym, Ti)
  def unapply(exp: LambdaExpression): Option[String] = exp match {
    case Var(name, Ti) => Some(name)
    case _ => None
  }
}

object FOLConst {
  def apply(name: String): Const = FOLConst(StringSymbol(name))
  def apply(sym: SymbolA): Const = Const(sym, Ti)
  def unapply(exp: LambdaExpression): Option[String] = exp match {
    case Const(name, Ti) => Some(name)
    case _ => None
  }
}

private[fol]
class FOLLambdaConst(sym: SymbolA, ty: TA) extends Const(sym, ty)
object FOLLambdaConst {
  def apply(sym: SymbolA, ty: TA) = new FOLLambdaConst(sym, ty)
}

// FOL atom of the form P(t_1,...,t_n)
object FOLAtom {
  def apply( head: String, args: List[FOLTerm] ): FOLFormula = 
    FOLAtom(StringSymbol(head), args)
  def apply( head: String ): FOLFormula = FOLAtom(head, List())
  def apply( head: SymbolA, args: List[FOLTerm] ): FOLFormula =
    Atom(FOLLambdaConst(head, FunctionType(To, args.map(_ => Ti))), args)
  def apply( head: SymbolA ):FOLFormula = FOLAtom(head, List())

  def unapply( expression: FOLExpression ) = expression match {
    case Atom(c : Const, args) => Some(c.sym, args)
    case _ => None
  }
}

// FOL function of the form f(t_1,...,t_n)
object FOLFunction {
  def apply( head: String, args: List[FOLTerm] ): FOLFormula =
    FOLFunction(StringSymbol(head), args)
  def apply( head: String ): FOLFormula = FOLFunction(head, List())
  def apply( head: SymbolA, args: List[FOLTerm] ): FOLFormula =
    Function(FOLLambdaConst(head, FunctionType(Ti, args.map(_ => Ti))), args)
  def apply( head: SymbolA ): FOLFormula = FOLFunction(head, List())

  def unapply( expression: FOLExpression ) = expression match {
    case Function(c : Const, args, Ti) => Some(c.sym, args)
    case _ => None
  }
}

