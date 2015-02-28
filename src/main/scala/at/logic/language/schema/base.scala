/*
 *
 * Schema's mini lambda-calculus and factory
 *
 */

package at.logic.language

import at.logic.language.hol.{Atom, Function}
import at.logic.language.lambda.{ LambdaExpression, Var, Const, App, Abs, FactoryA }
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._

package object schema {
  type SchemaFormula = LambdaExpression
  type SchemaExpression = LambdaExpression
  type IntegerTerm = LambdaExpression
}

