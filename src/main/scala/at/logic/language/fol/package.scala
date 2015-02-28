package at.logic.language

import at.logic.language.lambda.LambdaExpression

package object fol {
  type FOLFormula = LambdaExpression
  type FOLTerm = LambdaExpression
  type FOLExpression = LambdaExpression
}
