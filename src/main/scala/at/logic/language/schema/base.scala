package at.logic.language

import at.logic.language.lambda.LambdaExpression

package object schema {
  type SchemaFormula = LambdaExpression
  type SchemaExpression = LambdaExpression
  type IntegerTerm = LambdaExpression
}

