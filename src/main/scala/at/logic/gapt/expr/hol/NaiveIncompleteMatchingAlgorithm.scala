package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.expr.substitution.Substitution

object NaiveIncompleteMatchingAlgorithm {

  def matchTerm( term: LambdaExpression, posInstance: LambdaExpression ): Option[Substitution] =
    syntacticMatching( term, posInstance )

  // restrictedDomain: variables to be treated as constants.
  def matchTerm( term: LambdaExpression, posInstance: LambdaExpression, restrictedDomain: Set[Var] ): Option[Substitution] =
    syntacticMatching( List( term -> posInstance ), restrictedDomain.map { v => v -> v }.toMap )
}
