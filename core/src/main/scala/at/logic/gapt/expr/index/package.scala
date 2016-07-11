package at.logic.gapt.expr

package object index {

  implicit def substTreeAreRepl[A]: ClosedUnderReplacement[SubstitutionTree[A]] = new ClosedUnderReplacement[SubstitutionTree[A]] {
    override def replace( obj: SubstitutionTree[A], p: PartialFunction[LambdaExpression, LambdaExpression] ): SubstitutionTree[A] =
      SubstitutionTree(
        TermReplacement( obj.vars, p ).map( _.asInstanceOf[Var] ),
        TermReplacement( obj.children, p ),
        obj.leaves
      )

    override def names( obj: SubstitutionTree[A] ): Set[VarOrConst] =
      containedNames( obj.children ) ++ obj.vars
  }
}
