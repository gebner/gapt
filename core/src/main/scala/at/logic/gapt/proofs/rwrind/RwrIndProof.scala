package at.logic.gapt.proofs.rwrind

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.provers.escargot.impl.getFOPositions

trait RwrIndProof extends SequentProof[Atom, RwrIndProof] {

}

trait ContextRwrIndRule extends RwrIndProof with ContextRule[Atom, RwrIndProof]

case class Input(eqn: Atom) extends ContextRwrIndRule {
  def mainFormulaSequent= Sequent() :+ eqn
  def auxIndices = Seq()
  def immediateSubProofs = Seq()
}

case class Lemma(subProof: RwrIndProof, eqn: Atom) extends ContextRwrIndRule {
  def mainFormulaSequent = Sequent() :+ eqn
  def auxIndices = Seq(Seq())
  def immediateSubProofs = Seq(subProof)
}

case class Simplify(subProof: RwrIndProof, aux: SequentIndex, to: Atom) extends ContextRwrIndRule {
  require(aux.isSuc)

  def mainFormulaSequent = Sequent() :+ to
  def auxIndices = Seq(Seq(aux))
  def immediateSubProofs = Seq(subProof)

  def auxFormula = auxFormulas.head.head
}

object SimplifyMacro {
  def apply(subProof: RwrIndProof, aux: SequentIndex, theory: Iterable[Atom]) = {
    val eqns = subProof.conclusion.antecedent ++ theory

    var to:Expr = subProof.conclusion(aux)
    var didRewrite = false
    do {
      didRewrite = false
      for {
        (subterm, pos) <- getFOPositions(to) if !didRewrite
        Eq(lhs, rhs) <- eqns if !didRewrite
        subst <- syntacticMatching(lhs, subterm)
      } {
        for ( p <- pos ) to = to.replace( p, subst( rhs ) )
        didRewrite = true
      }
    } while(didRewrite)

    Simplify(subProof, aux, to.asInstanceOf[Atom])
  }
}

case class Expand(subProof: RwrIndProof, aux: SequentIndex,
                  ltr: Boolean,
                  basicSubTerm: Expr, eqns: Vector[Atom]) extends ContextRwrIndRule {
  require(aux.isSuc)

  val auxFormula= subProof.conclusion(aux)
  val rwrCtx = replacementContext.abstractTerm(auxFormula)(basicSubTerm)

  private def freshVars(eqn: Atom): Atom =
    Substitution(rename(freeVariables(eqn), freeVariables(auxFormula)))(eqn).asInstanceOf[Atom]

  val newEqs =
    for {
      Eq(l,r) <- eqns.map(freshVars)
      subst <- syntacticMGU(l, basicSubTerm)
    } yield BetaReduction.betaNormalize(subst(rwrCtx(r))).asInstanceOf[Atom]

  val newRule =
    auxFormula match {
      case Eq(l, r) =>
        if (ltr) l === r else r === l
    }

  def mainFormulaSequent = newRule +: Sequent() :++ newEqs
  def auxIndices = Seq(Seq(aux))
  def immediateSubProofs = Seq(subProof)
}

case class Refl(subProof: RwrIndProof, aux: SequentIndex) extends ContextRwrIndRule {
  require(aux.isSuc)
  subProof.conclusion(aux) match {
    case Eq(t, t_) => require(t == t_)
    case a => throw new MatchError(a)
  }

  def mainFormulaSequent = Sequent()
  def auxIndices = Seq(Seq(aux))
  def immediateSubProofs = Seq(subProof)
}

case class Contract(subProof: RwrIndProof, aux1: SequentIndex, aux2: SequentIndex) extends ContextRwrIndRule {
  require(aux1 sameSideAs aux2)
  val formula = subProof.conclusion(aux1)
  require (formula == subProof.conclusion(aux2))

  def mainFormulaSequent = Sequent() :+ formula
  def auxIndices = Seq(Seq(aux1,aux2))
  def immediateSubProofs = Seq(subProof)
}

object ContractMacro {
  def apply(subProof: RwrIndProof): RwrIndProof = {
    for {
      (a, i) <- subProof.conclusion.zipWithIndex.elements
      (b, j) <- subProof.conclusion.zipWithIndex.elements
      if i sameSideAs j
    if i != j
      if a == b
    } return apply(Contract(subProof, i ,j))

    subProof
  }
}
