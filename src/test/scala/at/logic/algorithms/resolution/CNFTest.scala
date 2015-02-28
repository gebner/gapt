package at.logic.algorithms.resolution

import at.logic.language.fol.{FOLAtom, FOLConst}
import at.logic.language.hol.{Imp, And, Or, Neg}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.calculi.resolution.FClause

@RunWith(classOf[JUnitRunner])
class CNFTest extends SpecificationWithJUnit {
  "the computation of CNFp(f)" should {
    "be {|- Pa,Qa, Qa|-} for f = (Pa ∨ Qa) ∧ ¬Qa" in {
      val Pa = FOLAtom("P", FOLConst("a")::Nil)
      val Qa = FOLAtom("Q", FOLConst("a")::Nil)
      val nQa = Neg(Qa)
      val PavQa = Or(Pa,Qa)
      val f = And(PavQa, nQa)
      CNFp(f).toSet must beEqualTo(Set(FClause(List(),List(Pa,Qa)),FClause(List(Qa),List())))
    }
  }

  "the computation of TseitinCNF(f)" should {
    "should be right, where f = ((P ∨ Q) ∧ R ) -> ¬S" in {
      val p = FOLAtom("P", Nil)
      val q = FOLAtom("Q", Nil)
      val r = FOLAtom("R", Nil)
      val s = FOLAtom("S", Nil)

      val f = Imp(And(Or(p, q), r), Neg(s))

      val x =  FOLAtom("x", Nil)
      val x0 = FOLAtom("x0", Nil)
      val x1 = FOLAtom("x1", Nil)
      val x2 = FOLAtom("x2", Nil)

      val cnf = TseitinCNF(f)
      val expected = Set(
        FClause(List(), List(x2)),
        FClause(List(x1), List(x2)),
        FClause(List(), List(x2, x0)),
        FClause(List(), List(x1, s)),
        FClause(List(x1, s), List()),
        FClause(List(x0), List(r)),
        FClause(List(x0), List(x)),
        FClause(List(q), List(x)),
        FClause(List(p), List(x)),
        FClause(List(x2, x0), List(x1)),
        FClause(List(x, r), List(x0)),
        FClause(List(x), List(p, q))
      )
      cnf._1.toSet must beEqualTo(expected)
    }
  }
}
