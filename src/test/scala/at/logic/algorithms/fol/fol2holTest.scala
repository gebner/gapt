package at.logic.algorithms.fol

import at.logic.language.lambda.{Substitution, Abs, Var, Const}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol
import at.logic.language.hol
import at.logic.language.lambda.types.{To, Ti}

/**
 * Created by marty on 3/10/14.
 */
@RunWith(classOf[JUnitRunner])
class fol2holTest extends SpecificationWithJUnit {
  "Conversion from fol to hol" should {
    "allow substitution of a fol term into a hol term" in {
      val p = Const("P", Ti -> ((Ti -> Ti) -> To))
      val x = Var("x", Ti)
      val y = Var("y", Ti)

      val hterm = hol.Atom(Const("P", Ti -> ((Ti -> Ti) -> To)),List(y, Abs(x,x)))

      val fterm = fol.FOLConst("c")

      val fsub = Substitution(fol.FOLVar("y"), fterm)


      fsub(hterm)
      ok
    }

    //TODO: add test cases
  }
}
