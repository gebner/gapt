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
    "work for some simple terms" in {
      val fterm = fol.FOLFunction("f", List(
                    fol.FOLConst("q1"),
                    fol.FOLVar("x")))
      val hterm = fol2hol(fterm)
      ok
    }

    "allow substitution of a fol term into a hol term" in {
      val p = Const("P", Ti -> ((Ti -> Ti) -> To))
      val x = Var("x", Ti)
      val y = Var("y", Ti)

      val hterm = hol.Atom(Const("P", Ti -> ((Ti -> Ti) -> To)),List(y, Abs(x,x)))

      val fterm = fol.FOLConst("c")

      val fsub = Substitution(fol.FOLVar("y"), fterm)


      /*TODO: Martin expected this to fail, but it doesn't (app takes the factory of the first parameter, which is fol
        after the substitution, so the lambda x.x should be created by the fol factory and fail).

        in the new lambda calculus, this really fails as expected
       */
      //val sterm = fsub(hterm)
      //sterm.factory must beEqualTo(HOLFactory) //surprisingly enough, this does not fail

      //println(sterm)
      //TODO: add tests for converting substitutions back in
      //val f2hterm = fol2hol(fsub.asInstanceOf[Substitution[fol.FOLExpression]])(hterm)

      //f2hterm.factory must beEqualTo(hol.HOLFactory)

      //recreateWithFactory(fsub, hol.HOLFactory)(hterm).factory must beEqualTo(hol.HOLFactory)
      ok
    }

    //TODO: add test cases
  }
}
