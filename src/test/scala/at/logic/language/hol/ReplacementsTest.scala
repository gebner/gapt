/*
 * ReplacementsTest.scala
 *
 */

package at.logic.language.hol.replacements

import at.logic.language.lambda.Const
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class ReplacementsTest extends SpecificationWithJUnit {
  "Replacements" should {
    "work correctly on" in {
      "Atoms" in {
        val a = Const("a", Ti)
        val b = Const("b", Ti)
        val P = Const("P", Ti -> To)
        val atom1 = Atom(P, a::Nil)
        val atom2 = Atom(P, b::Nil)
        val pos = List(1)
        val rep = Replacement(pos, b)
        (rep.apply(atom1)) must beEqualTo (atom2)
      }
    }
  }
}
