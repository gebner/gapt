package at.logic.parsing.language.tptp

import at.logic.language.lambda.{Const, Var}
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.execute.Success
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.FSequent

class TPTPHOLExporterTest extends SpecificationWithJUnit {
  "Export to TPTP thf" should {
    "handle atoms correctly" in {
      val x = Var("x", Ti -> To)
      val y = Var("y", To)
      val c = Const("c", Ti)

      val ax = Atom(x, List(c))
      val ay = Atom(y)

      println(TPTPHOLExporter(List(FSequent(Nil, List(ax,ay)))))

      println(TPTPHOLExporter(List(FSequent(List(ax), Nil),
                                   FSequent(Nil, List(ay)))))
      ok
    }
  }

}
