package at.logic.algorithms.lksk

import at.logic.language.lambda.{Substitution, Const, Var, App}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base.{Sequent, FSequent}
import at.logic.calculi.lksk._
import at.logic.calculi.lksk.TypeSynonyms._
import at.logic.language.lambda.types._

import scala.App

@RunWith(classOf[JUnitRunner])
class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    val f = Const("f", Ti -> Ti)
    val y = Var("y", Ti)
    val x = Var("x", Ti)
    val a = Var("a", Ti)
    val fa = App(f, a)
    val R = Const("R", Ti -> (Ti -> To))
    val Rafa = Atom(R, a::fa::Nil)
    val exyRay = ExVar(y, Atom(R, a::y::Nil ))
    val allxexy = AllVar(x, ExVar( y, Atom(R, x::y::Nil ) ) )

    val ax = Axiom.createDefault(new FSequent(Rafa::Nil, Rafa::Nil), Tuple2( (EmptyLabel() + a)::Nil , EmptyLabel()::Nil ) )
    val r1 = ExistsSkLeftRule(ax._1, ax._2._1.head, exyRay, fa)
    val r2 = ForallSkLeftRule(r1, r1.prin.head, allxexy, a, true)
    r2.root.antecedent.toList.head must beLike {case o: LabelledFormulaOccurrence => ok}
    r2.root.succedent.toList.head must beLike {case o: LabelledFormulaOccurrence => ok}

    "work for an axiom" in {
      val P = Const("P", Ti -> To)
      val Px = Atom(P, x::Nil)
      val c : HOLExpression = Const("c", Ti)
      val Pc = Atom(P, c::Nil)

      val a = Axiom.createDefault(new FSequent( Px::Nil, Px::Nil ), Tuple2( (EmptyLabel() + x)::Nil, (EmptyLabel() + y)::Nil ) )
      val subst = Substitution(x, c)
      val r = applySubstitution(a._1, subst)
      r._1.root.succedent.toList.head must beLike {case o : LabelledFormulaOccurrence => o.skolem_label == (EmptyLabel() + y) && o.formula == Pc must_== true }
      r._1.root.antecedent.toList.head must beLike {case o : LabelledFormulaOccurrence => o.skolem_label == (EmptyLabel() + c) && o.formula == Pc must_== true }
    }

    "apply correctly to a simple proof" in {
      val c = Const("c", Ti)
      val g = Const("g", Ti -> Ti)
      val gc = App(g, c)
      val fgc = App(f, gc)
      val R = Const("R", Ti -> (Ti -> To))
      val Rgcfgc = Atom(R, gc::fgc::Nil )
      val exyRgcy = ExVar(y, Atom(R, gc::y::Nil ) )
      val subst = Substitution( a, gc ) // a <- g(c)

      val p_s = applySubstitution( r2, subst )
      p_s._1.root.antecedent.toList.head must beLike{ case o : LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == allxexy must_== true }
      p_s._1.root.succedent.toList.head must beLike{ case o : LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == Rgcfgc must_== true }
    }
  }
}
