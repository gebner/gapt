
package at.logic.algorithms.lk

import at.logic.language.lambda.{Const, Var}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol.{FOLFormula, FOLExpression}
import at.logic.language.hol._
import at.logic.language.fol.{FOLFunction, FOLAtom, FOLVar, FOLConst}
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class SimplificationTest extends SpecificationWithJUnit {
  "Simplifications" should {
      val a = Atom(Var("a", To), List())
      val b = Atom(Var("b", To), List())
      val s1 = FSequent( a::Nil, a::Nil )
      val s2 = FSequent( b::a::b::Nil, b::b::b::a::b::Nil )
      val s3 = FSequent( a::Nil, b::Nil )
      val s4 = FSequent( b::Nil, a::Nil )

      val P = Const("P", (Ti ->Ti) -> To)
      val Q = Const("Q", (Ti -> Ti)-> To)
      val z = Var("z", Ti -> Ti)
      val z2 = Var("z2", Ti -> Ti)
      val b1 = Const("b", Ti -> Ti)
      val Pz = Atom(P, z::Nil)
      val Pz2 = Atom(P, z2::Nil)
      val Qb1 = Atom(Q, b1::Nil)

      val f1a = And(Pz, Qb1)
      val f1b = And(Pz2, Qb1)
      
      val P1 = Const("P", Ti -> To)
      val x = Var("x", Ti)
      val y = Var("y", Ti)
      val ai = Const("a", Ti)
      val b2 = Const("b", Ti)
      val f = Const("f", Ti -> (Ti -> Ti))
      val fxy = Function(f, x::y::Nil)
      val fba = Function(f, b2::ai::Nil)

      val a1 = Atom(P1, x::Nil)
      val a2 = Atom(P1, fxy::Nil)
      val a3 = Atom(P1, ai::Nil)
      val a4 = Atom(P1, b2::Nil)
      val a5 = Atom(P1, fba::Nil)

      val s9 = FSequent(Nil, a1::a2::Nil)
      val s10 = FSequent(f1a::f1b::Nil, a3::a4::a5::Nil)

    "correctly delete tautologous sequents" in {
      val list = s1::s2::s3::s4::s1::Nil
      val dlist = deleteTautologies( list )
      dlist.size must beEqualTo( 2 )
    }

    "correctly set-normalize a list of Sequents" in {
      val list = s1::s2::s2::s1::s2::s3::s1::s2::s4::s3::s2::s1::s2::s3::Nil
      val set = setNormalize( list )
      set.size must beEqualTo( 4 )
    }

    "correctly remove subsumed sequents from a set of Sequents" in {
      val a = FOLConst("a")
      val x = FOLVar("x")
      val px = FOLFunction("p", x::Nil)
      val s = FOLConst("s")

      val f1 = FOLAtom("<", a::px::Nil)
      val f2 = FOLAtom("=", x::s::Nil)
      val f3 = FOLAtom("=", a::a::Nil)
      val f4 = FOLAtom("=", x::x::Nil)
      val f5 = FOLAtom("=", x::a::Nil)

      val seq1f = FSequent(Nil, f1::Nil)
      val seq2f = FSequent(f2::Nil, f1::Nil)
      val seq3f = FSequent(Nil, f3::Nil)
      val seq4f = FSequent(Nil, f4::f5::Nil)

      "FOL" in {
        val ls = List(seq1f,seq2f,seq3f,seq4f)
        val ret = subsumedClausesRemoval( ls )
        ret.toSet must beEqualTo( Set(seq1f,seq4f) )
      }
      "HOL" in {
       "1" in {
          val ls = List(s9,s10)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqualTo( 1 )
        }
        "2" in {
          val ls = List(seq1f,seq2f,seq3f,seq4f)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.toSet must beEqualTo( Set(seq1f,seq4f) )
        }
      }
    }
  }
}
