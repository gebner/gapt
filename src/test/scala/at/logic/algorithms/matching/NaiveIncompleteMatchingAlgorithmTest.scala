/*
 * NaiveIncompleteMatchingAlgorithmTest.scala
 *
 */

package at.logic.algorithms.matching

import at.logic.language.lambda.{Substitution, App, Var, Const}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.types._

import scala.App

@RunWith(classOf[JUnitRunner])
class NaiveIncompleteMatchingAlgorithmTest extends SpecificationWithJUnit {
  "NaiveIncompleteMatchingAlgorithm " should {
    "match correctly the HOL expressions P(a,x) and P(a,f(b))" in {
      val P = Const("P", Ti->(Ti->To))
      val a = Const("a", Ti)
      val b = Const("b", Ti)
      val Pa = App(P,a);
      val x = Var("x", Ti)
      val Pax = App(Pa,x)
      val f = Const("f", Ti->Ti)
      val fb= App(f,b)
      val Pafb = App(Pa,fb)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pax,Pafb)
      val subst1 = Substitution(x,fb)
      subst must beEqualTo (Some(subst1))
    }

    "match correctly the HOL expressions P(z,x) and P(f(b),f(b))" in {
      val P = Const("P", Ti->(Ti->To))
      val b = Const("b", Ti)
      val x = Var("x", Ti)
      val z = Var("z", Ti)
      val Pz = App(P,z)
     
      val Pzx = App(Pz,x)
      val f = Const("f", Ti->Ti)
      val fb= App(f,b)
      val Pfb = App(P,fb)
      val Pfbfb = App(Pfb,fb)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbfb)
      val subst1 = Substitution(Map((x, fb), (z, fb)))
      subst must beEqualTo (Some(subst1))
    }

    "NOT match correctly the HOL expressions P(z,x) and P(f(b),z)" in {
      val P = Const("P", Ti->(Ti->To))
      val b = Const("b", Ti)
      val x = Var("x", Ti)
      val z = Var("z", Ti)
      val Pz = App(P,z)
      val Pzx = App(Pz,x)
      val f = Const("f", Ti->Ti)
      val fb= App(f,b)
      val Pfb = App(P,fb)
      val Pfbz = App(Pfb,z)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbz)
      val subst1 = Substitution( Map((z,fb), (x,z)) )
      subst must beEqualTo (None)         // correct !!!
    }

    "match correctly the HOL expression a < p(x) with itself" in {
      val lt = Const("<", Ti->(Ti->To))
      val a = Const("a", Ti)
      val p = Const("p", Ti->Ti)
      val x = Var("x", Ti)
      val px = Function(p, x::Nil)
      val at = Function(lt, a::px::Nil)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(at, at)
      subst must beEqualTo (Some(Substitution()))
    }

    "match correctly the HOL expression a < p(x) with another copy of itself" in {
      val lt = Const("<", Ti->(Ti->To))
      val a = Const("a", Ti)
      val p = Const("p", Ti->Ti)
      val x = Var("x", Ti)
      val px = Function(p, x::Nil)
      val at = Function(lt, a::px::Nil)
      val at2 = Function(lt, a::px::Nil) // Is this a copy?
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(at, at2)
      subst must beEqualTo (Some(Substitution()))
    }
  }
}


