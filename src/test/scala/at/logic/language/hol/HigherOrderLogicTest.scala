/*
 * HigherOrderLogicTest.scala
 */

package at.logic.language.hol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.symbols._
import logicSymbols._
import skolemSymbols._
import BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

@RunWith(classOf[JUnitRunner])
class HigherOrderLogicTest extends SpecificationWithJUnit {
  
  "FunctionLike" should {
    "pick apart one app" in {
      App(Const("f", Ti->Ti), Const("x",Ti)) must beLike {
        case FunctionLike(f, List(x)) => ok
        case _ => ko
      }
    }
    
    "pick apart two apps" in {
      App(App(Const("f", Ti->(To->Ti)), Const("x", Ti)), Const("y", To)) must beLike {
        case FunctionLike(f, List(x, y)) => ok
        case _ => ko
      }
    }
    
  }

  "HigherOrderLogic" should {
    val c1 = Const("a", Ti->To)
    val v1 = Var("x", Ti)
    val a1 = App(c1, v1)
    val c2 = Var("a", Ti->(Ti->To))
    val v21 = Var("x", Ti)
    val v22 = Var("y", Ti)
    val a21 = App(c2, v21)
    val a22 = App(a21, v22)

    "And connective should return the right And formula" in {
      val c1 = Atom(Const("a", To))
      val c2 = Atom(Const("b", To))
      val result = And(c1, c2) match {
        case App(App(andC, c1), c2) => true
        case _ => false
      }
      result must beTrue
      }
    "Or connective should return the right formula" in {
      val c1 = Atom(Const("a", To))
      val c2 = Atom(Const("b", To))
      val result = Or(c1, c2) match {
        case App(App(orC, c1), c2) => true
        case _ => false
      }
      result must beTrue
    }
    "Imp connective should return the right formula" in {
      val c1 = Atom(Var("a", To))
      val c2 = Atom(Var("b", To))
      val result = Imp(c1, c2) match {
        case App(App(impC, c1), c2) => true
        case _ => false
      }
      result must beTrue
    }
    "Neg connective should " in {
      "return the right formula" in {
        val c1 = Atom(Var("a", To))
        val result = Neg(c1) match {
          case App(negC, c1) => true
          case _ => false
        }
        result must beTrue
      }
      "be extracted correctly" in {
        val e = App(Const("g","(i -> i)"), Const("c", "i")::Nil)
        val result = e match {
          case Neg(_) => false
          case _ => true
        }
        result must beTrue
      }
    }

    "substitute and normalize correctly when Substitution is applied" in {
      val x = Var("X", Ti -> To )
      val f = Var("f", (Ti -> To) -> Ti )
      val xfx = App(x, App( f, x ) )

      val z = Var("z", Ti)
      val p = Var("P", Ti -> To)
      val Pz = App( p, z )
      val t = Abs( z, Pz )
      val pft = App( p, App( f, t ))

      val sigma = Substitution( x, t )

      betaNormalize( sigma( xfx ) ) must beEqualTo( pft )
    }

    "substitute and normalize correctly when Substitution is applied on the formula level" in {
      val x = Var("X", Ti -> To )
      val f = Var("f", (Ti -> To) -> Ti )
      val xfx = Atom(x, Function( f, x::Nil )::Nil )

      val z = Var("z", Ti)
      val p = Var("P", Ti -> To)
      val Pz = App( p, z )
      val t = Abs( z, Pz )
      val pft = Atom( p, Function( f, t::Nil )::Nil )

      val sigma = Substitution( x, t )
      val xfx_sigma = betaNormalize( sigma( xfx ) )

      xfx_sigma must beEqualTo( pft )
    }
  }

  "Exists quantifier" should {
    val c1 = Const("a", Ti->To)
    val v1 = Var("x", Ti)
    val f1 = Atom(c1,v1::Nil)
    "create a term of the right type" in {
      (ExVar(v1, f1).exptype) must beEqualTo (To)
    }
  }

  "Forall quantifier" should {
    val c1 = Const("a", Ti->To)
    val v1 = Var("x", Ti)
    val f1 = Atom(c1,v1::Nil)
    "create a term of the right type" in {
      (AllVar(v1, f1).exptype) must beEqualTo (To)
    }
  }

  "Atoms" should {
    "be extracted correctly" in {
      val p = Const("P", To)
      val result = p match {
        case Atom(Const("P", To), Nil) => true
        case _ => false
      }
      result must beTrue
    }
  }
  
  "Equation" should {
    "be of the right type" in {
      val c1 = Const("f1", Ti -> Ti)
      val c2 = Const("f2", Ti -> Ti)
      val eq = Equation(c1,c2)
      val App(App(t,_), _) = eq
      t.exptype must beEqualTo ((Ti -> Ti) -> ((Ti -> Ti) -> To))
    }
  }

  "Substitution" should {
    "work correctly on some testcase involving free/bound vars" in {
      val s0 = Const("s_{0}", Ti -> Ti)
      val C = Const("C", Ti -> Ti)
      val T = Const("T", Ti -> Ti)
      val sCTn = Function(s0, Function( C, Function( T, Const("n", Ti)::Nil)::Nil)::Nil )
      val u = Var("u", Ti)
      val v = Var("v", Ti)
      val P1 = Atom( Var("P", ->(sCTn.exptype, ->(Ti, To))), sCTn::u::Nil)
      val P2 = Atom( Var("P", ->(sCTn.exptype, ->(Ti, To))), sCTn::v::Nil)
      val q_form = AllVar(u, ExVar(v, Imp(P1, P2)))
      
      q_form match {
        case AllVar(x, f) => {
          val a = Const("a", x.exptype)
          val sub = Substitution( x, a )
          val P3 = Atom(Var("P", ->(sCTn.exptype, ->(a.exptype, To))), sCTn::a::Nil)
          val s = sub( f )
          val result = s match {
            case ExVar(v, Imp(P3, P2)) => true
            case _ => false
          }
          result must beTrue
        }
      }
    }
  }

  "SkolemSymbolFactory" should {
      val x = Var("x", Ti)
      val y = Var("y", Ti)
      val f = AllVar( x, Atom(Var("P", ->(Ti, To)), x::Nil ) )
      val s0 = new StringSymbol( "s_{0}" )
      val s1 = new StringSymbol( "s_{2}" )
      val s2 = new StringSymbol( "s_{4}" )
      val s3 = new StringSymbol( "s_{6}" )

      SkolemSymbolFactory.reset
      val stream = SkolemSymbolFactory.getSkolemSymbols

    "return a correct stream of Skolem symbols" in {
      stream.head must beEqualTo( s0 )
      stream.tail.head must beEqualTo( s1 )
      stream.tail.tail.head must beEqualTo( s2 )
    }
  }

  "Higher Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val f = And(Atom(Var("P", To),Nil), Atom(Var("P", To),Nil))

      f must beLike {
        case Atom(_,_) => println("Is an atom"); ko
        case Function(_,_,_) => ko
        case AllVar(_,_) => ko
        case ExVar(_,_) => ko
        case Or(_,_) => ko
        case Imp(_,_) => ko
        case And(_,_) => ok
        case _ => ko
      }
    }
  }

  "Quantifier blocks" should {
    val x = Var("x", Ti)
    val y = Var("y", Ti)
    val z = Var("z", Ti)

    val Pxyz = Atom(Const("P", ->(Ti,->(Ti,(->(Ti,To))))), List(x,y,z))
    val allP = AllVar(x, AllVar(y, AllVar(z, Pxyz)))
    val exP = ExVar(x, ExVar(y, ExVar(z, Pxyz)))

    "Correctly introduce one quantifier" in {
      AllVarBlock(List(x), Pxyz) must beEqualTo(AllVar(x, Pxyz))
      ExVarBlock(List(x), Pxyz) must beEqualTo(ExVar(x, Pxyz))
    }

    "Correctly introduce multiple quantifiers" in {
      AllVarBlock(List(x,y,z), Pxyz) must beEqualTo(allP)
      ExVarBlock(List(x,y,z), Pxyz) must beEqualTo(exP)
    }

    "Correctly match quantified formulas" in {

      val match1 = allP match {
        case AllVarBlock(vars, f) =>
          vars == List(x,y,z)
          f == Pxyz
        case _ => false
      }

      val match2 = exP match {
        case ExVarBlock(vars, f) =>
          vars == List(x,y,z)
          f == Pxyz
        case _ => false
      }

      match1 must beTrue
      match2 must beTrue
    }

    "Fail to match other formulas" in {
      exP match {
        case AllVarBlock(_,_) => failure
        case _ =>
      }

      allP match {
        case ExVarBlock(_,_) => failure
        case _ =>
      }

      Pxyz match {
        case AllVarBlock(_,_) | ExVarBlock(_,_) => failure
        case _ =>
      }

      success
    }
  }
}
