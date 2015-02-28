/*
* Tests for computing the decomposition of terms
*
*/

package at.logic.algorithms.cutIntroduction

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.collection.immutable.HashMap
import at.logic.language.fol._
import TermsExtraction._
import ComputeGrammars._
import Deltas._
import types._

@RunWith(classOf[JUnitRunner])
class GrammarTest extends SpecificationWithJUnit {

// On the comments of the examples below, consider A as α

  "The decomposition" should {

    "compute the bounded multi-variable delta-vector correctly" in {
      "trivial decomposition" in {

        val deltaG = new ManyVariableDelta(1)

        val f = "f"
        val g = "g"
        val a = FOLConst("a")
        val b = FOLConst("b")

        val f1 = FOLFunction(f, a::Nil)
        val g1 = FOLFunction(g, b::Nil)

        val dec = deltaG.computeDelta(f1::g1::Nil, "α")

        val alpha = FOLVar("α_0")

        val s = Set(((f1::g1::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((alpha, s)))
      }

        "example #1" in {
            val deltaG = new ManyVariableDelta(2)

            val f = "f"
            val a = FOLConst("a")
            val b = FOLConst("b")

            val f1 = FOLFunction(f, a::b::Nil)
            val f2 = FOLFunction(f, b::a::Nil)

            val dec = deltaG.computeDelta(f1::f2::Nil, "α")

            val alpha = FOLVar("α_0")
            val alpha_2 = FOLVar("α_1")
            val f_alpha = FOLFunction(f, alpha::alpha_2::Nil)

            val s1 = Set(((f1::f2::Nil)::Nil).transpose: _*)
            val s2 = Set(((a::b::Nil)::(b::a::Nil)::Nil).transpose: _*)

            (dec) must beEqualTo (Set[Decomposition]((alpha, s1), (f_alpha, s2.asInstanceOf[types.S])))
        }

        "example with a unary function symbol" in {
            val deltaG = new ManyVariableDelta(2)

            val f = "f"
            val a = FOLConst("a")
            val b = FOLConst("b")

            val f1 = FOLFunction(f, a::Nil)
            val f2 = FOLFunction(f, b::Nil)

            val dec = deltaG.computeDelta(f1::f2::Nil, "α")

            val alpha = FOLVar("α_0")
            val f_alpha = FOLFunction(f, alpha::Nil)

            val s = Set(((a::b::Nil)::Nil).transpose: _*)

            (dec) must beEqualTo (Set[Decomposition]((f_alpha, s.asInstanceOf[types.S])))
        }
    }

    "compute the multi-variable delta-vector DeltaG correctly" in {
      "trivial decomposition" in {

        val deltaG = new UnboundedVariableDelta()

        val f = "f"
        val g = "g"
        val a = FOLConst("a")
        val b = FOLConst("b")

        val f1 = FOLFunction(f, a::Nil)
        val g1 = FOLFunction(g, b::Nil)

        val dec = deltaG.computeDelta(f1::g1::Nil, "α")

        val alpha = FOLVar("α_0")

        val s = Set(((f1::g1::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((alpha, s)))
      }

      "example #1 without duplicates" in {

        val deltaG = new UnboundedVariableDelta()

        val f = "f"
        val g = "g"
        val a = FOLConst("a")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val d = FOLConst("d")
        val e = FOLConst("e")
        val fc = FOLConst("f")

        val f1 = FOLFunction(f, a::FOLFunction(g, c::d::Nil)::Nil)
        val f2 = FOLFunction(f, b::FOLFunction(g, e::fc::Nil)::Nil)

        val dec = deltaG.computeDelta(f1::f2::Nil, "α")

        val alpha0 = FOLVar("α_0")
        val alpha1 = FOLVar("α_1")
        val alpha2 = FOLVar("α_2")

        val uTarget = FOLFunction(f, alpha0::FOLFunction(g, alpha1::alpha2::Nil)::Nil)
        val s = Set(((a::b::Nil)::(c::e::Nil)::(d::fc::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((uTarget, s.asInstanceOf[types.S])))
      }

      "example #2 with duplicates" in {

        val deltaG = new UnboundedVariableDelta()

        val f = "f"
        val g = "g"
        val a = FOLConst("a")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val d = FOLConst("d")

        val f1 = FOLFunction(f, a::FOLFunction(g, c::c::Nil)::Nil)
        val f2 = FOLFunction(f, b::FOLFunction(g, d::d::Nil)::Nil)

        val dec = deltaG.computeDelta(f1::f2::Nil, "α")

        val alpha0 = FOLVar("α_0")
        val alpha1 = FOLVar("α_1")

        val uTarget = FOLFunction(f, alpha0::FOLFunction(g, alpha1::alpha1::Nil)::Nil)
        val s = Set(((a::b::Nil)::(c::d::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((uTarget, s.asInstanceOf[types.S])))
      }

      "example #3 with alpha-elimination" in {

        val deltaG = new UnboundedVariableDelta()

        val f = "f"
        val g = "g"
        val a = FOLConst("a")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val d = FOLConst("d")

        val f1 = FOLFunction(f, a::FOLFunction(g, c::d::Nil)::Nil)
        val f2 = FOLFunction(f, b::FOLFunction(g, c::d::Nil)::Nil)

        val dec = deltaG.computeDelta(f1::f2::Nil, "α")

        val alpha0 = FOLVar("α_0")

        val uTarget = FOLFunction(f, alpha0::FOLFunction(g, c::d::Nil)::Nil)
        val s = Set(((a::b::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((uTarget, s.asInstanceOf[types.S])))
      }

      "example #4 with duplicates and alpha-elimination" in {

        val deltaG = new UnboundedVariableDelta()

        val f = "f"
        val g = "g"
        val h = "h"
        val a = FOLConst("a")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val d = FOLConst("d")

        val f1 = FOLFunction(f, FOLFunction(h, a::Nil)::FOLFunction(g, c::a::Nil)::Nil)
        val f2 = FOLFunction(f, FOLFunction(h, b::Nil)::FOLFunction(g, c::b::Nil)::Nil)
        val f3 = FOLFunction(f, FOLFunction(h, b::Nil)::FOLFunction(g, c::b::Nil)::Nil)

        val dec = deltaG.computeDelta(f1::f2::f3::Nil, "α")

        val alpha0 = FOLVar("α_0")

        val uTarget = FOLFunction(f, FOLFunction(h, alpha0::Nil)::FOLFunction(g, c::alpha0::Nil)::Nil)
        val s = Set(((a::b::b::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((uTarget, s.asInstanceOf[types.S])))
      }
    }

    "compute the delta-vector correctly" in {
      "initial example" in {
        // f(hggc, ggc), f(hgc, gc) --> (f(hgA, gA), {gc, c})
        val delta = new OneVariableDelta()

        val f = "f"
        val h = "h"
        val g = "g"
        val c = FOLConst("c")

        val gc = FOLFunction(g, c::Nil)
        val ggc = FOLFunction( g, (FOLFunction(g, c::Nil))::Nil )
        val hgc = FOLFunction( h, (FOLFunction(g, c::Nil))::Nil )
        val hggc = FOLFunction(h, (FOLFunction(g, (FOLFunction(g, c::Nil))::Nil))::Nil)

        val f1 = FOLFunction(f, hggc::ggc::Nil)
        val f2 = FOLFunction(f, hgc::gc::Nil)

        val alpha = FOLVar("α_0")
        val galpha = FOLFunction(g, alpha::Nil)
        val hgalpha = FOLFunction(h, galpha::Nil)
        val common = FOLFunction(f, hgalpha::galpha::Nil)

        val dec = delta.computeDelta(f1::f2::Nil, "α")
        val s = Set(((gc::c::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((common, s)))
      }

      "trivial decomposition" in {
        // f(hggc, gga), f(hgc, gb) --> (A, {f(hggc, gga), f(hgc, gb)})
        val delta = new OneVariableDelta()

        val f = "f"
        val h = "h"
        val g = "g"
        val c = FOLConst("c")
        val b = FOLConst("b")
        val a = FOLConst("a")

        val gb = FOLFunction(g, b::Nil)
        val gga = FOLFunction( g, (FOLFunction(g, a::Nil))::Nil )
        val hgc = FOLFunction( h, (FOLFunction(g, c::Nil))::Nil )
        val hggc = FOLFunction(h, (FOLFunction(g, (FOLFunction(g, c::Nil))::Nil))::Nil)

        val f1 = FOLFunction(f, hggc::gga::Nil)
        val f2 = FOLFunction(f, hgc::gb::Nil)

        val alpha = FOLVar("α_0")

        val dec = delta.computeDelta(f1::f2::Nil, "α")
        val s = Set(((f1::f2::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((alpha, s)))

      }

      "decomposition with neutral element" in {
        // f(hggc, ga), f(hgc, ga) --> (f(hgA, ga), {gc, c})
        val delta = new OneVariableDelta()

        val f = "f"
        val h = "h"
        val g = "g"
        val c = FOLConst("c")
        val a = FOLConst("a")

        val ga = FOLFunction(g, a::Nil)
        val gc = FOLFunction(g, c::Nil)
        val hgc = FOLFunction( h, (FOLFunction(g, c::Nil))::Nil )
        val hggc = FOLFunction(h, (FOLFunction(g, (FOLFunction(g, c::Nil))::Nil))::Nil)

        val f1 = FOLFunction(f, hggc::ga::Nil)
        val f2 = FOLFunction(f, hgc::ga::Nil)

        val alpha = FOLVar("α_0")
        val galpha = FOLFunction(g, alpha::Nil)
        val hgalpha = FOLFunction(h, galpha::Nil)
        val common = FOLFunction(f, hgalpha::ga::Nil)

        val dec = delta.computeDelta(f1::f2::Nil, "α")
        val s = Set(((gc::c::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((common, s)))

      }

      "terms from the paper example (more than 2 terms)" in {
        // fa, f²a, f³a --> (fA, {a, fa, f²a})
        val delta = new OneVariableDelta()

        val f = "f"
        val a = FOLConst("a")

        val fa = FOLFunction(f, a::Nil)
        val f2a = FOLFunction(f, (FOLFunction(f, a::Nil))::Nil)
        val f3a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)

        val alpha = FOLVar("α_0")
        val falpha = FOLFunction(f, alpha::Nil)

        val dec = delta.computeDelta(fa::f2a::f3a::Nil, "α")
        val s = Set(((a::fa::f2a::Nil)::Nil).transpose: _*)

        (dec) must beEqualTo (Set[Decomposition]((falpha, s)))
      }
    }

    //Complex tests temporarily commented out.

    /*
    "compute the delta-table correctly" in {
      "for the f^i(a) set of terms (i = 1 to 4)" in {
        // fa, f²a, f³a, f⁴a
        val delta = new OneVariableDelta()

        val f = "f"
        val a = FOLConst("a")

        val fa = FOLFunction(f, a::Nil)
        val f2a = FOLFunction(f, (FOLFunction(f, a::Nil))::Nil)
        val f3a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)
        val f4a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil))::Nil)

        val alpha = "α"
        val falpha = FOLFunction(f, alpha::Nil)
        val f2alpha = FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil)
        val f3alpha = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil))::Nil)

        var expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (Nil) -> ((null, Nil)::Nil) )
        expected += ( (fa::Nil) -> ((alpha, fa::Nil)::Nil) )
        expected += ( (f2a::Nil) -> ((alpha, f2a::Nil)::Nil) )
        expected += ( (f3a::Nil) -> ((alpha, f3a::Nil)::Nil) )
        expected += ( (f4a::Nil) -> ((alpha, f4a::Nil)::Nil) )
        expected += ( (a::fa::Nil) -> ((f2alpha, f2a::f3a::Nil)::(f3alpha, f3a::f4a::Nil)::(falpha, fa::f2a::Nil)::Nil) )
        expected += ( (a::f2a::Nil) -> ((f2alpha, f2a::f4a::Nil)::(falpha, fa::f3a::Nil)::Nil) )
        expected += ( (a::f3a::Nil) -> ((falpha, fa::f4a::Nil)::Nil) )
        expected += ( (a::fa::f2a::Nil) -> ((f2alpha, f2a::f3a::f4a::Nil)::(falpha, fa::f2a::f3a::Nil)::Nil) )
        expected += ( (a::fa::f3a::Nil) -> ((falpha, fa::f2a::f4a::Nil)::Nil) )
        expected += ( (a::f2a::f3a::Nil) -> ((falpha, fa::f3a::f4a::Nil)::Nil) )
        expected += ( (a::fa::f2a::f3a::Nil) -> ((falpha, fa::f2a::f3a::f4a::Nil)::Nil) )

        val deltatable = new DeltaTable(fa::f2a::f3a::f4a::Nil, alpha)

        deltaTableEquals(deltatable.table, expected) must beTrue
      }


      "for Stefan's example" in {
        val delta = new OneVariableDelta()
        // t1 = f(c, gc)
        // t2 = f(c, g²c)
        // t3 = f(c, g³c)
        // t4 = f(gc, c)
        // t5 = f(g²c, gc)
        // t6 = f(g³c, g²c)

        val f = "f"
        val g = "g"
        val c = FOLConst("c")

        val gc = FOLFunction(g, c::Nil)
        val g2c = FOLFunction(g, (FOLFunction(g, c::Nil))::Nil)
        val g3c = FOLFunction(g, (FOLFunction(g, (FOLFunction(g, c::Nil))::Nil))::Nil)

        val t1 = FOLFunction(f, c::gc::Nil)
        val t2 = FOLFunction(f, c::g2c::Nil)
        val t3 = FOLFunction(f, c::g3c::Nil)
        val t4 = FOLFunction(f, gc::c::Nil)
        val t5 = FOLFunction(f, g2c::gc::Nil)
        val t6 = FOLFunction(f, g3c::g2c::Nil)

        val alpha = "α"
        val galpha = FOLFunction(g, alpha::Nil)
        val g2alpha = FOLFunction(g, (FOLFunction(g, alpha::Nil))::Nil)
        val f_c_galpha = FOLFunction(f, c::galpha::Nil)
        val f_c_g2alpha = FOLFunction(f, c::g2alpha::Nil)
        val f_galpha_alpha = FOLFunction(f, galpha::alpha::Nil)
        val f_g2alpha_galpha = FOLFunction(f, g2alpha::galpha::Nil)
        val f_alpha_gc = FOLFunction(f, alpha::gc::Nil)
        val f_alpha_g2c = FOLFunction(f, alpha::g2c::Nil)

        var expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (Nil) -> ((null, Nil)::Nil) )
        expected += ( (t1::Nil) -> ((alpha, t1::Nil)::Nil) )
        expected += ( (t2::Nil) -> ((alpha, t2::Nil)::Nil) )
        expected += ( (t3::Nil) -> ((alpha, t3::Nil)::Nil) )
        expected += ( (t4::Nil) -> ((alpha, t4::Nil)::Nil) )
        expected += ( (t5::Nil) -> ((alpha, t5::Nil)::Nil) )
        expected += ( (t6::Nil) -> ((alpha, t6::Nil)::Nil) )
        expected += ( (c::gc::Nil) -> ((f_c_g2alpha, t2::t3::Nil)::(f_galpha_alpha, t4::t5::Nil)::(f_g2alpha_galpha, t5::t6::Nil)::(f_c_galpha, t1::t2::Nil)::Nil) )
        expected += ( (c::g2c::Nil) -> ((f_galpha_alpha, t4::t6::Nil)::(f_c_galpha, t1::t3::Nil)::(f_alpha_gc, t1::t5::Nil)::Nil) )
        expected += ( (c::g3c::Nil) -> ((f_alpha_g2c, t2::t6::Nil)::Nil) )
        expected += ( (c::gc::g2c::Nil) -> ((f_galpha_alpha, t4::t5::t6::Nil)::(f_c_galpha, t1::t2::t3::Nil)::Nil) )

        val deltatable = new DeltaTable(t1::t2::t3::t4::t5::t6::Nil, alpha)

        deltaTableEquals(deltatable.table, expected) must beTrue
      }
    }*/

    /*
    "find the right decompositions for" in {
      "the paper's example" in {
        val delta = new OneVariableDelta()
        // fa, f²a, f³a, f⁴a

        val f = "f"
        val a = FOLConst("a")

        val fa = FOLFunction(f, a::Nil)
        val f2a = FOLFunction(f, (FOLFunction(f, a::Nil))::Nil)
        val f3a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)
        val f4a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil))::Nil)

        val alpha = "α"
        val falpha = FOLFunction(f, alpha::Nil)
        val f2alpha = FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil)
        val f3alpha = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil))::Nil)

        // NOTE: with the new implementation, once a grammar with size N is
        // found, no other grammar of size bigger than N is generated.
        var expected : List[Grammar] = Nil
        expected = expected :+ new Grammar(f3alpha::falpha::Nil, a::fa::Nil, alpha)
        expected = expected :+ new Grammar(f2alpha::f3alpha::falpha::Nil, a::fa::Nil, alpha)
        expected = expected :+ new Grammar(f2alpha::falpha::Nil, a::f2a::Nil, alpha)
        expected = expected :+ new Grammar(f2alpha::falpha::Nil, a::fa::f2a::Nil, alpha)
        expected = expected :+ new Grammar(falpha::Nil, a::fa::f2a::f3a::Nil, alpha)

        val d = ComputeGrammars(fa::f2a::f3a::f4a::Nil)

        containsEquivalentGrammars(d, expected) must beTrue

      }

      "Stefan's example" in {
        // t1 = f(c, gc)
        // t2 = f(c, g²c)
        // t3 = f(c, g³c)
        // t4 = f(gc, c)
        // t5 = f(g²c, gc)
        // t6 = f(g³c, g²c)
        val delta = new OneVariableDelta()

        val f = "f"
        val g = "g"
        val c = FOLConst("c")

        val gc = FOLFunction(g, c::Nil)
        val g2c = FOLFunction(g, (FOLFunction(g, c::Nil))::Nil)
        val g3c = FOLFunction(g, (FOLFunction(g, (FOLFunction(g, c::Nil))::Nil))::Nil)

        val t1 = FOLFunction(f, c::gc::Nil)
        val t2 = FOLFunction(f, c::g2c::Nil)
        val t3 = FOLFunction(f, c::g3c::Nil)
        val t4 = FOLFunction(f, gc::c::Nil)
        val t5 = FOLFunction(f, g2c::gc::Nil)
        val t6 = FOLFunction(f, g3c::g2c::Nil)


        val alpha = "α"
        val galpha = FOLFunction(g, alpha::Nil)
        val g2alpha = FOLFunction(g, (FOLFunction(g, alpha::Nil))::Nil)
        val f_c_galpha = FOLFunction(f, c::galpha::Nil)
        val f_c_g2alpha = FOLFunction(f, c::g2alpha::Nil)
        val f_galpha_alpha = FOLFunction(f, galpha::alpha::Nil)
        val f_g2alpha_galpha = FOLFunction(f, g2alpha::galpha::Nil)
        val f_alpha_gc = FOLFunction(f, alpha::gc::Nil)
        val f_alpha_g2c = FOLFunction(f, alpha::g2c::Nil)

        var expected : List[Grammar] = Nil
        expected = expected :+ new Grammar(f_c_g2alpha::f_galpha_alpha::f_g2alpha_galpha::f_c_galpha::Nil, c::gc::Nil, alpha)
        expected = expected :+ new Grammar(f_galpha_alpha::f_c_galpha::Nil, c::gc::g2c::Nil, alpha)

        //val minGrammar = new Grammar(f_galpha_alpha::f_c_galpha::Nil, c::gc::g2c::Nil, alpha)

        val d = ComputeGrammars(t1::t2::t3::t4::t5::t6::Nil)

        /*val contains = d.exists(g =>
          g.u.diff(minGrammar.u) == Nil && minGrammar.u.diff(g.u) == Nil &&
          g.s.diff(minGrammar.s) == Nil && minGrammar.s.diff(g.s) == Nil
        )

        contains must beTrue*/
        containsEquivalentGrammars(d, expected) must beTrue

      }

      "an example that needs the trivial decomposition added at the end" in {
        // a, fa, f²a, f³a
        val delta = new OneVariableDelta()

        val f = "f"
        val a = FOLConst("a")

        val fa = FOLFunction(f, a::Nil)
        val f2a = FOLFunction(f, (FOLFunction(f, a::Nil))::Nil)
        val f3a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)

        val alpha = "α"
        val falpha = FOLFunction(f, alpha::Nil)
        val f2alpha = FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil)
        val f3alpha = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, alpha::Nil))::Nil))::Nil)

        var expected : List[Grammar] = Nil
        expected = expected :+ new Grammar(alpha::f2alpha::Nil, a::fa::Nil, alpha)
        expected = expected :+ new Grammar(alpha::f2alpha::falpha::Nil, a::fa::Nil, alpha)
        expected = expected :+ new Grammar(alpha::falpha::Nil, a::f2a::Nil, alpha)
        expected = expected :+ new Grammar(alpha::falpha::Nil, a::fa::f2a::Nil, alpha)

        val d = ComputeGrammars(a::fa::f2a::f3a::Nil)

        containsEquivalentGrammars(d, expected) must beTrue
      }

      "issue 206!!" in {
        // LinearEqExampleProof(4)
        // Term set for three formulas:
        // F1 (1 quant.) -> (a)
        // F2 (1 quant.) -> (a, fa, f²a, f³a)
        // F3 (3 quant.) -> ([fa, a, a], [f²a, fa, a], [f³a, f²a, a], [f⁴a, f³a, a])
        val delta = new OneVariableDelta()

        val f = "f"
        val a = FOLConst("a")
        val alpha = FOLVar("α")

        val fa = FOLFunction(f, a::Nil)
        val f2a = FOLFunction(f, (FOLFunction(f, a::Nil))::Nil)
        val f3a = FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)
        val f4a = FOLFunction(f, FOLFunction(f, (FOLFunction(f, (FOLFunction(f, a::Nil))::Nil))::Nil)::Nil)

        // Tuple function symbols:
        val tuple1 = "tuple1"
        val tuple2 = "tuple2"
        val tuple3 = "tuple3"

        // Termset for F1
        val t11 = FOLFunction(tuple1, a::Nil)
        val ts1 = t11::Nil

        // Termset for F2
        val t21 = FOLFunction(tuple2, a::Nil)
        val t22 = FOLFunction(tuple2, fa::Nil)
        val t23 = FOLFunction(tuple2, f2a::Nil)
        val t24 = FOLFunction(tuple2, f3a::Nil)
        val ts2 = t21::t22::t23::t24::Nil

        // Termset for F3
        val t31 = FOLFunction(tuple3, fa::a::a::Nil)
        val t32 = FOLFunction(tuple3, f2a::fa::a::Nil)
        val t33 = FOLFunction(tuple3, f3a::f2a::a::Nil)
        val t34 = FOLFunction(tuple3, f4a::f3a::a::Nil)
        val ts3 = t31::t32::t33::t34::Nil

        val termset = ts1 ++ ts2 ++ ts3

        val d = ComputeGrammars(termset)

        val t2alpha = FOLFunction(tuple2, alpha::Nil)
        val t3alpha = FOLFunction(tuple3, FOLFunction(f, alpha::Nil)::alpha::a::Nil)
        val criticalGrammar = new Grammar(t2alpha::t3alpha::t11::Nil, a::fa::f2a::f3a::Nil, alpha)

        val contains = d.exists(g =>
          g.u.diff(criticalGrammar.u) == Nil && criticalGrammar.u.diff(g.u) == Nil &&
          g.s.diff(criticalGrammar.s) == Nil && criticalGrammar.s.diff(g.s) == Nil
        )

        contains must beTrue
      }
    }*/
  }

  /*
  def containsEquivalentGrammars(g1: List[Grammar], g2: List[Grammar]) =
    g1.forall(g =>
      g2.exists(e =>
       g.u.diff(e.u) == Nil && e.u.diff(g.u) == Nil &&
       g.s.diff(e.s) == Nil && e.s.diff(g.s) == Nil
      )
    )
      
  def deltaTableEquals(d1: HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]], d2: HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]) = (
    d1.forall(v1 =>
      d2.exists(v2 => 
        v1._1 == v2._1 && v1._2.toSet.equals(v2._2.toSet)
      )
    )
    &&
    d2.forall(v1 =>
      d1.exists(v2 => 
        v1._1 == v2._1 && v1._2.toSet.equals(v2._2.toSet)
      )
    )
  )*/

}
