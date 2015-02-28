/*
* Tests for forgetful resolution.
*
*/

package at.logic.algorithms.cutIntroduction

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.language.hol._
import MinimizeSolution._

@RunWith(classOf[JUnitRunner])
class ForgetfulResolutionTest extends SpecificationWithJUnit {

  "Forgetful Paramodulation Should" should {

    "successfully paramodulate a=b into f(a,a)" in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val fs = "f"
      val faa = FOLFunction(fs, a::a::Nil)

      val realab = Set( FOLFunction( fs, a::a::Nil ), FOLFunction( fs, a::b::Nil ), FOLFunction( fs, b::a::Nil ), FOLFunction( fs, b::b::Nil ) )
      val realba = Set( FOLFunction( fs, a::a::Nil ) )
     
      val parasab = Paramodulants1(a, b, faa)
      val parasba = Paramodulants1(b, a, faa)

      parasab must beEqualTo(realab)
      parasba must beEqualTo(realba)
    }

    "successfully apply forgetful paramodulation to { :- a = b; :- P(a, a); :- Q } " in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val ps = "P"
      val paa = FOLAtom(ps, a::a::Nil)
      val pab = FOLAtom(ps, a::b::Nil)
      val pba = FOLAtom(ps, b::a::Nil)
      val pbb = FOLAtom(ps, b::b::Nil)
      val q = FOLAtom("Q", Nil )
      val cq = new MyFClause( Nil, q::Nil )
      val cpaa = new MyFClause( Nil, paa::Nil )
      val cpab = new MyFClause( Nil, pab::Nil )
      val cpba = new MyFClause( Nil, pba::Nil )
      val cpbb = new MyFClause( Nil, pbb::Nil )

      val r1 = Set(cpab, cq)
      val r2 = Set(cpba, cq)
      val r3 = Set(cpbb, cq)
      val real = Set(r1, r2, r3)

      val res = ForgetfulParamodulateCNF( And( Equation( a, b)::paa::q::Nil ) )

      val setres = res.map( cnf => cnf.toSet ).toSet

      setres must beEqualTo(real)
    }
/*
    "improve the solution correctly" in {
      val p = at.logic.testing.LinearExampleProof(8)
      val ts = new FlatTermSet(TermsExtraction(p))
      val g = ComputeGrammars(ts)
      val grm = g(2)
      val ehs = new ExtendedHerbrandSequent(p.root, grm, ts)
      val improv = improveSolution(ehs.canonicalSol, ehs)

      // TODO: type the expected value correctly
      //val expected =
      //improv must
      success
    }
*/
  }

  "Forgetful Resolution Should" should {

    "compute a single resolvent successfully" in {
      val a = FOLAtom("A")
      val b = FOLAtom("B")
      val c = FOLAtom("C")
      val d = FOLAtom("D")
      val e = FOLAtom("E")

      val f = And(And(Or(a,Or(b,c)), Or(Neg(b), d)), e)

      val res = ForgetfulResolve(f)

      //println("Formula (in CNF): " + f)
      //println("Resolvent: " + res)

      res.size must beEqualTo(1)
    }

/*
    "improve the solution correctly" in {
      val p = at.logic.testing.LinearExampleProof(8)
      val ts = new FlatTermSet(TermsExtraction(p))
      val g = ComputeGrammars(ts)
      val grm = g(2)
      val ehs = new ExtendedHerbrandSequent(p.root, grm, ts)
      val improv = improveSolution(ehs.canonicalSol, ehs)

      // TODO: type the expected value correctly
      //val expected =
      //improv must
      success
    }
*/
  }
}

