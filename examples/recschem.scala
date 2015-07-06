import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.{parse, time}

import at.logic.gapt.examples.{UniformAssociativity3ExampleProof, SumExampleProof, LinearEqExampleProof}
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{FOLSubTerms, Numeral, FOLSubstitution, Utils}
import at.logic.gapt.expr.hol.{univclosure, toNNF, simplify, lcomp}
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansionTrees.{removeFromExpansionSequent, ExpansionSequent, InstanceTermEncoding}
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.lk.cutIntroduction.TermsExtraction
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.provers.inductionProver.{SipProver, SimpleInductionProof}
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import org.apache.log4j.{Logger, Level}

import scala.util.Random

for (c <- Seq(minimizeSipGrammar.getClass, minimizeRecursionScheme.getClass))
  Logger.getLogger(c.getName).setLevel(Level.DEBUG)

if (false) {

  //val terms = TermsExtraction(SumExampleProof(7)).set
  val N = 8
  val terms = (0 until N) map { i =>
    FOLFunction("r", Utils.numeral(i), Utils.numeral(N - i))
  }

  val nfs = normalForms(FOLSubTerms(terms), Seq(FOLVar("x"), FOLVar("y")))

  val nfRecSchem = RecursionScheme(
    (for (arg1 <- nfs; arg2 <- nfs; if freeVariables(Seq(arg1, arg2)).isEmpty)
      yield Rule(FOLFunction("A"), FOLFunction("B", arg1, arg2))).toSet ++
      (for (nf <- nfs; if !nf.isInstanceOf[FOLVar]) yield Rule(FOLFunction("B", FOLVar("x"), FOLVar("y")), nf))
  )

  val targets = terms.map(FOLFunction("A") -> _)
  println(lcomp(simplify(toNNF((new RecSchemGenLangFormula(nfRecSchem))(targets)))))

  val nfG = normalFormsProofVectGrammar(terms, Seq(2))
  println(lcomp(simplify(toNNF(new VectGrammarMinimizationFormula(nfG).coversLanguage(terms)))))

  val minimized = time {
    minimizeRecursionScheme(nfRecSchem, targets)
  }
  println(minimized)

  val minG = time {
    minimizeVectGrammar(nfG, terms)
  }
  println(minG)

}

if (true) {
//  val endSequent = FSequent(
//    Seq("s(x+y) = s(x)+y", "0+x = x")
//      map (s => univclosure(parseFormula(s))),
//    Seq(parseFormula("x+y = y+x")))
//  val endSequent = FSequent(
//    Seq("min(s(x), s(y)) = s(min(x,y))", "min(0,x) = 0", "min(x,0) = 0")
//      map (s => univclosure(parseFormula(s))),
//    Seq(parseFormula("min(x,y) = min(y,x)")))
  val endSequent = FSequent(
    Seq("0 <= x", "x <= y -> x <= s(y)", "x <= x", "x+y = y+x", "x + 0 = x", "x + s(y) = s(x+y)")
      map (s => univclosure(parseFormula(s))),
    Seq(parseFormula("x <= y + x")))
  val instances = Set((0,0), (1,0), (0,1)) ++ (0 until 6).map{_ => (Random.nextInt(3), Random.nextInt(3))}
  val instanceProofs = instances.par.map { case (x,y) =>
    val instanceSequent = FOLSubstitution( FOLVar("x") -> Numeral(x), FOLVar("y") -> Numeral(y) )( endSequent )
    println( s"[$x,$y] Proving $instanceSequent" )
    (x,y) -> new Prover9Prover().getExpansionSequent( instanceSequent ).get
  }.seq.toSeq

  val termEncoding = InstanceTermEncoding( endSequent )
  var instanceLanguages = instanceProofs map {
    case ( n, expSeq ) =>
      n -> termEncoding.encode( expSeq )
  }

  // Ground the instance languages.
  instanceLanguages = instanceLanguages map {
    case ( n, lang ) =>
      val groundingSubst = FOLSubstitution( freeVariables( lang ).
        map { c => FOLVar( c.name ) -> FOLConst( c.name ) }.toSeq )
      n -> lang.map( groundingSubst.apply )
  }

  val nfRecSchem = SipRecSchem.normalForms(instanceLanguages)
  println(nfRecSchem.rules.size)
  val minimized = time{minimizeRecursionScheme(nfRecSchem, SipRecSchem.toTargets(instanceLanguages), SipRecSchem.targetFilter)}
  println(minimized);println

  (0 until 50) foreach { _ =>
    val x = Random.nextInt(15)
    val y = Random.nextInt(15)
    val instanceLang = minimized.language(FOLFunction(SipRecSchem.A, Numeral(x), Numeral(y)))
    val instanceSeq = FOLSubstitution(FOLVar("x") -> Numeral(x), FOLVar("y") -> Numeral(y))(termEncoding.decodeToFSequent(instanceLang))
    val isCovered = instanceLanguages.find(_._1 == (x,y)).map(_._2.toSet subsetOf instanceLang)
    val isTaut = new VeriTProver().isValid(instanceSeq)
    println(s"[$x,$y]: tautology=$isTaut covers=$isCovered")
  }

//  val sipG = SipRecSchem.toSipGrammar(minimized)
//  println(sipG)

//  val nfSipG = normalFormsSipGrammar(instanceLanguages)
//  println(nfSipG.productions.size)
//  println(time{minimizeSipGrammar(nfSipG, instanceLanguages)})
}