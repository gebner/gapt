package at.logic.gapt.examples.induction

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, Sequent }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.provers.OneShotProver
import at.logic.gapt.provers.viper._
import SimpleInductionProof._
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.{ Logger, Maybe }

object factorialmodth extends Script {

  Logger.makeVerbose( classOf[SipProver] )
  FindFormulaH.makeVerbose()

  val factorialES = ( ( ( "s(0) = f(0)" +: "s(x)*f(x) = f(s(x))" +: "g(x,0) = x" +: "g(x*s(y),y) = g(x,s(y))" +: "x*s(0) = x" +: "s(0)*x = x" +: "(x*y)*z = x*(y*z)" +: Sequent() ) map parseFormula ) map universalClosure.apply ) :+ FOLSubstitution( FOLVar( "x" ) -> alpha )( parseFormula( "g(s(0), x) = f(x)" ) )

  val theory = ( "x*s(0) = x" +: "s(0)*x = x" +: "(x*y)*z = x*(y*z)" +: Sequent() ) map parseFormula map universalClosure.apply

  val modThProver = new OneShotProver {
    override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
      Prover9.getLKProof( theory ++ seq )

    override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
      Prover9.isValid( theory ++ seq )
  }

  object patchingSolFinder extends SolutionFinder {
    val n = 0

    override def findSolution( sip: SimpleInductionProofU ): Option[FOLFormula] = {
      // We could pass the whole theory here, but ForgetfulParamodulate only does ground
      // paramodulation--so we give just the correct instance.
      val canSolModTh = canonicalSolution( sip, n )
      val canSol = And( canSolModTh, FOLSubstitution( FOLVar( "x" ) -> gamma )( parseFormula( "x*s(0)=x" ) ) )

      FindFormulaH( canSol, sip, n, forgetClauses = true, prover = modThProver )
    }
  }

  val sipProver = new SipProver(
    quasiTautProver = modThProver,
    solutionFinder = patchingSolFinder,
    instances = 0 to 4,
    instanceProver = Prover9,
    testInstances = 0 to 6,
    minimizeInstanceLanguages = true // <- removes instances that are subsumed by the theory :-)
  )

  val Some( sip ) = sipProver.getSimpleInductionProof( factorialES )
  println( sip.inductionFormula )
  println( sip.isSolved( modThProver ) )
  //prooftool(sip.toLKProof(modThProver))
}
