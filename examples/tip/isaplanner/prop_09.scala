package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.axioms.SequentialInductionAxioms
import at.logic.gapt.provers.viper.aip.provers.escargot
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_09 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_09.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof1 = Lemma( sequent ) {
    allR
    induction( hov"i:Nat" )
    allR
    allR
    allL( "h3", le"j:Nat" )
    allL( "h3", le"plus(j:Nat, k:Nat)" )
    allL( "h3", le"k:Nat" )
    eql( "h3_0", "goal" ).fromLeftToRight
    eql( "h3_1", "goal" ).fromLeftToRight
    eql( "h3_2", "goal" ).fromLeftToRight
    refl

    allR
    induction( hov"j:Nat" )
    allR
    allL( "h1", le"k:Nat" )
    allL( "h4", le"i_0:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    eql( "h4_0", "goal" ).fromLeftToRight
    refl

    allR
    allL( "h5", le"i_0:Nat", le"j_0:Nat" )
    allL( "h2", le"j_0:Nat", le"k:Nat" )
    allL( "h5", le"i_0:Nat", le"plus(j_0:Nat, k:Nat)" )
    allL( "IHi_0", le"j_0:Nat", le"k:Nat" )
    eql( "h5_0", "goal" )
    eql( "h2_0", "goal" )
    eql( "h5_1", "goal" )
    axiomLog
  }

  val aipOptions1 = new ProverOptions( escargot, SequentialInductionAxioms().forVariables( List( hov"i:Nat", hov"j:Nat" ) ).forLabel( "goal" ) )
  val proof2 = new AnalyticInductionProver( aipOptions1 ) lkProof ( sequent ) get

  val aipOptions2 = new ProverOptions( escargot, SequentialInductionAxioms().forAllVariables.forLabel( "goal" ) )
  val proof3 = new AnalyticInductionProver( aipOptions2 ) lkProof ( sequent ) get

  import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic.{ independentAxioms, sequentialAxioms }

  val proof4 = Lemma( sequent ) {
    analyticInduction withAxioms
      sequentialAxioms.forAllVariables.forLabel( "goal" )
  }

  val proof5 = Lemma( sequent ) {
    analyticInduction withAxioms
      sequentialAxioms.forAllVariables.forLabel( "goal" ) :/\: independentAxioms.forVariables( hov"i:Nat" )
  }
}
