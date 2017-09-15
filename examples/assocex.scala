
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.expansion.{ ExpansionProof, extractInstances, minimalExpansionSequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof, ReductiveCutElimination, extractRecSchem, instanceProof, makeInductionExplicit }
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, Suc }
import at.logic.gapt.provers.OneShotProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire
import at.logic.gapt.provers.viper.ViperOptions
import at.logic.gapt.provers.viper.grammars.TreeGrammarProver
import at.logic.gapt.utils.{ Logger, Maybe }

object assocex extends TacticsProof {
  ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"

  val bgTh = Normalizer(
    hoa"0 + x = x", hoa"x + 0 = x"
  //    hoa"s x + y = s (x + y)", hoa"x + s y = s (x + y)"
  )
  val bgThF = bgTh.toFormula

  def normSeq( seq: HOLSequent ): HOLSequent =
    seq.map( bgTh.normalize ).map( _.asInstanceOf[Formula] )

  val bgThProver = new OneShotProver {
    override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = ???

    override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      import at.logic.gapt.provers.viper.aip.provers._
      spass.getExpansionProof( bgThF +: seq ).map { foProof =>
        minimalExpansionSequent( foProof, this ).get
      }
    }

    override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
      Z3.isValid( seq.map( bgTh.normalize( _ ).asInstanceOf[Formula] ) )
  }

  val sequent =
    hols"""
          zp: !x 0+x=x, pz: !x x+0=x,
          sp: !x!y s(x)+y=s(x+y),
          ps: !x!y x+s(y)=s(x+y)
          :- !x (x+x)+x=x+(x+x)
        """

  val p = Lemma( sequent ) {
    decompose
    cut( "c", hof"!y (y+x)+x=y+(x+x)" ).right( chain( "c" ) )
    forget( "g" ); decompose; induction( hov"y:nat" )
    rewrite.many ltr "zp"; refl
    rewrite.many ltr ( "sp", "IHy_0" ); refl
  }
  if ( false )
    println( extractInstances( LKToExpansionProof( makeInductionExplicit( p ) ) ) )

  // This is the proof that we would find using SPASS's instance proofs,
  // if we would rewrite with 0+x=x=x+0 during solution search.
  val p_spass = Lemma( sequent ) {
    decompose
    cut( "c", hof"!y (x+x)+y=y+(x+x)" ).right( chain( "c" ) )
    forget( "g" ); decompose; induction( hov"y:nat" )
    rewrite.many ltr ( "zp", "pz" ); refl
    rewrite.many ltr ( "sp", "ps", "IHy_0" ); refl
  }
  //  println( p_spass )
  println( extractInstances( LKToExpansionProof( makeInductionExplicit( p_spass ) ) ) )

  Logger.makeVerbose( classOf[TreeGrammarProver] )
  Lemma( sequent ) {
    treeGrammarInduction.instanceProver( bgThProver )
      .smtSolver( bgThProver )
      .quantTys()
      .canSolSize( 2, 2 )
      .doForgetOne( true )
  }
}
