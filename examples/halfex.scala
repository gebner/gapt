import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.expansion.{ ExpansionProof, InstanceTermEncoding, minimalExpansionSequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, ReductiveCutElimination, extractRecSchem, instanceProof }
import at.logic.gapt.proofs.{ Context, HOLSequent, Suc }
import at.logic.gapt.provers.OneShotProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.viper.grammars.TreeGrammarProver
import at.logic.gapt.utils.Logger

object halfex extends TacticsProof {
  ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"h: nat>nat"

  val bgTh = Normalizer(
    hoa"0 + x = x", hoa"x + 0 = x",
    hoa"s x + y = s (x + y)", hoa"x + s y = s (x + y)"
  )
  val bgThF = bgTh.toFormula

  def normSeq( seq: HOLSequent ): HOLSequent =
    seq.map( bgTh.normalize ).map( _.asInstanceOf[Formula] )

  val bgThProver = new OneShotProver {
    override def getLKProof( seq: HOLSequent ): Option[LKProof] = ???

    override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] = {
      Escargot.getExpansionProof( bgThF +: seq ).map { foProof0 =>
        val foProof1 = ExpansionProof( foProof0.expansionSequent.filter( _.shallow != bgThF ) )
        val ( lang, enc ) = InstanceTermEncoding( foProof1 )
        val foProof2 = enc.decodeToExpansionProof( lang.map( bgTh.normalize ) )
        minimalExpansionSequent( foProof2, this ).get
      }
    }

    override def isValid( seq: HOLSequent ): Boolean =
      Z3.isValid( seq.map( bgTh.normalize( _ ).asInstanceOf[Formula] ) )
  }

  val sequent =
    hols"""
          pz: !x 0+x=x, zp: !x x+0=x,
          ps: !x!y x+s(y)=s(x+y),
          sp: !x!y s(x)+y=s(x+y),
          h0: h(0)=0, h1: h(s(0))=0,
          hss: !x h(s(s(x))) = s(h(x))
          :- !x h(x+x)=x
        """

  Lemma( sequent ) {
    decompose; induction( hov"x:nat" )
    rewrite.many ltr ( "pz", "h0" ); refl
    rewrite.many ltr ( "ps", "sp", "hss", "IHx_0" ); refl
  }

  Logger.makeVerbose( classOf[TreeGrammarProver] )
  Lemma( sequent ) {
    viper.instanceProver( bgThProver )
      .smtSolver( bgThProver )
      .quantTys( "nat" )
      .canSolSize( 1, 1 )
  }

}
