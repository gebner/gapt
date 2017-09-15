import at.logic.gapt.examples.Script
import at.logic.gapt.examples.tip.prod.prop_01
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ instantiate, universalClosure }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, Minimizer, minimalExpansionSequent }
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, Suc }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof, ReductiveCutElimination, extractRecSchem, instanceProof }
import at.logic.gapt.provers.OneShotProver
import at.logic.gapt.provers.escargot.{ Escargot, NonSplittingEscargot }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.viper.grammars.{ TreeGrammarProver, TreeGrammarProverOptions }
import at.logic.gapt.utils.{ Logger, Maybe }

object doubleex extends TacticsProof {
  ctx = prop_01.ctx

  if ( false ) {

    println( extractRecSchem( instanceProof( prop_01.singleInduction, Seq( le"x:nat" ) ) ) )

    val eliminationProver = new OneShotProver {
      val All.Block( xs, _ ) = prop_01.sequent.succedent.head._2
      val instProof = instanceProof( prop_01.singleInduction, xs )

      override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
        val Some( subst ) = clauseSubsumption( instProof.conclusion, seq )
        Some( ReductiveCutElimination.eliminateInduction( subst( instProof ) )( ctx.getOrElse( ??? ) ) )
      }
    }

    Logger.makeVerbose( classOf[TreeGrammarProver] )
    Lemma( prop_01.sequent ) {
      treeGrammarInduction.instanceProver( eliminationProver )
        .quantTys( "nat" )
        .canSolSize( 2, 2 )
    }

  }

  val bgTh = Normalizer(
    hoa"0 + x = x", hoa"x + 0 = x",
    hoa"S x + y = S (x + y)", hoa"x + S y = S (x + y)" )
  val bgThF = bgTh.toFormula

  def normSeq( seq: HOLSequent ): HOLSequent =
    seq.map( bgTh.normalize ).map( _.asInstanceOf[Formula] )

  val bgThProver = new OneShotProver {
    override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = ???

    override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      Escargot.getExpansionProof( bgThF +: seq ).map { foProof =>
        minimalExpansionSequent( foProof, this ).get
      }
    }

    override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
      Z3.isValid( seq.map( bgTh.normalize( _ ).asInstanceOf[Formula] ) )
  }

  Logger.makeVerbose( classOf[TreeGrammarProver] )
  Lemma( prop_01.sequent ) {
    treeGrammarInduction.instanceProver( bgThProver )
      .smtSolver( bgThProver )
      .quantTys()
      .canSolSize( 1, 1 )
  }
}
