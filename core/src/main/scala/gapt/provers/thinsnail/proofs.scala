package gapt.provers.thinsnail

import gapt.proofs.Sequent

class ResolutionProof(
    val lctx:       LCtx,
    val clause:     Sequent[Term],
    val assertions: Set[Int],
    val parents:    Seq[ResolutionProof] ) {
  override def toString: String = clause.toString
}

object ResolutionProof {
  def normalize( lctx: LCtx, clause: Sequent[Term], assertions: Set[Int], parents: Seq[ResolutionProof] ): ResolutionProof = {
    new ResolutionProof( lctx, clause, assertions, parents )
  }
}
