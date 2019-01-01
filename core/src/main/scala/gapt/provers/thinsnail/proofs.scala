package gapt.provers.thinsnail

import gapt.proofs.{ HOLSequent, Sequent }

import scala.collection.mutable

class ResolutionProof(
    val lctx:       LCtx,
    val clause:     Sequent[Term],
    val assertions: Set[Int],
    val parents:    Seq[ResolutionProof] ) {
  override def toString: String = clause.toString
}

private class Normalizer( oldLCtx: LCtx, newLCtx: LCtx ) {
  private val map = mutable.Map[Var, Var]()
  def go( t: Term ): Term = go( 0, t )
  def go( off: Int, t: Term ): Term =
    t match {
      case v: Var =>
        map.getOrElseUpdate( v + off, oldLCtx.get( v + off ) match {
          case LCtxElem.IsTy => newLCtx.newVar()
          case LCtxElem.HasTy( tyOff, ty ) =>
            newLCtx.newVar( go( tyOff, ty ) )
        } )
      case c: FnSym => c
      case f: Fn =>
        f.map( go( off, _ ) )
    }
}

object ResolutionProof {
  def normalize( lctx: LCtx, clause: Sequent[Term], assertions: Set[Int], parents: Seq[ResolutionProof] ): ResolutionProof = {
    val newLCtx = LCtx()
    val norm = new Normalizer( lctx, newLCtx )
    new ResolutionProof( newLCtx, clause.map( norm.go ), assertions, parents )
  }
}
