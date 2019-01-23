package gapt.provers.thinsnail

import gapt.expr
import gapt.proofs.resolution.{ findDerivationViaResolution, fixDerivation }
import gapt.proofs.{ HOLSequent, Sequent, SequentIndex, resolution }

import scala.collection.mutable

object normalize {
  def apply( lctx: LCtx, clause: Sequent[Term] ): ( LCtx, Sequent[Term] ) = {
    val newLCtx = LCtx()
    val map = mutable.Map[Var, Var]()
    def go( off: Int, t: Term ): Term =
      t match {
        case v: Var =>
          map.getOrElseUpdate( v + off, lctx.get( v + off ) match {
            case LCtxElem.IsTy => newLCtx.newVar()
            case LCtxElem.HasTy( tyOff, ty ) =>
              newLCtx.newVar( go( tyOff, ty ) )
          } )
        case c: FnSym => c
        case f: Fn =>
          f.map( go( off, _ ) )
      }
    ( newLCtx, clause.map( go( 0, _ ) ) )
  }
}

sealed abstract class RP {
  val lctx: LCtx
  val clause: Sequent[Term]
  val assertions: Set[Int]
  def parents: List[RP]

  def toResolutionProof( implicit ctx: Ctx ): gapt.proofs.resolution.ResolutionProof

  override def toString: String = clause.toString
}

class Input( val lctx: LCtx, val clause: Sequent[Term], val origProof: resolution.ResolutionProof ) extends RP {
  val assertions: Set[Int] = Set.empty
  def parents: List[RP] = Nil

  def toResolutionProof( implicit ctx: Ctx ): resolution.ResolutionProof = origProof
}

class Resolution(
    val p1: RP, val i1: SequentIndex,
    val p2: RP, val i2: SequentIndex,
    val lctx: LCtx, val clause: Sequent[Term] ) extends RP {
  val assertions: Set[Int] = p1.assertions.union( p2.assertions )
  def parents: List[RP] = List( p1, p2 )

  def toResolutionProof( implicit ctx: Ctx ): resolution.ResolutionProof = {
    val q1 = p1.toResolutionProof
    val q2 = p2.toResolutionProof
    resolution.Factor( resolution.MguResolution( q1, i1, q2, i2 ) )
  }
}
object Resolution {
  def apply( p1: RP, i1: SequentIndex,
             p2: RP, i2: SequentIndex,
             lctx: LCtx, clause: Sequent[Term] ): Resolution = {
    val ( lctx_, clause_ ) = normalize( lctx, clause )
    new Resolution( p1, i1, p2, i2, lctx_, clause_ )
  }
}

class General(
    val lctx:       LCtx,
    val clause:     Sequent[Term],
    val assertions: Set[Int],
    val parents:    List[RP],
    val label:      String ) extends RP {

  def toResolutionProof( implicit ctx: Ctx ): resolution.ResolutionProof = {
    // FIXME
    val deintern = ctx.deinternFor( lctx )
    val p = resolution.Input( clause.map( deintern.toExpr( _ ).asInstanceOf[expr.Formula] ) )
    fixDerivation( p, parents.map( _.toResolutionProof ) )
  }
}
object General {
  def apply( lctx: LCtx, clause: Sequent[Term], assertions: Set[Int], parents: Seq[RP], label: String ): General = {
    val ( lctx_, clause_ ) = gapt.provers.thinsnail.normalize( lctx, clause )
    new General( lctx_, clause_, assertions, parents.toList, label )
  }
}
