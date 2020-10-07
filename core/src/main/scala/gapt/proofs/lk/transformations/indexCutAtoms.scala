package gapt.proofs.lk.transformations

import gapt.expr.{ Abs, App, Const, Expr, Var }
import gapt.proofs.{ Ant, HOLSequent, SequentConnector, Suc }
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk._
import gapt.proofs.lk.rules._
import gapt.expr.formula._
import gapt.expr.formula.hol.instantiate
import gapt.expr.subst.Substitution
import gapt.utils.Maybe

object indexCutAtoms {

  def apply( p: LKProof )( implicit ctx: Maybe[MutableContext] ): LKProof =
    apply( p, p.endSequent )( ctx.getOrElse( MutableContext.guess( p ) ) )

  def rename( f: Formula )( implicit ctx: MutableContext ): Formula = f match {
    case f @ Atom( c: Const, args ) =>
      Atom( ctx.addDefinition( c, ctx.newNameGenerator.freshWithIndex( c.name ), reuse = false ), args )
    case Iff( a, b )      => Iff( rename( a ), rename( b ) )
    case And( a, b )      => And( rename( a ), rename( b ) )
    case Or( a, b )       => Or( rename( a ), rename( b ) )
    case Imp( a, b )      => Imp( rename( a ), rename( b ) )
    case Neg( a )         => Neg( rename( a ) )
    case All( x, a )      => All( x, rename( a ) )
    case Ex( x, a )       => Ex( x, rename( a ) )
    case Top() | Bottom() => f
    case Eq( _, _ )       => f
  }

  def apply( p: LKProof, es: HOLSequent )( implicit ctx: MutableContext ): LKProof = p match {

    case p @ CutRule( q, i, r, j ) =>
      val newCutF = rename( p.cutFormula )
      CutRule( apply( q, p.getLeftSequentConnector.parent( es, newCutF ) ), i,
        apply( r, p.getRightSequentConnector.parent( es, newCutF ) ), j )

    case LogicalAxiom( a ) =>
      if ( es( Ant( 0 ) ) == es( Suc( 0 ) ) ) LogicalAxiom( es( Ant( 0 ) ) )
      else ProofLink( Bottom(), es )
    case TopAxiom | BottomAxiom  => p
    case ReflexivityAxiom( _ )   => p
    case p @ ProofLink( ref, _ ) => ProofLink( ref, es ) // FIXME FIXME FIXME

    case p @ WeakeningLeftRule( q, f ) =>
      WeakeningLeftRule( apply( q, p.getSequentConnector.parent( es ) ), es( p.mainIndices.head ) )
    case p @ WeakeningRightRule( q, f ) =>
      WeakeningRightRule( apply( q, p.getSequentConnector.parent( es ) ), es( p.mainIndices.head ) )

    case p @ ContractionLeftRule( q, i, j ) =>
      ContractionLeftRule( apply( q, p.getSequentConnector.parent( es ) ), i, j )
    case p @ ContractionRightRule( q, i, j ) =>
      ContractionRightRule( apply( q, p.getSequentConnector.parent( es ) ), i, j )

    case p @ NegLeftRule( q, i ) =>
      val Neg( f ) = es( p.mainIndices.head )
      NegLeftRule( apply( q, p.getSequentConnector.parent( es ).updated( i, f ) ), i )
    case p @ NegRightRule( q, i ) =>
      val Neg( f ) = es( p.mainIndices.head )
      NegRightRule( apply( q, p.getSequentConnector.parent( es ).updated( i, f ) ), i )

    case p @ AndLeftRule( q, i, j ) =>
      val And( f, g ) = es( p.mainIndices.head )
      AndLeftRule( apply( q, p.getSequentConnector.parent( es ).updated( i, f ).updated( j, g ) ), i, j )
    case p @ AndRightRule( q, i, r, j ) =>
      val And( f, g ) = es( p.mainIndices.head )
      AndRightRule(
        apply( q, p.getLeftSequentConnector.parent( es ).updated( i, f ) ), i,
        apply( r, p.getRightSequentConnector.parent( es ).updated( j, g ) ), j )

    case p @ OrRightRule( q, i, j ) =>
      val Or( f, g ) = es( p.mainIndices.head )
      OrRightRule( apply( q, p.getSequentConnector.parent( es ).updated( i, f ).updated( j, g ) ), i, j )
    case p @ OrLeftRule( q, i, r, j ) =>
      val Or( f, g ) = es( p.mainIndices.head )
      OrLeftRule(
        apply( q, p.getLeftSequentConnector.parent( es ).updated( i, f ) ), i,
        apply( r, p.getRightSequentConnector.parent( es ).updated( j, g ) ), j )

    case p @ ImpRightRule( q, i, j ) =>
      val Imp( f, g ) = es( p.mainIndices.head )
      ImpRightRule( apply( q, p.getSequentConnector.parent( es ).updated( i, f ).updated( j, g ) ), i, j )
    case p @ ImpLeftRule( q, i, r, j ) =>
      val Imp( f, g ) = es( p.mainIndices.head )
      ImpLeftRule(
        apply( q, p.getLeftSequentConnector.parent( es ).updated( i, f ) ), i,
        apply( r, p.getRightSequentConnector.parent( es ).updated( j, g ) ), j )

    case p @ ForallLeftRule( q, i, _, t, _ ) =>
      val newMain = es( p.mainIndices.head )
      ForallLeftRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, t ) ) ),
        i, newMain, t )
    case p @ ExistsRightRule( q, i, _, t, _ ) =>
      val newMain = es( p.mainIndices.head )
      ExistsRightRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, t ) ) ),
        i, newMain, t )

    case p @ ForallRightRule( q, i, ev, _ ) =>
      val newMain = es( p.mainIndices.head )
      ForallRightRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, ev ) ) ),
        i, newMain, ev )
    case p @ ExistsLeftRule( q, i, ev, _ ) =>
      val newMain = es( p.mainIndices.head )
      ExistsLeftRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, ev ) ) ),
        i, newMain, ev )

    case p @ ForallSkRightRule( q, i, _, skT ) =>
      val newMain = es( p.mainIndices.head )
      ForallSkRightRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, skT ) ) ),
        i, newMain, skT )
    case p @ ExistsSkLeftRule( q, i, _, skT ) =>
      val newMain = es( p.mainIndices.head )
      ExistsSkLeftRule(
        apply( q, p.getSequentConnector.parent( es ).updated( i, instantiate( newMain, skT ) ) ),
        i, newMain, skT )

    case p @ EqualityRule( q, i, j, Abs( x, replCtx ) ) =>
      def adaptCtx( ctx: Expr, newMain: Expr ): Expr =
        ( ( ctx, newMain ): @unchecked ) match {
          case ( _, newMain: Const )          => newMain
          case ( ctx: Var, _ )                => ctx
          case ( App( a, b ), App( a_, b_ ) ) => App( adaptCtx( a, a_ ), adaptCtx( b, b_ ) )
          case ( Abs( x, a ), Abs( y, b ) )   => Abs( x, adaptCtx( a, Substitution( y -> x )( b ) ) )
        }
      val newCtx = adaptCtx( replCtx, es( p.auxInConclusion ) )
      EqualityRule(
        apply( q, p.getSequentConnector.parent( es )
          //          .updated( i, es( p.eqInConclusion ) )
          .updated( j, Substitution( x -> p.what )( newCtx ).asInstanceOf[Formula] ) ),
        i, j, Abs( x, newCtx ) )
  }

}
