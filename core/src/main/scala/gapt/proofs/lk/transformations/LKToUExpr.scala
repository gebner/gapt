package gapt.proofs.lk.transformations

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.untyped._
import gapt.expr.util.{ freeVariables, rename }
import gapt.logic.Polarity
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules._
import gapt.utils.NameGenerator
import Polarity._

class LKToUExpr(
    var rctx: RCtx,
    nameGen:  NameGenerator ) {

  def mkCon( n: String ): UCon = UCon( nameGen.fresh( n ) )
  def mkConI( n: String ): UCon = UCon( nameGen.freshWithIndex( n ) )

  val rfl = mkCon( "rfl" )
  val triv = mkCon( "triv" )

  val prod = mkCon( "prod" )
  val fst = mkCon( "fst" )
  val snd = mkCon( "snd" )
  rctx += RR( UApp( fst, UApps( prod, UVar( 0 ), UVar( 1 ) ) ), UVar( 0 ) )
  rctx += RR( UApp( snd, UApps( prod, UVar( 0 ), UVar( 1 ) ) ), UVar( 1 ) )

  // pairleft k l r = k (prod l r)
  val pairleft = mkCon( "pairleft" )
  rctx += RR( UApps( pairleft, 0, 1, 2 ), UApp( 0, UApps( prod, 1, 2 ) ) )

  sealed trait Arg
  case class AForm( formula: Formula, polarity: Polarity ) extends Arg
  case class AEigenVar( eigenVar: Var ) extends Arg
  def ASucc( formula: Formula ): AForm = AForm( formula, InSuccedent )
  def AAnt( formula: Formula ): AForm = AForm( formula, InAntecedent )

  def go( p: LKProof ): ( UExpr, List[Arg] ) =
    p match {
      case LogicalAxiom( f ) =>
        UApp( UVar( 1 ), UVar( 0 ) ) -> List( AAnt( f ), ASucc( f ) )
      case p @ ReflexivityAxiom( _ ) =>
        UApp( UVar( 0 ), rfl ) -> List( ASucc( p.mainFormula ) )
      case p @ TopAxiom =>
        UApp( UVar( 0 ), triv ) -> List( ASucc( p.mainFormula ) )
      case p @ BottomAxiom =>
        UVar( 0 ) -> List( AAnt( p.mainFormula ) )

      case p: EqualityRule =>
        val ( e, a ) = go( p.subProof )
        e -> a.map( b => if ( b == AForm( p.auxFormula, p.aux.polarity ) )
          AForm( p.mainFormula, p.aux.polarity )
        else b )

      case p: ContractionRule    => go( p.subProof )
      case p: WeakeningLeftRule  => go( p.subProof )
      case p: WeakeningRightRule => go( p.subProof )

      case p: CutRule =>
        val ( e1, a1 ) = go( p.leftSubProof )
        val ( e2, a2 ) = bound( p.rightSubProof, p.cutFormula, InAntecedent, "cut" )
        val as = ( a1.filterNot( _ == ASucc( p.cutFormula ) ) ++ a2 ).distinct
        renameExcept( e1, a1, as, ASucc( p.cutFormula ), rename( e2, a2, as ) ) -> as

      case p: NegLeftRule =>
        val ( e, a ) = go( p.subProof )
        e -> a.map( x => if ( x == ASucc( p.auxFormula ) ) AAnt( p.mainFormula ) else x )
      case p: NegRightRule =>
        val ( e, a ) = bound( p.subProof, p.auxFormula, InAntecedent, "negr" )
        UApp( UVar( a.size ), e ) -> ( a :+ ASucc( p.mainFormula ) )

      case p: ImpRightRule =>
        val ( e, a ) = bound( p.subProof, ASucc( p.impConclusion ), AAnt( p.impPremise ), "impr" )
        UApp( UVar( a.size ), e ) -> ( a :+ ASucc( p.mainFormula ) )
      case p: ImpLeftRule =>
        val ( e1, a1 ) = go( p.leftSubProof )
        val ( e2, a2 ) = bound( p.rightSubProof, p.impConclusion, InAntecedent, "impl" )
        val as = ( a1.filterNot( _ == ASucc( p.impPremise ) ) ++ a2 ).distinct :+ AAnt( p.mainFormula )
        renameExcept( e1, a1, as, ASucc( p.impPremise ),
          UApp( UVar( as.indices.last ), rename( e2, a2, as ) ) ) -> as

      // ∀ ↝ ∀¬¬
      case p: ForallRightRule =>
        val ( e, a ) = bound( p.subProof, AEigenVar( p.eigenVariable ), ASucc( p.auxFormula ), "allr" )
        UApp( UVar( a.size ), e ) -> ( a :+ ASucc( p.mainFormula ) )
      case p: ForallLeftRule =>
        val ( e, a ) = bound( p.subProof, AAnt( p.auxFormula ), "alll" )
        val a_ = ( a ++ freeVariables( p.term ).map( AEigenVar ) :+ AAnt( p.mainFormula ) ).distinct
        val t = go( p.term, v => a_.indexOf( AEigenVar( v ) ).ensuring( _ >= 0 ) )
        UApps( UVar( a_.indexOf( AAnt( p.mainFormula ) ) ), t, e ) -> a_

      case p: ExistsLeftRule =>
        val ( e, a ) = bound( p.subProof, AEigenVar( p.eigenVariable ), AAnt( p.auxFormula ), "exl" )
        UApp( UVar( a.size ), e ) -> ( a :+ AAnt( p.mainFormula ) )
      case p: ExistsRightRule =>
        val ( e, a ) = bound( p.subProof, AAnt( p.auxFormula ), "alll" )
        val a_ = ( a ++ freeVariables( p.term ).map( AEigenVar ) :+ AAnt( p.mainFormula ) ).distinct
        val t = go( p.term, v => a_.indexOf( AEigenVar( v ) ).ensuring( _ >= 0 ) )
        UApps( UVar( a_.indexOf( AAnt( p.mainFormula ) ) ), t, e ) -> a_

      case p: AndLeftRule =>
        val ( e, a ) = go( p.subProof )
        val as = ( a.toSet.diff( Set[Arg]( AAnt( p.leftConjunct ), AAnt( p.rightConjunct ) ) ) + AAnt( p.mainFormula ) ).toList
        val conj = UVar( as.indexOf( AAnt( p.mainFormula ) ) )
        renameExcept( e, a, as,
          AAnt( p.leftConjunct ) -> UApp( fst, conj ),
          AAnt( p.rightConjunct ) -> UApp( snd, conj ) ) -> as
      case p: AndRightRule =>
        val ( e1, a1 ) = go( p.leftSubProof )
        val ( e2, a2 ) = go( p.rightSubProof )
        val as = ( ( a1.toSet ++ a2 ).diff( Set( ASucc( p.leftConjunct ), ASucc( p.rightConjunct ) ) ) + ASucc( p.mainFormula ) ).toList
        val ( e2_, a2_ ) = bind(
          e2.subst( i => if ( a2( i ) == ASucc( p.rightConjunct ) ) UApps( pairleft, i, a2.size ) else UVar( i ) ),
          a2 :+ AAnt( p.leftConjunct ), List( AAnt( p.leftConjunct ) ), "andr" )
        val conj = UVar( as.indexOf( ASucc( p.mainFormula ) ).ensuring( _ >= 0 ) )
        renameExcept( e1, a1, as,
          ASucc( p.leftConjunct ),
          renameExcept( e2_, a2_, as,
            ASucc( p.rightConjunct ), conj ) ) -> as
    }

  def go( e: Expr, vs: Var => Int ): UExpr =
    e match {
      case Const( n, _, _ ) => UCon( n )
      case App( a, b )      => UApp( go( a, vs ), go( b, vs ) )
      case v: Var           => UVar( vs( v ) )
    }

  def renameExcept[T]( e: UExpr, from: List[T], to: List[T], x: ( T, UExpr )* ): UExpr =
    renameExcept( e, from, to, x.toMap )

  def renameExcept[T]( e: UExpr, from: List[T], to: List[T], x: Map[T, UExpr] ): UExpr =
    e.subst( Map() ++ from.zipWithIndex.map {
      case ( a, i ) => i -> x.getOrElse( a, UVar( to.indexOf( a ) ) )
    } )

  def renameExcept[T]( e: UExpr, from: List[T], to: List[T], x: T, y: UExpr ): UExpr =
    renameExcept( e, from, to, Map( x -> y ) )

  def rename[T]( e: UExpr, from: List[T], to: List[T] ): UExpr =
    e.subst( Map() ++ from.zipWithIndex.map {
      case ( a, i ) => i -> UVar( to.indexOf( a ) )
    } )

  def bound( p: LKProof, f: Formula, pol: Polarity, n: String ): ( UExpr, List[Arg] ) =
    bound( p, AForm( f, pol ), n )
  def bound( p: LKProof, arg: Arg, n: String ): ( UExpr, List[Arg] ) = {
    val ( e, as ) = go( p )
    bind( e, as, List( arg ), n )
  }

  def bound( p: LKProof, arg1: Arg, arg2: Arg, n: String ): ( UExpr, List[Arg] ) = {
    val ( e, as ) = go( p )
    bind( e, as, List( arg1, arg2 ), n )
  }

  def bind( e: UExpr, as: List[Arg], bs: List[Arg], n: String ): ( UExpr, List[Arg] ) = {
    val as_ = as.distinct.diff( bs ) ++ bs
    val c = mkConI( n )
    rctx += RR(
      UApps( c, as_.indices.map( UVar ) ),
      e.subst( Map() ++ as.zipWithIndex.map {
        case ( a, i ) =>
          i -> UVar( as_.indexOf( a ) )
      } ) )
    UApps( c, as_.indices.dropRight( bs.size ).map( UVar ) ) -> as_.dropRight( bs.size )
  }

  def boundAll( p: LKProof, n: String ): UCon = {
    val ( e, as ) = go( p )
    val c = mkCon( n )
    rctx += RR( UApps( c, as.indices.map( UVar ) ), e )
    c
  }

}

object LKToUExpr {
  def apply( p: LKProof ): RCtx = {
    val helper = new LKToUExpr( RCtx.empty, rename.awayFrom( containedNames( p ) ) )
    helper.boundAll( p, "main" )
    helper.rctx
  }
}
