package gapt.provers.thinsnail

import java.util

import gapt.utils.{ UNone, UOption, USome }
import gapt.expr
import gapt.expr.TVar
import gapt.proofs.Sequent

import scala.collection.mutable

sealed abstract class Term {
  def size: Int = {
    var result = 0
    def g( term: Term ): Unit =
      term match {
        case IsVar( _ ) =>
        case IsCon( _ ) => result += 1
        case IsFn( f ) =>
          result += 1
          for ( arg <- f ) g( arg )
      }
    g( this )
    result
  }

  def fvs: Set[Var] = {
    val result = Set.newBuilder[Var]
    def g( t: Term ): Unit =
      t match {
        case v: Var   => result += v
        case _: FnSym =>
        case f: Fn    => f.foreach( g )
      }
    g( this )
    result.result()
  }

  override def toString: String = {
    val out = new mutable.StringBuilder()
    def p( t: Term ): Unit =
      t match {
        case IsVar( i ) => out.append( '#' ).append( i.idx )
        case IsCon( c ) => out.append( c.name )
        case IsFn( f ) =>
          out.append( f.name )
          if ( f.arity > 0 ) {
            out.append( '(' )
            for ( i <- 0 until f.arity ) {
              p( f( i ) )
              if ( i != f.arity - 1 ) out.append( ',' )
            }
            out.append( ')' )
          }
      }
    p( this )
    out.result()
  }
}

case class Var( idx: Int ) extends Term {
  def +( off: Int ): Var = Var( idx + off )
}

class FnSym(
    val arity:            Int,
    val name:             String,
    val tyLCtx:           LCtx,
    val retTy:            UOption[Term],
    val argTys:           Array[UOption[Term]],
    val extraTyParamArgs: Array[Int],
    val needToPropagate:  Array[Boolean] ) extends Term with DiscrTree.Label {
  def ty: UOption[Term] = retTy
  def isType: Boolean = retTy.isEmpty
  override def hashCode: Int = 31 * arity.hashCode + name.hashCode
}

class Fn(
    val fnSym:          FnSym,
    private val argArr: Array[Term] ) extends Term {
  def name: String = fnSym.name

  def arity: Int = argArr.length
  def apply( i: Int ): Term = argArr( i )
  def args: IndexedSeq[Term] = argArr

  def map( f: Term => Term ): Fn = {
    val newArgs = argArr.clone()
    var i = 0
    while ( i < newArgs.length ) {
      newArgs( i ) = f( newArgs( i ) )
      i += 1
    }
    new Fn( fnSym, newArgs )
  }

  def updated( i: Int, term: Term ): Term = {
    val newArgs = argArr.clone()
    newArgs( i ) = term
    new Fn( fnSym, newArgs )
  }

  def forall( f: Term => Boolean ): Boolean =
    argArr.forall( f )
  def exists( f: Term => Boolean ): Boolean =
    argArr.exists( f )
  def foreach( f: Term => Unit ): Unit =
    argArr.foreach( f )

  override val hashCode: Int =
    31 * util.Arrays.hashCode( argArr.asInstanceOf[Array[AnyRef]] ) + fnSym.hashCode
  override def equals( that: Any ): Boolean =
    that match {
      case that: AnyRef if this eq that => true
      case that: Fn =>
        this.hashCode == that.hashCode &&
          this.fnSym == that.fnSym &&
          this.args == that.args
      case _ => false
    }
}

object Fn {
  def apply( fnSym: FnSym, args: Iterable[Term] ): Fn =
    new Fn( fnSym, args.toArray )

  def apply( fnSym: FnSym, args: Term* ): Fn = apply( fnSym, args )

  def unapply( term: Term ): Option[( FnSym, IndexedSeq[Term] )] =
    term match {
      case f: Fn => Some( ( f.fnSym, f.args ) )
      case _     => None
    }
}

object IsVar {
  def apply( t: Term ): Boolean =
    t match {
      case _: Var => true
      case _      => false
    }
  def unapply( t: Var ): Option[Var] = Some( t )
}
object IsFn {
  def unapply( t: Fn ): Option[Fn] = Some( t )
}
object IsCon {
  def unapply( t: FnSym ): Some[FnSym] = Some( t )
}

sealed trait LCtxElem {
  def isTy: Boolean = this == LCtxElem.IsTy
  def +( off: Int ): LCtxElem
}
object LCtxElem {
  case object IsTy extends LCtxElem {
    def +( off: Int ): LCtxElem = IsTy
  }
  case class HasTy( off: Int, ty: Term ) extends LCtxElem {
    def +( off2: Int ): LCtxElem = HasTy( off + off2, ty )
  }
}

class LCtx(
    private val tys: mutable.ArrayBuffer[LCtxElem] ) {

  def isTy( term: Term ): Boolean = term match {
    case IsCon( c ) => c.isType
    case IsFn( f )  => f.fnSym.isType
    case IsVar( v ) => get( v ).isTy
  }

  def get( v: Var ): LCtxElem = tys( v.idx )
  def length: Int = tys.length

  def extend( lctx: LCtx ): Int = {
    val off = length
    tys ++= lctx.tys.view.map( _ + off )
    off
  }

  def newVar(): Var = {
    val v = length
    tys += LCtxElem.IsTy
    Var( v )
  }
  def newVar( ty: Term ): Var = newVar( 0, ty )
  def newVar( off: Int, ty: Term ): Var = {
    val v = length
    tys += LCtxElem.HasTy( off, ty )
    Var( v )
  }

}

object LCtx {
  def apply(): LCtx = new LCtx( mutable.ArrayBuffer() )
}

case class Assg( off: Int, t: Term )

class Subst private (
    val lctx:         LCtx,
    private var assg: Array[Assg] ) {

  def get( v: Var ): UOption[Assg] =
    if ( v.idx >= assg.length ) UNone[Assg]() else UOption( assg( v.idx ) )

  def assign( v: Var, off: Int, t: Term ): Boolean = get( v ) match {
    case USome( Assg( off2, t2 ) ) => unify( off, t, off2, t2 )
    case _ =>
      t match { case IsVar( vt ) if v == vt + off => return true case _ => }
      if ( !checkTy( off, t, lctx.get( v ) ) )
        return false
      if ( occurs( v, off, t ) )
        return false
      if ( assg.length <= v.idx ) {
        val oldAssg = assg
        assg = new Array( 2 * math.max( lctx.length, v.idx + 1 ) )
        oldAssg.copyToArray( assg )
      }
      assg( v.idx ) = Assg( off, t )
      true
  }

  def checkTy( offTerm: Int, term: Term, lctxElem: LCtxElem ): Boolean =
    lctxElem match {
      case LCtxElem.IsTy               => lctx.isTy( term )
      case LCtxElem.HasTy( offTy, ty ) => checkTy( offTerm, term, offTy, ty )
    }

  def occurs( v: Var, off: Int, term: Term ): Boolean =
    term match {
      case IsVar( v2 ) =>
        val v2_ = v2 + off
        get( v2_ ) match {
          case USome( Assg( off_, term_ ) ) =>
            occurs( v, off_, term_ )
          case _ => v == v2_
        }
      case IsCon( _ ) => false
      case IsFn( f )  => f.exists( occurs( v, off, _ ) )
    }

  def checkTy( offTerm: Int, term: Term,
               offTy: Int, ty: UOption[Term] )( implicit dummyImplicit: DummyImplicit ): Boolean =
    ty match {
      case USome( ty2 ) => checkTy( offTerm, term, offTy, ty2 )
      case _            => lctx.isTy( term )
    }

  def checkTy( offTerm: Int, term: Term,
               offTy: Int, ty: Term ): Boolean =
    term match {
      case IsVar( v ) =>
        lctx.get( v + offTerm ) match {
          case LCtxElem.IsTy => false
          case LCtxElem.HasTy( offTy2, ty2 ) =>
            unify( offTy, ty, offTy2, ty2 )
        }
      case IsCon( c ) =>
        c.ty match {
          case USome( ty2 ) => unify( offTy, ty, 0, ty2 )
          case _ =>
            false
        }
      case IsFn( f ) =>
        val fs = f.fnSym
        val fsOff = lctx.extend( fs.tyLCtx )
        fs.retTy match {
          case USome( retTy ) =>
            unify( fsOff, retTy, offTy, ty ) &&
              ( 0 until fs.arity ).forall( i =>
                !fs.needToPropagate( i ) ||
                  checkTy( offTerm, f( i ), fsOff, fs.argTys( i ) ) )
          case _ =>
            false
        }
    }

  def unify( off1: Int, t1: Term,
             off2: Int, t2: Term ): Boolean =
    ( t1, t2 ) match {
      case ( IsCon( c1 ), IsCon( c2 ) ) => c1 == c2
      case ( IsFn( f1 ), IsFn( f2 ) ) =>
        f1.fnSym == f2.fnSym &&
          ( 0 until f1.arity ).forall( i =>
            unify( off1, f1( i ), off2, f2( i ) ) )
      case ( IsVar( v1 ), _ ) =>
        assign( v1 + off1, off2, t2 )
      case ( _, IsVar( _ ) ) => unify( off2, t2, off1, t1 )
      case ( _, _ ) =>
        false
    }

  def matching( off1: Int, t1: Term,
                off2: Int, t2: Term ): Boolean =
    ( t1, t2 ) match {
      case ( IsCon( c1 ), IsCon( c2 ) ) => c1 == c2
      case ( IsFn( f1 ), IsFn( f2 ) ) =>
        f1.fnSym == f2.fnSym &&
          ( 0 until f1.arity ).forall( i =>
            matching( off1, f1( i ), off2, f2( i ) ) )
      case ( IsVar( v1 ), _ ) =>
        assign( v1 + off1, off2, t2 )
      case ( _, _ ) =>
        false
    }

  def apply( off: Int, t: Sequent[Term] ): Sequent[Term] =
    t.map( apply( off, _ ) )

  def apply( off: Int, t: Term ): Term =
    t match {
      case IsVar( v ) => apply( v + off )
      case IsCon( c ) => c
      case IsFn( f )  => f.map( apply( off, _ ) )
    }

  def apply( v: Var ): Term =
    get( v ) match {
      case USome( Assg( off, t ) ) =>
        apply( off, t )
      case _ => v
    }

  override def clone(): Subst =
    new Subst( lctx, assg.clone() )
}

object Subst {
  def apply( lctx: LCtx ): Subst = new Subst( lctx, Array() )
  def apply(): Subst = apply( LCtx() )
}

class Ctx( val cx: gapt.proofs.context.mutable.MutableContext ) { ctx =>

  val baseTys: mutable.Map[( String, Int ), FnSym] = mutable.Map()
  val fnSyms: mutable.Map[( String, Int ), FnSym] = mutable.Map()

  val arrTyFnSym: FnSym = new FnSym(
    arity = 2,
    name = "->:",
    tyLCtx = LCtx(),
    retTy = UNone(),
    argTys = Array( UNone(), UNone() ),
    extraTyParamArgs = Array(),
    needToPropagate = Array( false, false ) )

  val appFnSym: FnSym = {
    val lctx = LCtx()
    val a = lctx.newVar()
    val b = lctx.newVar()
    new FnSym(
      arity = 2,
      name = "@",
      tyLCtx = lctx,
      retTy = USome( b ),
      argTys = Array( USome( Fn( arrTyFnSym, a, b ) ), USome( a ) ),
      extraTyParamArgs = Array(),
      needToPropagate = Array( true, false ) )
  }

  def allFnSyms: Set[FnSym] =
    Set.empty ++ baseTys.values ++ fnSyms.values + arrTyFnSym + appFnSym

  def internBaseTy( name: String, arity: Int ): FnSym =
    fnSyms.getOrElseUpdate( name -> arity, new FnSym(
      arity = arity,
      name = name,
      tyLCtx = LCtx(),
      retTy = UNone(),
      argTys = ( 0 until arity ).map( _ => UNone(): UOption[Term] ).toArray,
      extraTyParamArgs = Array(),
      needToPropagate = ( 0 until arity ).map( _ => false ).toArray ) )

  private def etaExpand( const: expr.Const, arity: Int ): expr.Const = {
    val expr.FunctionType( retTy, argTys ) = const.ty
    if ( argTys.size >= arity ) const else {
      val nameGen = expr.rename.awayFrom( expr.typeVariables( const ) )
      val a = TVar( nameGen.fresh( "a" ) )
      etaExpand( expr.Substitution( Map(), Map( retTy.asInstanceOf[TVar] -> ( a ->: retTy ) ) )( const ), arity )
    }
  }

  def internFnSym( name: String, arity: Int ): FnSym =
    fnSyms.getOrElseUpdate( name -> arity, {
      val Some( decl ) = cx.constant( name ).map( etaExpand( _, arity ) )
      val expr.FunctionType( retTy0, argTys0 ) = decl.ty
      val argTys = argTys0.take( arity )
      val retTy = expr.FunctionType( retTy0, argTys0.drop( arity ) )
      val needExplicitly = expr.typeVariables( decl.params ).
        diff( expr.typeVariables( argTys ) ).toVector
      val interner = new Interner
      new FnSym(
        arity = arity + needExplicitly.size,
        name = name,
        tyLCtx = interner.lctx,
        retTy = USome( interner.intern( retTy ) ),
        argTys = ( argTys.view.map( interner.intern ).map( USome( _ ) ) ++
          needExplicitly.map( _ => UNone[Term]() ) ).toArray,
        extraTyParamArgs = needExplicitly.view.map( v => decl.params.indexOf( v ) ).toArray,
        needToPropagate = {
          val idxs = expr.typeVariables( retTy ).map( v =>
            if ( needExplicitly.contains( v ) ) arity + needExplicitly.indexOf( v )
            else argTys.indexWhere( expr.typeVariables( _ ).contains( v ) ) )
          ( 0 until ( arity + needExplicitly.size ) ).map( idxs.contains ).toArray
        } )
    } )

  class Interner {
    val lctx: LCtx = LCtx()
    val vs: mutable.Map[expr.Var, Var] = mutable.Map()
    val tyVs: mutable.Map[TVar, Var] = mutable.Map()

    def intern( t: expr.Ty ): Term =
      t match {
        case v @ expr.TVar( _ ) =>
          tyVs.getOrElseUpdate( v, lctx.newVar() )
        case expr.TBase( n, ps ) =>
          val fnSym = internBaseTy( n, ps.size )
          if ( fnSym.arity == 0 ) fnSym else {
            Fn( fnSym, ps.map( intern ) )
          }
        case expr.TArr( a, b ) =>
          Fn( arrTyFnSym, Seq( intern( a ), intern( b ) ) )
      }

    def intern( e: expr.Expr ): Term =
      e match {
        case e @ expr.Var( _, t ) =>
          vs.getOrElseUpdate( e, lctx.newVar( intern( t ) ) )
        case e @ expr.Apps( expr.Const( n, _, ps ), args ) =>
          val fnSym = internFnSym( n, args.size )
          if ( fnSym.arity == 0 ) fnSym else {
            Fn( fnSym, args.map( intern ) ++ fnSym.extraTyParamArgs.map {
              case -1 => intern( e.ty )
              case i  => intern( ps( i ) )
            } )
          }
        case expr.Apps( v @ expr.Var( _, _ ), b ) =>
          val v_ = intern( v )
          b.map( intern ).foldLeft( v_ )( Fn( appFnSym, _, _ ) )
        case expr.Apps( lam @ expr.Abs.Block( xs, b ), args ) =>
          val fvs = expr.freeVariables( lam ).toVector
          val c = cx.addDefinition( expr.Abs( fvs, lam ) )
          intern( c( fvs )( args ) )
      }
  }

}