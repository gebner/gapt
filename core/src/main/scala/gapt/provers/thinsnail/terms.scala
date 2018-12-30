package gapt.provers.thinsnail

import gapt.utils.{ UNone, UOption, USome }
import gapt.expr

import scala.collection.mutable

class Con(
    val arity: Int,
    val name:  String,
    val ty:    UOption[Term] ) {
  def toTerm: Term = new Term( this )
  def isType: Boolean = ty.isEmpty
}

case class Var( idx: Int ) extends AnyVal {
  def toTerm: Term = new Term( Integer.valueOf( idx ) )
  def +( off: Int ): Var = Var( idx + off )
}

class FnSym(
    val arity:           Int,
    val name:            String,
    val tyLCtx:          LCtx,
    val retTy:           UOption[Term],
    val argTys:          Array[UOption[Term]],
    val needToPropagate: Array[Boolean] ) {
  def isType: Boolean = retTy.isEmpty
}

class Fn( private val raw: Array[AnyRef] ) extends AnyVal {
  def toTerm: Term = new Term( raw )

  def fnSym: FnSym = raw( 0 ).asInstanceOf[FnSym]

  def arity: Int = raw.length - 1
  def apply( i: Int ): Term = new Term( raw( i + 1 ) )
  def args: IndexedSeq[Term] = ( 0 until arity ).map( apply )

  def map( f: Term => Term ): Fn = {
    val newRaw = raw.clone()
    var i = 1
    while ( i < newRaw.length ) {
      newRaw( i ) = f( new Term( newRaw( i ) ) ).raw
      i += 1
    }
    new Fn( newRaw )
  }

  def forall( f: Term => Boolean ): Boolean =
    ( 0 until arity ).forall( i => f( args( i ) ) )
  def exists( f: Term => Boolean ): Boolean =
    ( 0 until arity ).exists( i => f( args( i ) ) )
}

object Fn {
  def apply( fnSym: FnSym, args: Seq[Term] ): Fn =
    new Fn( ( Vector( fnSym ) ++ args.view.map( _.raw ) ).toArray )
}

class Term( val raw: AnyRef ) extends AnyVal
object Term {
  implicit def ofVar( v: Var ): Term = v.toTerm
  implicit def ofFn( f: Fn ): Term = f.toTerm
  implicit def ofCon( c: Con ): Term = c.toTerm
}

object IsVar {
  def unapply( t: Term ): Option[Var] =
    t.raw match {
      case i: Integer => Some( Var( i ) )
      case _          => None
    }
}
object IsFn {
  def unapply( t: Term ): Option[Fn] =
    t.raw match {
      case a: Array[AnyRef] => Some( new Fn( a ) )
      case _                => None
    }
}
object IsCon {
  def unapply( t: Term ): Option[Con] =
    t.raw match {
      case c: Con => Some( c )
      case _      => None
    }
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

class Subst(
    val lctx:         LCtx,
    private var assg: Array[UOption[Assg]] ) {

  def get( v: Var ): UOption[Assg] =
    if ( v.idx < assg.length ) UNone() else assg( v.idx )

  def assign( v: Var, off: Int, t: Term ): Boolean = get( v ) match {
    case USome( Assg( off2, t2 ) ) => unify( off, t, off2, t2 )
    case _ =>
      if ( !checkTy( off, t, lctx.get( v ) ) ) return false
      if ( occurs( v, off, t ) ) return false
      if ( assg.length < v.idx ) {
        val oldAssg = assg
        assg = new Array( 2 * math.max( lctx.length, v.idx + 1 ) )
        oldAssg.copyToArray( assg )
      }
      assg( v.idx ) = USome( Assg( off, t ) )
      true
  }

  def checkTy( offTerm: Int, term: Term, lctxElem: LCtxElem ): Boolean =
    lctxElem match {
      case LCtxElem.IsTy               => lctx.isTy( term )
      case LCtxElem.HasTy( offTy, ty ) => checkTy( offTerm, term, offTy, ty )
    }

  def occurs( v: Var, off: Int, term: Term ): Boolean =
    term match {
      case IsVar( v2 ) => v == v2 + off
      case IsCon( _ )  => false
      case IsFn( f )   => f.exists( occurs( v, off, _ ) )
    }

  def checkTy( offTerm: Int, term: Term,
               offTy: Int, ty: UOption[Term] ): Boolean =
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
          case _            => false
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
          case _ => false
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
      case ( _, _ )          => false
    }

}

class Ctx(
    val baseTys: mutable.Map[( String, Int ), FnSym],
    val fnSyms:  mutable.Map[( expr.Const, Int ), FnSym],
    val consts:  mutable.Map[expr.Const, Term] ) { ctx =>

  def intern( c: expr.Const ): Term = {
    consts.getOrElseUpdate(
      c,
      if ( c.params.isEmpty ) ??? //new Con()
      else {
        val interner = new Interner
        val ps2 = c.params.map( interner.intern )
        Fn( new FnSym(
          arity = c.params.size,
          name = c.name,
          tyLCtx = interner.lctx,
          retTy = USome( interner.intern( c.ty ) ),
          argTys = c.params.map( _ => UNone() ).toArray,
          needToPropagate = c.params.map( _ => false ).toArray // TODO: correct?
        ), ps2 )
      } )
  }

  private class Interner {
    val lctx = LCtx()
    val vs = mutable.Map[expr.Var, Var]()
    val tyVs = mutable.Map[expr.TVar, Var]()

    def intern( t: expr.Ty ): Term = ???

    def intern( e: expr.Expr ): Term =
      e match {
        case e @ expr.Var( n, t ) =>
          vs.getOrElseUpdate( e, lctx.newVar( intern( t ) ) )
        case e @ expr.Const( n, t, ps ) =>
          ctx.intern( e )
      }
  }

}