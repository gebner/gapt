package gapt.expr.untyped

import gapt.utils.Doc

import scala.annotation.tailrec
import scala.collection.mutable
import scala.runtime.ScalaRunTime

sealed trait UExpr { self: Product =>
  override val hashCode: Int = ScalaRunTime._hashCode( self )

  def varBound: Int = this match {
    case UCon( _ )    => 0
    case UApp( a, b ) => math.max( a.varBound, b.varBound )
    case UVar( i )    => i + 1
  }

  def subst( s: Int => UExpr ): UExpr = this match {
    case UCon( _ )    => this
    case UApp( a, b ) => UApp( a.subst( s ), b.subst( s ) )
    case UVar( i )    => s( i )
  }

  def consts: Set[String] = {
    val out = Set.newBuilder[String]
    def go( e: UExpr ): Unit = e match {
      case UCon( n ) => out += n
      case UApp( a, b ) =>
        go( a ); go( b )
      case UVar( _ ) =>
    }
    go( this )
    out.result()
  }

  def /( that: UExpr ): Option[Map[Int, UExpr]] = {
    val s = mutable.Map[Int, UExpr]()
    def m( a: UExpr, b: UExpr ): Boolean =
      ( a, b ) match {
        case ( UCon( an ), UCon( bn ) ) => an == bn
        case ( UApp( a1, a2 ), UApp( b1, b2 ) ) =>
          m( a1, b1 ) && m( a2, b2 )
        case ( UVar( i ), _ ) =>
          s.get( i ) match {
            case Some( bOld ) => b == bOld
            case None         => s( i ) = b; true
          }
        case _ => false
      }
    if ( m( that, this ) ) Some( s.toMap ) else None
  }

  def toDoc: Doc = Printer.go( this ).doc
  override def toString: String = toDoc.render( Printer.lineWidth )
}

object UExpr {
  implicit def mkVar( i: Int ): UExpr = UVar( i )
}

private object Printer {
  import Doc._

  val defaultIndent = 2
  val lineWidth = 80

  def nest( doc: Doc, j: Int = defaultIndent ): Doc =
    doc.group.nest( j )

  def parens( doc: Doc ): Doc = "(" <> doc <> ")"

  case class Parenable( prec: Int, doc: Doc ) {
    def inPrec( outerPrec: Int ): Doc =
      if ( outerPrec > prec ) {
        parens( nest( doc ) )
      } else if ( outerPrec + 1 < prec ) {
        nest( doc )
      } else {
        doc
      }
  }

  def go( e: UExpr ): Parenable =
    e match {
      case UVar( i ) => Parenable( Integer.MAX_VALUE, "#" + i )
      case UCon( n ) => Parenable( Integer.MAX_VALUE, n )
      case UApps( f, as ) =>
        Parenable(
          0,
          wordwrap2( ( f :: as ).map( go( _ ).inPrec( 2 ) ) ) )
    }
}

case class UCon( name: String ) extends UExpr
case class UApp( a: UExpr, b: UExpr ) extends UExpr
case class UVar( i: Int ) extends UExpr

object UApps {
  def apply( fn: UExpr, as: UExpr* ): UExpr = apply( fn, as )
  def apply( fn: UExpr, as: Iterable[UExpr] ): UExpr = apply( fn, as.toList )
  def apply( fn: UExpr, as: List[UExpr] ): UExpr =
    as match {
      case Nil      => fn
      case a :: as_ => UApps( UApp( fn, a ), as_ )
    }

  def unapply( e: UExpr ): Some[( UExpr, List[UExpr] )] =
    Some( decompose( e, Nil ) )

  private def decompose( e: UExpr, as: List[UExpr] ): ( UExpr, List[UExpr] ) =
    e match {
      case UApp( e_, a ) => decompose( e_, a :: as )
      case _             => ( e, as )
    }
}

case class RR( lhs: UExpr, rhs: UExpr ) {
  val UApps( head @ UCon( headSym ), lhsArgs ) = lhs
  val lhsArgsSize: Int = lhsArgs.size
  require( rhs.varBound <= lhs.varBound )

  def red( exprArgs: List[UExpr] ): Option[UExpr] =
    if ( exprArgs.size >= lhsArgsSize ) {
      ( UApps( head, exprArgs.take( lhsArgsSize ) ) / lhs ).
        map( rhs.subst ).
        map( UApps( _, exprArgs.drop( lhsArgsSize ) ) )
    } else {
      None
    }

  def red( expr: UExpr ): Option[UExpr] =
    expr match {
      case UApps( UCon( `headSym` ), exprArgs ) => red( exprArgs )
      case _                                    => None
    }

  def toDoc: Doc =
    Printer.nest( lhs.toDoc <+> "->" </> rhs.toDoc )
  override def toString: String = toDoc.render( Printer.lineWidth )
}

class RCtx(
    rules:    Map[String, List[RR]],
    headSyms: List[String] ) {

  def +( rule: RR ): RCtx =
    new RCtx(
      rules = rules.updated( rule.headSym, rule :: rules( rule.headSym ) ),
      headSyms = if ( rules.contains( rule.headSym ) ) headSyms else rule.headSym :: headSyms )

  def red( expr: UExpr ): Option[UExpr] =
    expr match {
      case UApps( UCon( h ), args ) =>
        rules( h ).view.flatMap( _.red( args ) ).headOption
      case _ => None
    }

  final def whnf( expr: UExpr ): UExpr =
    red( expr ) match {
      case Some( expr_ ) => whnf( expr_ )
      case None          => expr
    }

  final def nf( expr: UExpr ): UExpr = {
    val UApps( hd, as ) = expr
    val expr1 = UApps( hd, as.map( nf ) )
    val expr2 = whnf( expr1 )
    if ( expr1 eq expr2 ) expr1 else nf( expr2 )
  }

  private def mapRules( f: RR => RR ): RCtx =
    new RCtx(
      headSyms = headSyms,
      rules = Map().withDefaultValue( Nil ) ++ rules.mapValues( _.map( f ) ) )

  def nfRhs: RCtx = mapRules( r => r.copy( rhs = nf( r.rhs ) ) )

  def deEta: RCtx = mapRules { r =>
    val UApps( rhsHead, rhsArgs ) = r.rhs
    val toDrop = rhsArgs.reverse.zip( r.lhsArgs.reverse ).takeWhile( x => x._1 == x._2 ).length
    RR( UApps( r.head, r.lhsArgs.dropRight( toDrop ) ), UApps( rhsHead, rhsArgs.dropRight( toDrop ) ) )
  }

  def reachableFrom( hs: Iterable[String] ): Set[String] = {
    val added = mutable.Set[String]()
    def go( h: String ): Unit = {
      if ( added( h ) ) return
      added += h
      for ( r <- rules( h ); c <- r.rhs.consts ) go( c )
    }
    for ( h <- hs ) go( h )
    added.toSet
  }

  def restrictToReachable( h: String ): RCtx = restrictToReachable( List( h ) )
  def restrictToReachable( hs: Iterable[String] ): RCtx = {
    val reachable = reachableFrom( hs )
    new RCtx(
      headSyms = headSyms.filter( reachable ),
      rules = rules.filter( reachable contains _._1 ) )
  }

  def toDoc: Doc =
    Doc.stack(
      ( headSyms.view ++ rules.keys ).distinct.
        flatMap( rules( _ ) ).map( _.toDoc ) )
  override def toString: String = toDoc.render( Printer.lineWidth )
}

object RCtx {
  val empty = new RCtx( Map().withDefaultValue( Nil ), Nil )
}