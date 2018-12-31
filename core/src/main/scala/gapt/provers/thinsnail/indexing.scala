package gapt.provers.thinsnail

import DiscrTree._
import gapt.utils._

class TermString( private val stack: List[Term] ) extends AnyVal {
  def isEmpty: Boolean = stack.isEmpty
  def jump: TermString = new TermString( stack.tail )
  def next: UOption[( Label, TermString )] =
    stack match {
      case Nil => UNone()
      case IsVar( v ) :: rest =>
        USome( ( Variable, new TermString( rest ) ) )
      case IsCon( c ) :: rest =>
        USome( ( c, new TermString( rest ) ) )
      case IsFn( f ) :: rest =>
        USome( ( f.fnSym, new TermString( f.args.toList ++ rest ) ) )
    }
  def toList: List[Label] =
    next match {
      case USome( ( hd, tl ) ) => hd :: tl.toList
      case _                   => Nil
    }
}
object TermString {
  def apply( e: Term ): TermString = new TermString( e :: Nil )
}

sealed trait DiscrTree[+T] {
  def isEmpty: Boolean =
    this match {
      case Leaf( elems ) => elems.isEmpty
      case Node( next )  => next.values.forall( _.isEmpty )
    }

  def filter( p: T => Boolean ): DiscrTree[T] =
    this match {
      case Leaf( elems ) => Leaf( elems.filter( p ) )
      case Node( next )  => Node( Map() ++ next.mapValues( _.filter( p ) ) )
    }

  def remove[S >: T]( t: S ): DiscrTree[T] = filter( _ != t )

  def jump( n: Int = 1 ): Vector[DiscrTree[T]] = {
    val result = Vector.newBuilder[DiscrTree[T]]
    def walk( t: DiscrTree[T], n: Int ): Unit =
      t match {
        case _ if n == 0 =>
          result += t
        case Leaf( _ ) =>
          result += t
        case Node( next ) =>
          for ( ( l, ch ) <- next )
            walk( ch, n - 1 + l.arity )
      }
    walk( this, n )
    result.result()
  }

  def foreach( f: T => Unit ): Unit =
    this match {
      case Leaf( elems ) => elems.foreach( f )
      case Node( next )  => next.values.foreach( _.foreach( f ) )
    }

  def elements: Vector[T] = {
    val builder = Vector.newBuilder[T]
    foreach( builder += _ )
    builder.result()
  }

  def insert[S >: T]( es: Iterable[( Term, S )] ): DiscrTree[S] =
    es.foldLeft[DiscrTree[S]]( this ) { case ( dt, ( e, t ) ) => dt.insert( e, t ) }
  def insert[S >: T]( es: Iterable[Term], t: S ): DiscrTree[S] =
    es.foldLeft[DiscrTree[S]]( this )( _.insert( _, t ) )
  def insert[S >: T]( e: Term, t: S ): DiscrTree[S] =
    insert( TermString( e ), t, DiscrTree.maxDepth )
  def insert[S >: T]( e: TermString, t: S, ttl: Int ): DiscrTree[S] =
    ( e.next, this ) match {
      case ( USome( ( label, e_ ) ), Node( next ) ) =>
        Node( next.updated(
          label,
          next.getOrElse( label, if ( e_.isEmpty || ttl < 0 ) Leaf[S]( Vector.empty ) else Node[S]( Map() ) ).
            insert( e_, t, ttl - 1 ) ) )
      case ( _, Leaf( elems ) ) => Leaf( elems :+ t )
      case _ =>
        throw new IllegalStateException
    }

  def generalizations( e: Term ): Vector[T] = generalizations( TermString( e ) )
  def generalizations( e: TermString ): Vector[T] =
    ( e.next, this ) match {
      case ( USome( ( label, e_ ) ), Node( next ) ) =>
        val res1 = next.get( Variable ).map( _.generalizations( e.jump ) ).getOrElse( Vector.empty[T] )
        if ( label == Variable ) res1 else
          res1 ++ next.get( label ).map( _.generalizations( e_ ) ).getOrElse( Vector.empty[T] )
      case ( _, Leaf( elems ) ) => elems
      case _ =>
        throw new IllegalStateException
    }

  def unifiable( e: Term ): Vector[T] = unifiable( TermString( e ) )
  def unifiable( e: TermString ): Vector[T] =
    ( e.next, this ) match {
      case ( USome( ( label, e_ ) ), Node( next ) ) =>
        if ( label == Variable )
          jump().view.flatMap( _.unifiable( e_ ) ).toVector
        else
          next.get( Variable ).map( _.unifiable( e.jump ) ).getOrElse( Vector.empty[T] ) ++
            next.get( label ).map( _.unifiable( e_ ) ).getOrElse( Vector.empty[T] )
      case ( _, Leaf( elems ) ) => elems
      case _ =>
        throw new IllegalStateException
    }

}

object DiscrTree {
  trait Label { def arity: Int }
  case object Variable extends Label { def arity = 0 }

  case class Leaf[T]( elems: Vector[T] ) extends DiscrTree[T]
  case class Node[T]( next: Map[Label, DiscrTree[T]] ) extends DiscrTree[T]

  val empty: DiscrTree[Nothing] = Node( Map() )
  def apply[T](): DiscrTree[T] = empty

  val maxDepth = 100
}