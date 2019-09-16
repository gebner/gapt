package gapt.provers.scan

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.fol.Numeral
import gapt.expr.formula.hol.instantiate
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.util.{ freeVariables, rename, syntacticMGU }
import gapt.logic.hol.simplify
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.{ Ant, HOLSequent, Sequent, SequentIndex, Suc }
import gapt.provers.escargot.Escargot
import gapt.utils.{ NameGenerator, verbose }

import scala.collection.mutable

case class ScanState(
    predicateVars: Set[Var],
    clauses:       Set[HOLSequent],
    solution:      Substitution,
    normalizer:    HOLSequent => Set[HOLSequent] = ScanState.defaultNormalizer ) {

  def removeClause( clause: HOLSequent ): ScanState =
    copy( clauses = clauses.filter( _ != clause ) )
  def addClause( clause: HOLSequent ): ScanState =
    copy( clauses = clauses + clause )
  def addClauses( newClauses: Iterable[HOLSequent] ): ScanState =
    copy( clauses = clauses ++ newClauses )

  def addConstraints( clause: HOLSequent, idx: SequentIndex ): ( ScanState, HOLSequent ) = {
    val newClause = ScanState.addConstraints( clause, idx )
    removeClause( clause ).addClause( newClause ) -> newClause
  }

  def predicateOccs: Iterable[( HOLSequent, SequentIndex )] =
    for {
      c <- clauses
      ( Apps( p, _ ), i ) <- c.zipWithIndex.elements
      if predicateVars.toSet.contains( p )
    } yield ( c, i )

  def addAllResolvents( a0: HOLSequent, i: SequentIndex ): ScanState = {
    val a = ScanState.addConstraints( a0, i )
    val f @ Apps( pred: Var, _ ) = a( i )
    val todo = clauses.diff( Set( a0 ) ).to[mutable.Queue]
    val resolvents = mutable.Set[HOLSequent]()
    while ( todo.nonEmpty ) {
      val given0 = todo.dequeue()
      val given = Substitution( rename( freeVariables( given0 ).diff( predicateVars ), freeVariables( a ) ) )( given0 )
      if ( given0 != a0 ) for {
        ( g @ Apps( `pred`, _ ), j ) <- given.zipWithIndex
        if i.polarity != j.polarity
        subst <- syntacticMGU( f, g, predicateVars )
        newClause = subst( a.delete( i ) ++ given.delete( j ) )
        newClauseN <- normalizer( newClause )
      } {
        todo += newClauseN
        resolvents += newClauseN
      }
    }
    addClauses( resolvents )
  }

  def interreduceAndEliminate( occ: ( HOLSequent, SequentIndex ) ): ScanState =
    interreduceAndEliminate( occ._1, occ._2 )
  def interreduceAndEliminate( clause: HOLSequent, idx: SequentIndex ): ScanState =
    addAllResolvents( clause, idx ).eliminateFullyInterreducedClause( clause, idx )

  def solve: ScanState =
    predicateOccs.headOption match {
      case Some( ( c, i ) ) => interreduceAndEliminate( c, i ).solve
      case None             => this
    }

  def addSubstitution( subst: Substitution ): ScanState =
    copy( solution = Substitution( subst.domain.map( p =>
      p -> BetaReduction.betaNormalize( subst( solution( p ) ) ) ) ) )
  def addSubstitution( predVar: Var, solutionForPreviousState: Expr ): ScanState =
    addSubstitution( Substitution( predVar -> solutionForPreviousState ) )

  def eliminateFullyInterreducedClause( clause0: HOLSequent, idx: SequentIndex ): ScanState = {
    val clause = ScanState.addConstraints( clause0, idx )
    val Apps( predVar: Var, args ) = clause( idx )
    require( predicateVars.contains( predVar ) )
    val extraFOVars = freeVariables( clause ).diff( predicateVars ).diff( freeVariables( args ) ).toSeq
    val newSol = idx match {
      case Ant( _ ) => clause( idx ) & All.Block( extraFOVars, clause.delete( idx ).toDisjunction )
      case Suc( _ ) => clause( idx ) | Ex.Block( extraFOVars, clause.delete( idx ).toNegConjunction )
    }
    require( freeVariables( newSol ).subsetOf( predicateVars union freeVariables( args ) ) )
    removeClause( clause0 ).addSubstitution( predVar, Abs( args.map( _.asInstanceOf[Var] ), newSol ) )
  }

  def removeSolvedPredicates: ScanState = {
    val solvedPredicates = predicateVars.diff( freeVariables( clauses.flattenS ) )
    copy( predicateVars = predicateVars.diff( solvedPredicates ) ).
      addSubstitution( Substitution( solvedPredicates.map { p =>
        val FunctionType( _, argTys ) = p.ty
        p -> Abs.Block( argTys.map( t => Var( "x", t ) ), Bottom() )
      } ) )
  }

  def toFormula: Formula =
    Ex.Block(
      predicateVars.toSeq,
      And( clauses.map( seq =>
        All.Block( freeVariables( seq ) diff predicateVars toSeq, seq.toImplication ) ) ) )

}

object ScanState {

  def defaultNormalizerStep( sequent: HOLSequent ): Option[Set[HOLSequent]] =
    sequent.zipWithIndex.antecedent.collectFirst {
      case ( Eq( x: Var, t ), i: Ant ) =>
        Set( Substitution( x -> t )( sequent.delete( i ) ) )
      case ( Eq( t, x: Var ), i: Ant ) =>
        Set( Substitution( x -> t )( sequent.delete( i ) ) )
      case ( Eq( x, x_ ), i: Ant ) if x == x_ =>
        Set( sequent.delete( i ) )
      case ( Eq( x, x_ ), i: Suc ) if x == x_ => Set[HOLSequent]()
    }

  def normalizerFixpoint( F: HOLSequent => Option[Set[HOLSequent]] ): HOLSequent => Set[HOLSequent] =
    seq => F( seq ) match {
      case Some( next ) => next.flatMap( normalizerFixpoint( F ) )
      case None         => Set( seq )
    }

  val defaultNormalizer: HOLSequent => Set[HOLSequent] =
    normalizerFixpoint( defaultNormalizerStep )

  def clausify( sequent: HOLSequent, predicateVars: Set[Var] ): Seq[HOLSequent] =
    sequent.zipWithIndex.elements.view.flatMap {
      case ( f, _ ) if predicateVars.intersect( freeVariables( f ) ).isEmpty => Some( Seq( sequent ) )
      case ( And( f, g ), i @ Ant( _ ) )                                     => Some( clausify( f +: g +: sequent.delete( i ), predicateVars ) )
      case ( Or( f, g ), i @ Suc( _ ) )                                      => Some( clausify( sequent.delete( i ) :+ f :+ g, predicateVars ) )
      case ( Imp( f, g ), i @ Suc( _ ) )                                     => Some( clausify( f +: sequent.delete( i ) :+ g, predicateVars ) )
      case ( Neg( f ), i @ Suc( _ ) )                                        => Some( clausify( f +: sequent.delete( i ), predicateVars ) )
      case ( Neg( f ), i @ Ant( _ ) )                                        => Some( clausify( sequent.delete( i ) :+ f, predicateVars ) )
      case ( f @ All( x0, _ ), i @ Suc( _ ) ) =>
        val x = rename( x0, freeVariables( sequent ) )
        Some( clausify( sequent.delete( i ) :+ instantiate( f, x ), predicateVars ) )
      case ( f @ Ex( x0, _ ), i @ Ant( _ ) ) =>
        val x = rename( x0, freeVariables( sequent ) )
        Some( clausify( instantiate( f, x ) +: sequent.delete( i ), predicateVars ) )
      case ( And( f, g ), i @ Suc( _ ) ) =>
        Some {
          clausify( sequent.delete( i ) :+ f, predicateVars ) ++
            clausify( sequent.delete( i ) :+ g, predicateVars )
        }
      case ( Or( f, g ), i @ Ant( _ ) ) =>
        Some {
          clausify( f +: sequent.delete( i ), predicateVars ) ++
            clausify( g +: sequent.delete( i ), predicateVars )
        }
      case ( Imp( f, g ), i @ Ant( _ ) ) =>
        Some {
          clausify( sequent.delete( i ) :+ f, predicateVars ) ++
            clausify( g +: sequent.delete( i ), predicateVars )
        }
      case ( Apps( pred, _ ), _ ) if predicateVars.toSet.contains( pred ) => Some( Seq( sequent ) )
    }.head

  def apply( bup: Formula ): ScanState = {
    val Ex.Block( predVars, matrix ) = bup
    ScanState( predVars.toSet, clausify( Sequent() :+ matrix, predVars.toSet ).toSet, Substitution() )
  }

  def addEq( clause: HOLSequent, eq: Formula ): HOLSequent =
    Sequent( clause.antecedent :+ eq, clause.succedent )

  def addConstraints( clause: HOLSequent, idx: SequentIndex ): HOLSequent = {
    val Apps( predVar, args ) = clause( idx )

    def replArg( i: Int, newArg: Var ): HOLSequent =
      addEq( clause, newArg === args( i ) ).
        updated( idx, predVar( args.updated( i, newArg ) ).asInstanceOf[Formula] )

    args.indexWhere( !_.isInstanceOf[Var] ) match {
      case -1 =>
      case i =>
        val newVar = Var( rename.awayFrom( freeVariables( clause ) ).fresh( "x" ), args( i ).ty )
        return addConstraints( replArg( i, newVar ), idx )
    }

    val dups = args.diff( args.distinct )
    if ( dups.nonEmpty ) {
      val i = args.indexOf( dups.head )
      val oldVar = args( i ).asInstanceOf[Var]
      val newVar = rename.awayFrom( freeVariables( clause ) ).fresh( oldVar )
      return addConstraints( replArg( i, newVar ), idx )
    }

    clause
  }

  private implicit class NameGenExtras( private val nameGen: NameGenerator ) extends AnyVal {
    def mkArgVarsFor( e: Expr ): Seq[Var] = {
      val FunctionType( _, argTys ) = e.ty
      argTys.map( ty => Var( nameGen.freshWithIndex( "x" ), ty ) )
    }
  }

}

private object demo extends scala.App {
  val bup @ Ex.Block( _, matrix ) =
    //    hof"""
    //             ?X (
    //               !x (A x -> X x) &
    //               !x (X a & X b -> B x) &
    //               !x (X a & X b -> B x)
    //             )
    //           """
    hof"""
             ?X (
               !x ((P(x)->P(s(x))) & (P(s(x))->P(s(s(x)))) -> X(x)) &
               (X(0) & X(s(s(0))) -> P(s(s(s(s(0))))))
             )
           """
  //    hof"""
  //       ?X (
  //         !x ((P(x)->P(s(x))) -> X(x)) &
  //         (X(0) -> P(0)->P(s(0)))
  //       )
  //     """
  println( bup )
  val s0 = ScanState( bup )
  println( s0 )
  println( s0.predicateOccs.toVector )
  val s1 = s0.solve
  val s2 = s1.removeSolvedPredicates
  println( s2 )

  val Abs.Block( _, sol: Formula ) = s2.solution( s0.predicateVars.head )
  println( simplify( sol ) )
  val f = BetaReduction.betaNormalize( s2.solution( matrix ) )
  println( simplify( f ) )
  println( "CNF:" )
  structuralCNF( Sequent() :+ simplify( f ) ).map( _.conclusion ).foreach( println )
}

private object indDemo extends scala.App {
  val bup @ Ex.Block( _, matrix ) =
    Substitution( hov"y" -> Numeral( 0 ) )( hof"""
             ?X (
               (P(0) -> X(0)) &
               !x ((P(x) -> P(s(x))) & X(x) -> X(s(x))) &
               (X(y) -> P(y))
             )
           """ )
  val s0 = ScanState( bup ).copy( normalizer = ScanState.normalizerFixpoint { seq =>
    ScanState.defaultNormalizerStep( seq ) orElse seq.zipWithIndex.antecedent.collectFirst {
      case ( Eq( App( Const( "s", _, _ ), a ), App( Const( "s", _, _ ), b ) ), i ) =>
        Set( seq.updated( i, a === b ) )
      case ( Eq( App( Const( "s", _, _ ), _ ), Const( "0", _, _ ) ), _ ) => Set()
      case ( Eq( Const( "0", _, _ ), App( Const( "s", _, _ ), _ ) ), _ ) => Set()
    }
  } )
  println( s0 )
  println( s0.predicateOccs.toVector )
  var s1 = s0
  while ( s1.predicateOccs.nonEmpty ) {
    s1.predicateOccs.find {
      case ( c, i ) => i.isSuc && !freeVariables( c( i ) ).subsetOf( s0.predicateVars )
    } match {
      case Some( occ ) =>
        s1 = s1.interreduceAndEliminate( occ )
      case None =>
        s1 = s1.interreduceAndEliminate( s1.predicateOccs.head )
    }
    println( s1.clauses )
  }
  val s2 = s1.removeSolvedPredicates
  println( s2 )

  val Abs.Block( _, sol: Formula ) = s2.solution( s0.predicateVars.head )
  println( simplify( sol ) )
  val f = BetaReduction.betaNormalize( s2.solution( matrix ) )
  println( simplify( f ) )
  println( "CNF:" )
  structuralCNF( Sequent() :+ simplify( f ) ).map( _.conclusion ).foreach( println )
  //  println( verbose( Escargot.getExpansionProof( hof"!x (s(x)!=0) & !x!y(s(x)=s(y)->x=y)" --> f ) ) )

  println( s2.clauses )
}
