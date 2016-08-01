package at.logic.gapt.proofs.drup

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution._

import scala.collection.mutable
import scalaz.{ Name, Need, Value }

sealed abstract class DrupProofLine extends Product {
  def clause: HOLClause
  override def toString = s"[${productPrefix.stripPrefix( "Drup" ).toLowerCase}] $clause"
}

/** Input clause in a DRUP proof. */
case class DrupInput( clause: HOLClause ) extends DrupProofLine
/**
 * Derived clause in a DRUP proof.
 *
 * The clause is not only required to be a consequence of the previous
 * clauses in the proof, but also RUP (a strictly stronger requirement):
 *
 * Given a set of clauses Γ and a clause C, then C has the property RUP with regard to Γ iff
 * Γ, ¬C can be refuted with only unit propagation.
 */
case class DrupDerive( clause: HOLClause ) extends DrupProofLine
/**
 * Forgets a clause in a DRUP proof.
 *
 * This inference is not necessary for completeness, it is mainly a
 * performance optimization since it speeds up the unit propagation in [[DrupDerive]].
 */
case class DrupForget( clause: HOLClause ) extends DrupProofLine

/**
 * DRUP proof.
 *
 * A DRUP proof consists of a sequence of clauses.  Each clause is either a [[DrupInput]], a [[DrupDerive]], or a [[DrupForget]].
 */
case class DrupProof( refutation: Seq[DrupProofLine] ) {
  override def toString = refutation.reverse.mkString( "\n" )
}
object DrupProof {
  def apply( cnf: Iterable[HOLClause], refutation: Seq[DrupProofLine] ): DrupProof =
    DrupProof( cnf.map( DrupInput ).toSeq ++ refutation )
}

object DrupToResolutionProof {

  // We operate on pairs of clauses and resolution proofs.
  //   - Proofs are computed only when needed (Name[_] does lazy evaluation)
  //   - The clauses can be smaller than the conclusion of the proof,
  //      e.g. we can have a pair (:- a, Taut(a))
  private type ResProofThunk = ( HOLSequent, Name[ResolutionProof] )

  // An atom together with a polarity (true iff it is in the succedent)
  private type Literal = ( HOLFormula, Boolean )

  private class ClauseIndex {

    var emptyClause: Option[ResProofThunk] = None
    // All unit clauses that we have found so far, indexed by their one literal
    val unitIndex = mutable.Map[Literal, ResProofThunk]()
    // All non-unit clauses that we have found so far, indexed by all of their literals
    val nonUnitIndex = mutable.Map[Literal, Map[HOLSequent, Name[ResolutionProof]]]().withDefaultValue( Map() )

    override def clone() = {
      val copy = new ClauseIndex
      copy.emptyClause = emptyClause
      copy.unitIndex ++= unitIndex
      copy.nonUnitIndex ++= nonUnitIndex
      copy
    }

    def negate( lit: Literal ) = ( lit._1, !lit._2 )
    def resolve( p: ResProofThunk, unit: ResProofThunk, lit: Literal ): ResProofThunk =
      if ( lit._2 ) ( p._1.removeFromSuccedent( lit._1 ), Need( Factor( Resolution( p._2.value, unit._2.value, lit._1 ) ) ) )
      else ( p._1.removeFromAntecedent( lit._1 ), Need( Factor( Resolution( unit._2.value, p._2.value, lit._1 ) ) ) )

    // Handle a new clause, and fully interreduce it with the clauses we have found so far
    def add( p: ResProofThunk ): Unit =
      if ( emptyClause.isDefined ) {
        // already found empty clause somewhere else
      } else if ( p._1.isEmpty ) {
        emptyClause = Some( p )
      } else {
        val lits = p._1.polarizedElements
        if ( lits.exists( unitIndex.contains ) ) {
          // subsumed by unit clause
        } else {
          lits.find( l => unitIndex.contains( negate( l ) ) ) match {
            case Some( lit ) =>
              val q = unitIndex( negate( lit ) )
              add( resolve( p, q, lit ) )
            case None =>
              if ( lits.size == 1 ) { // found unit clause
                val lit = lits.head
                unitIndex( lit ) = p

                // propagate
                val negLit = negate( lit )
                val qs = nonUnitIndex( negLit )
                nonUnitIndex.remove( negLit )
                for {
                  q <- qs.keys
                  lit_ <- q.polarizedElements.view.take( 2 )
                  if lit_ != negLit
                } nonUnitIndex( lit_ ) -= q

                // .map removes duplicate clauses
                qs.map( resolve( _, p, negLit ) ).foreach( add )
              } else {
                val watched = lits.view.take( 2 )
                for ( lit <- watched ) nonUnitIndex( lit ) += p
              }
          }
        }
      }

  }

  def apply( drup: DrupProof ): ResolutionProof = {
    val index = new ClauseIndex
    drup.refutation foreach {
      case DrupInput( clause ) =>
        index.add( clause -> Value( Input( clause ) ) )
      case DrupDerive( clause ) =>
        val derivationIndex = index.clone()
        for {
          ( a, i ) <- clause.zipWithIndex.elements
          negatedUnitClause = if ( i.isSuc ) Seq( a ) :- Seq() else Seq() :- Seq( a )
        } derivationIndex.add( negatedUnitClause -> Need( Taut( a ) ) )
        val derivation = derivationIndex.emptyClause.get._2.value
        index.add( derivation.conclusion -> Value( derivation ) )
      case DrupForget( clause ) =>
    }
    simplifyResolutionProof( index.emptyClause.get._2.value )
  }
}