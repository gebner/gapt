package at.logic.gapt.proofs.resolutionNew

import at.logic.gapt.algorithms.rewriting.{ TermReplacement, NameReplacement, RenameResproof }
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, FOLClause, Suc }
import at.logic.gapt.proofs.lk.subsumption.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolutionOld.robinson.RobinsonResolutionProof
import at.logic.gapt.provers.atp.SearchDerivation
import at.logic.gapt.provers.groundFreeVariables
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.utils.logging.Logger

import scala.collection.immutable.HashMap

/**
 *  Sometimes, we have a resolution refutation R of a set of clauses C
 *  and want a refutation R' of a set C' such that C implies C'.
 *
 *  This algorithm tries to obtain R' by trying to replace clauses c
 *  from C in R by derivations of C from C' in the following way:
 *
 *  - If c is in C' or c is an instance of reflexivity, do nothing.
 *  - If c is subsumed by some c' in C', derive c from c' by factoring.
 *  - Otherwise, try to derive c from C' by paramodulation and symmetry (prover9 often needs
 *    this, and the check is usually fast),
 *  - Otherwise, try to derive c from C' by propositional resolution.
 *
 *  If none of this works, we issue a warning and keep the clause c. If no warning is issued
 *  and the algorithm terminates, the result is the desired R'.
 *
 *  In general, if R is a derivation of a clause c, the result R' of fixDerivation(R)
 *  is a derivation of a subclause of c.
 */

object fixDerivation extends Logger {
  private def getSymmetryMap( to: Pair[Seq[FOLFormula], Seq[FOLFormula]], from: Pair[Seq[FOLFormula], Seq[FOLFormula]] ) = {
    var err = false
    def createMap( from: Seq[FOLFormula], to: Seq[FOLFormula] ) = {
      ( from zip from.indices ).foldLeft( HashMap[Int, Int]() ) {
        case ( map, ( from_f, from_i ) ) => {
          val to_i = to.indexWhere( to_f => ( from_f == to_f ) || ( ( from_f, to_f ) match {
            case ( Eq( from_l, from_r ), Eq( to_l, to_r ) ) if from_l == to_r && from_r == to_l => true
            case _ => false
          } ) )
          if ( to_i != -1 )
            map + ( ( from_i, to_i ) )
          else {
            err = true
            map
          }
        }
      }
    }
    val neg_map = createMap( from._1, to._1 )
    val pos_map = createMap( from._2, to._2 )
    if ( err )
      None
    else
      Some( ( neg_map, pos_map ) )
  }
  private def convertSequent( seq: FOLClause ) =
    ( seq.antecedent, seq.succedent )
  private def applySymm( p: ResolutionProof, f: FOLFormula, pos: Boolean ): ResolutionProof =
    {
      val ( left, right ) = f match {
        case Eq( l, r ) => ( l, r )
      }
      val newe = Eq( right, left )
      val refl = Eq( left, left )
      if ( pos ) {
        val irefl = ReflexivityClause( left )
        Paramodulation( p, p.conclusion indexOf f, irefl, Suc( 0 ), newe )
      } else {
        val init = TautologyClause( newe )
        val init2 = init
        val eq1 = Paramodulation( init, Suc( 0 ), p, p.conclusion indexOf f, refl )
        val eq2 = Paramodulation( init2, Suc( 0 ), eq1, eq1.conclusion indexOf refl, newe )
        Factor( eq2 )._1
      }
    }
  def tryDeriveBySymmetry( to: FOLClause, from: FOLClause ): Option[ResolutionProof] =
    getSymmetryMap( convertSequent( to ), convertSequent( from ) ) map {
      case ( neg_map, pos_map ) =>
        trace( "deriving " + to + " from " + from + " by symmetry" )
        val my_to = convertSequent( to )
        val my_from = convertSequent( from )
        val ( neg_map, pos_map ) = getSymmetryMap( my_to, my_from ).get
        val init: ResolutionProof = InputClause( from.map( _.asInstanceOf[FOLAtom] ) )

        var my_from_s = ( List[FOLFormula](), List[FOLFormula]() )
        var neg_map_s = HashMap[Int, Int]()
        var pos_map_s = HashMap[Int, Int]()

        // add symmetry derivations
        val s_neg = neg_map.keySet.foldLeft( init )( ( p, i ) => {
          val f = my_from._1( i )
          val to_i = neg_map( i )
          neg_map_s = neg_map_s + ( my_from_s._1.size -> to_i )
          f match {
            case Eq( _, _ ) if my_to._1( to_i ) != f => {
              my_from_s = ( my_from_s._1 :+ my_to._1( to_i ), my_from_s._2 )
              applySymm( p, f, false )
            }
            case _ => {
              my_from_s = ( my_from_s._1 :+ f, my_from_s._2 )
              p
            }
          }
        } )
        val s_pos = pos_map.keySet.foldLeft( s_neg )( ( p, i ) => {
          val f = my_from._2( i )
          val to_i = pos_map( i )
          pos_map_s = pos_map_s + ( my_from_s._2.size -> to_i )
          f match {
            case Eq( _, _ ) if my_to._2( to_i ) != f => {
              my_from_s = ( my_from_s._1, my_from_s._2 :+ my_to._2( to_i ) )
              applySymm( p, f, true )
            }
            case _ => {
              my_from_s = ( my_from_s._1, my_from_s._2 :+ f )
              p
            }
          }
        } )

        assert( to.isSubMultisetOf( s_pos.conclusion ) )

        Factor( s_pos )._1
    }

  private val subsumption_alg = StillmanSubsumptionAlgorithmFOL
  def tryDeriveByFactor( to: FOLClause, from: FOLClause ): Option[ResolutionProof] =
    subsumption_alg.subsumes_by( from, to ) map { s =>
      Factor( Instance( InputClause( from ), s ) )._1
    }

  def tryDeriveTrivial( to: FOLClause, from: Seq[FOLClause] ) = to match {
    case _ if from contains to => Some( InputClause( to ) )
    case FOLClause( Seq(), Seq( Eq( t, t_ ) ) ) if t == t_ => Some( ReflexivityClause( t ) )
    case FOLClause( Seq( a ), Seq( a_ ) ) if a == a_ => Some( TautologyClause( a ) )
    case _ => None
  }

  def tryDeriveViaSearchDerivation( to: FOLClause, from: Seq[FOLClause] ) = {
    val cls_sequent = FOLClause( to.negative.map( _.asInstanceOf[FOLFormula] ), to.positive.map( _.asInstanceOf[FOLFormula] ) )
    SearchDerivation( from, cls_sequent, true ) flatMap { d =>
      val ret = d.asInstanceOf[RobinsonResolutionProof]
      if ( ret.root.toHOLSequent != to ) {
        //        val ret_seq = FOLClause( ret.root.antecedent.map( _.formula ), ret.root.succedent.map( _.formula ) )
        // FIXME: replace InitialClause(ret_seq) by ret in the following proof
        // tryDeriveByFactor( to, ret_seq )
        None
      } else {
        Some( resOld2New( ret ) )
      }
    }
  }

  private val prover9 = new Prover9Prover
  def tryDeriveViaResolution( to: FOLClause, from: Seq[FOLClause] ) =
    if ( prover9 isInstalled )
      findDerivationViaResolution.applyNew( to, from.map { seq => FOLClause( seq.antecedent, seq.succedent ) }.toSet )
    else
      None

  private def findFirstSome[A, B]( seq: Seq[A] )( f: A => Option[B] ): Option[B] =
    seq.view.flatMap( f( _ ) ).headOption

  def apply( p: RobinsonResolutionProof, cs: Seq[HOLSequent] ): RobinsonResolutionProof =
    resNew2Old( applyNew( resOld2New( p ), cs.map( _.asInstanceOf[FOLClause] ) ) )

  def applyNew( p: ResolutionProof, cs: Seq[FOLClause] ): ResolutionProof =
    mapInputClauses( p ) { cls =>
      tryDeriveTrivial( cls, cs ).
        orElse( findFirstSome( cs )( tryDeriveByFactor( cls, _ ) ) ).
        orElse( findFirstSome( cs )( tryDeriveBySymmetry( cls, _ ) ) ).
        orElse( tryDeriveViaSearchDerivation( cls, cs ) ).
        orElse( tryDeriveViaResolution( cls, cs ) ).
        getOrElse {
          warn( "Could not derive " + cls + " from " + cs + " by symmetry or propositional resolution" )
          InputClause( cls )
        }
    }
}

object tautologifyInitialClauses {
  /**
   * Replace matching initial clauses by tautologies.
   *
   * If shouldTautologify is true for an initial clause Γ:-Δ, then it is replaced by the tautology Γ,Δ:-Γ,Δ.  The
   * resulting resolution proof has the same structure as the original proof, and will hence contain many duplicate
   * literals originating from the new initial clauses as the new literals are not factored away.
   */
  def apply( p: ResolutionProof, shouldTautologify: FOLClause => Boolean ): ResolutionProof =
    p match {
      case InputClause( clause ) if shouldTautologify( clause )             => InputClause( clause ++ clause.swapped )
      case InputClause( _ ) | ReflexivityClause( _ ) | TautologyClause( _ ) => p
      case Factor( p1, i1, i2 ) =>
        val newP1 = apply( p1, shouldTautologify )
        Factor( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).take( 2 ) )._1
      case Instance( p1, subst ) => Instance( apply( p1, shouldTautologify ), subst )
      case Resolution( p1, i1, p2, i2 ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        Resolution( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).head,
          newP2, newP2.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).filter( _ sameSideAs i2 ).head )
      case Paramodulation( p1, i1, p2, i2, pos, dir ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        Paramodulation( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).head,
          newP2, newP2.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).filter( _ sameSideAs i2 ).head, pos, dir )
    }
}

object containedVariables {
  import at.logic.gapt.proofs.resolutionNew
  def apply( p: resolutionNew.ResolutionProof ): Set[FOLVar] =
    p.subProofs.flatMap { subProof => freeVariables( subProof.conclusion ) }
}

object findDerivationViaResolution {
  def apply( a: FOLClause, bs: Set[FOLClause] ): Option[RobinsonResolutionProof] =
    applyNew( a, bs ) map { resNew2Old( _ ) }

  /**
   * Finds a resolution derivation of a clause from a set of clauses.
   *
   * The resulting resolution proof ends in a subclause of the specified clause a, and its initial clauses are either
   * from bs, tautologies, or reflexivity.
   *
   * @param a Consequence to prove.
   * @param bs Set of initial clauses for the resulting proof.
   * @return Resolution proof ending in a subclause of a, or None if prover9 couldn't prove the consequence.
   */
  def applyNew( a: FOLClause, bs: Set[FOLClause] ): Option[ResolutionProof] = {
    val grounding = groundFreeVariables.getGroundingMap(
      freeVariables( a ),
      ( a.formulas ++ bs.flatMap( _.formulas ) ).flatMap( constants( _ ) ).toSet
    )

    val groundingSubst = FOLSubstitution( grounding )
    val negatedClausesA = a.negative.map { f => FOLClause( Seq(), Seq( groundingSubst( f ) ) ) } ++
      a.positive.map { f => FOLClause( Seq( groundingSubst( f ) ), Seq() ) }

    new Prover9Prover().getRobinsonProof( bs.toList ++ negatedClausesA.toList ) map { refutation =>
      val tautologified = tautologifyInitialClauses( resOld2New( refutation ), negatedClausesA.toSet )

      val toUnusedVars = rename( grounding.map( _._1 ).toSet, containedVariables( tautologified ) )
      val nonOverbindingUnground = grounding.map { case ( v, c ) => c -> toUnusedVars( v ) }.toMap[FOLTerm, FOLTerm]
      val derivation = TermReplacement( tautologified, nonOverbindingUnground )
      val derivationInOrigVars = Instance( derivation, FOLSubstitution( toUnusedVars.map( _.swap ) ) )

      Factor( derivationInOrigVars )._1
    }
  }
}