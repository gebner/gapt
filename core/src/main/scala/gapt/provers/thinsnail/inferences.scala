package gapt.provers.thinsnail

import gapt.proofs._
import gapt.utils.{ UNone, UOption, USome }

import scala.collection.mutable

trait PreprocessingRule {
  def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls]
}

/**
 * An operation that looks at the given clause, and the set of worked off clauses;
 * it returns a set of new clauses, plus a set of clauses that should be discarded.
 */
trait InferenceRule extends PreprocessingRule {
  def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] )

  def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] = {
    val inferred = mutable.Set[Cls]()
    val deleted = mutable.Set[Cls]()

    for ( c <- newlyInferred ) {
      val ( i, d ) = apply( c, existing )
      inferred ++= i
      for ( ( dc, r ) <- d if r subsetOf dc.ass )
        deleted += dc
    }

    newlyInferred -- deleted ++ inferred
  }
}

trait RedundancyRule extends InferenceRule {
  def isRedundant( given: Cls, existing: IndexedClsSet ): Option[Set[Int]]
  def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    isRedundant( given, existing ) match {
      case Some( reason ) => ( Set(), Set( given -> reason ) )
      case None           => ( Set(), Set() )
    }
}

trait SimplificationRule extends InferenceRule {
  def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )]
  def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    simplify( given, existing ) match {
      case Some( ( simplified, reason ) ) => ( Set( simplified ), Set( given -> reason ) )
      case None                           => ( Set(), Set() )
    }
}

case class Pos( is: List[Int] = Nil ) extends AnyVal {
  def replace( in: Term, by: Term ): Term =
    ( is, in ) match {
      case ( Nil, _ ) => by
      case ( i :: is_, IsFn( f ) ) =>
        f.updated( i, Pos( is_ ).replace( f( i ), by ) )
    }

  def apply( t: Term ): UOption[Term] =
    ( is, t ) match {
      case ( Nil, _ ) => USome( t )
      case ( i :: is_, IsFn( f ) ) =>
        Pos( is_ )( f( i ) )
      case _ => UNone()
    }

  def +( i: Int ): Pos = Pos( i :: is )
}

object getFOPositions {
  def apply( exp: Term ): Map[Term, Seq[Pos]] = {
    val poss = mutable.Map[Term, Seq[Pos]]().withDefaultValue( Seq() )
    def walk( exp: Term, pos: Pos ): Unit = {
      poss( exp ) :+= pos
      exp match {
        case IsVar( _ ) | IsCon( _ ) =>
        case IsFn( f ) =>
          for ( i <- 0 until f.arity )
            walk( f( i ), pos + i )
      }
    }
    walk( exp, Pos() )
    poss.toMap
  }
}

case class UnitRwrLhsIndex( eqSym: FnSym ) extends Index[DiscrTree[( Term, Term, Boolean, Cls )]] {
  def empty: I = DiscrTree()
  private def choose[T]( ts: T* ): Seq[T] = ts
  def add( index: I, c: Cls ): I =
    index.insert( c.clause match {
      case Sequent( Seq(), Seq( Fn( `eqSym`, Seq( t, s ) ) ) ) =>
        for {
          ( t_, s_, ltr ) <- choose( ( t, s, true ), ( s, t, false ) )
          if !IsVar( t_ )
          if !c.state.termOrdering.lt( t_, s_ )
        } yield t_ -> ( t_, s_, ltr, c )
      case _ => Seq.empty
    } )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._4 ) )
}

object MaxPosLitIndex extends Index[DiscrTree[( Cls, SequentIndex )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for ( i <- c.maximal if i.isSuc if c.selected.isEmpty )
      yield c.clause( i ) -> ( c, i ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object SelectedLitIndex extends Index[DiscrTree[( Cls, SequentIndex )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- if ( c.selected.nonEmpty ) c.selected else c.maximal
      if i.isAnt
    } yield c.clause( i ) -> ( c, i ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

case class ForwardSuperpositionIndex( eqSym: FnSym ) extends Index[DiscrTree[( Cls, SequentIndex, Term, Term, Boolean )]] {
  def empty: I = DiscrTree()
  private def choose[T]( ts: T* ): Seq[T] = ts
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- c.maximal if i.isSuc if c.selected.isEmpty
      Fn( `eqSym`, Seq( t, s ) ) <- choose( c.clause( i ) )
      ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
      if !c.state.termOrdering.lt( t_, s_ )
    } yield t_ -> ( c, i, t_, s_, leftToRight ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object BackwardSuperpositionIndex extends Index[DiscrTree[( Cls, SequentIndex, Term, Seq[Pos] )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- if ( c.selected.nonEmpty ) c.selected else c.maximal
      a = c.clause( i )
      ( st, pos ) <- getFOPositions( a )
      if !IsVar( st )
    } yield st -> ( c, i, st, pos ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object clauseSubsumption {
  def apply( lctx1: LCtx, s1: Sequent[Term], lctx2: LCtx, s2: Sequent[Term] ): UOption[Subst] = {
    if ( s1.antecedent.size > s2.antecedent.size || s1.succedent.size > s2.succedent.size )
      return UNone()
    val subst = Subst()
    val off1 = subst.lctx.extend( lctx1 )
    val off2 = subst.lctx.extend( lctx2 )
    require( off1 == 0 )
    apply( subst, off1, s1, off2, s2 )
  }

  def apply(
    subst: Subst,
    off1:  Int, s1: Sequent[Term],
    off2: Int, s2: Sequent[Term] ): UOption[Subst] = {
    if ( s1.isEmpty ) return USome( subst )
    val chosenFrom = s1.indices.head
    for {
      chosenTo <- s2.indices if chosenTo sameSideAs chosenFrom
      newSubst = subst.clone()
      if newSubst.matching( off1, s1( chosenFrom ), off2, s2( chosenTo ) )
      subsumption <- apply(
        newSubst,
        off1, s1 delete chosenFrom,
        off2, s2 delete chosenTo )
    } return USome( subsumption )
    UNone()
  }
}

class StandardInferences( state: EscargotState, propositional: Boolean ) {
  import state.{ DerivedCls, SimpCls, termOrdering }
  val eqSym = state.eqFnSym

  object Eq {
    def apply( a: Term, b: Term ): Term = Fn( `eqSym`, choose( a, b ) )
    def unapply( t: Term ): Option[( Term, Term )] =
      t match {
        case Fn( `eqSym`, Seq( a, b ) ) => Some( ( a, b ) )
        case _                          => None
      }
  }

  def subsume( a: Cls, b: Cls ): Option[Subst] =
    if ( !a.ass.subsetOf( b.ass ) ) None else
      subsume( a.lctx, a.clause,
        b.lctx, b.clause )
  //    fastSubsumption( a.clause, b.clause, a.featureVec, b.featureVec, a.literalFeatureVecs, b.literalFeatureVecs )
  def subsume( lctxA: LCtx, a: Sequent[Term],
               lctxB: LCtx, b: Sequent[Term] ): Option[Subst] = {
    val lctx = LCtx()
    val offA = lctx.extend( lctxA )
    val offB = lctx.extend( lctxB )
    if ( propositional ) {
      if ( a isSubMultisetOf b ) Some( Subst( lctx ) )
      else None
    } else clauseSubsumption( lctxA, a, lctxB, b ).toOption
  }
  def unify(
    subst: Subst,
    offA:  Int, a: Term,
    offB: Int, b: Term ): Boolean =
    if ( propositional ) a == b
    else subst.unify( offA, a, offB, b )
  def matching( lctx: LCtx, a: Term, b: Term ): Boolean =
    matching( Subst( lctx ), 0, a, 0, b )
  def matching(
    subst: Subst,
    offA:  Int, a: Term,
    offB: Int, b: Term ): Boolean =
    if ( propositional ) a == b
    else subst.matching( offA, a, offB, b )

  //  object Clausification extends Clausifier(
  //    propositional,
  //    structural = true,
  //    bidirectionalDefs = false,
  //    cse = false,
  //    ctx = state.ctx,
  //    nameGen = state.nameGen ) with InferenceRule {
  //    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
  //      if ( given.clause.forall( _.isInstanceOf[Atom] ) ) ( Set(), Set() )
  //      else {
  //        expand( given.proof )
  //
  //        val consts = constants( cnf.map( _.conclusion.elements ).flatMap( constants( _ ) ).
  //          filter( _.name != "=" ) ).map( _.name )
  //        state.termOrdering match {
  //          case LPO( precedence, typeOrder ) =>
  //            val pc = precedence.takeWhile( state.ctx.constant( _ ).exists( arity( _ ) == 0 ) )
  //            state.termOrdering = LPO( pc ++ consts.diff( precedence.toSet ) ++ precedence.drop( pc.size ), typeOrder )
  //        }
  //
  //        val inferred = cnf.map( SimpCls( given, _ ) ).toSet
  //        cnf.clear()
  //        ( inferred, Set( given -> Set() ) )
  //      }
  //  }

  def isTaut( ass: Set[Int] ): Boolean =
    ass.intersect( ass.map( -_ ) ).nonEmpty

  object TautologyDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      if ( isTaut( given.ass ) || given.clause.isTaut ) Some( Set.empty ) else None
  }

  object EqualityResolution extends SimplificationRule {
    def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val simpd = given.clause.copy( antecedent =
        given.clause.antecedent.filterNot {
          case Eq( t, s ) => t == s
          case _          => false
        } )
      if ( simpd.size == given.clause.size ) None
      else Some( SimpCls(
        given,
        ResolutionProof.normalize(
          given.lctx,
          simpd,
          given.ass,
          choose( given.proof ) ) ) -> Set() )
    }
  }

  object ReflexivityDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      if ( given.clause.succedent exists {
        case Eq( t, t_ ) if t == t_ => true
        case _                      => false
      } ) Some( Set() ) else None
  }

  object OrderEquations extends SimplificationRule {
    def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      var didFlip = false
      val flipped = given.clause.map {
        case Eq( t, s ) if termOrdering.lt( s, t ) =>
          didFlip = true
          Eq( s, t )
        case x => x
      }
      if ( !didFlip ) {
        None
      } else {
        Some( SimpCls( given, ResolutionProof.normalize( given.lctx, flipped, given.ass, choose( given.proof ) ) ) -> Set() )
      }
    }
  }

  object ClauseFactoring extends SimplificationRule {
    def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val factored = given.clause.distinct
      if ( given.clause == factored ) None
      else Some( SimpCls( given, ResolutionProof.normalize( given.lctx, factored, given.ass, choose( given.proof ) ) ) -> Set() )
    }
  }

  object DuplicateDeletion extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] =
      newlyInferred.groupBy( _.clauseWithAssertions ).values.map( _.head ).toSet
  }

  object ReflModEqIndex extends Index[DiscrTree[( Term, Term, Boolean, Cls )]] {
    def empty: I = DiscrTree()
    private def choose[T]( ts: T* ): Seq[T] = ts
    def add( index: I, c: Cls ): I =
      index.insert( c.clause match {
        case Sequent( Seq(), Seq( Eq( t, s ) ) ) if matching( c.lctx, t, s )
          && matching( c.lctx, s, t ) =>
          for {
            ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
            if !termOrdering.lt( t_, s_ )
            if !IsVar( t_ )
          } yield t_ -> ( t_, s_, leftToRight, c )
        case _ => Seq.empty
      } )
    def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._4 ) )
  }

  object ReflModEqDeletion extends RedundancyRule {

    def canonize( lctx: LCtx, expr: Term, assertion: Set[Int], eqs: ReflModEqIndex.I ): Term = {
      val subst = Subst()
      require( subst.lctx.extend( lctx ) == 0 )
      def rewrite( t0: Term ): Term = {
        if ( IsVar( t0 ) ) return t0
        val t = t0 match {
          case IsFn( f ) => f.map( rewrite )
          case _         => t0
        }
        eqs.generalizations( t ).view.flatMap {
          case ( t_, s_, ltr, c1 ) =>
            val off = subst.lctx.extend( c1.lctx )
            if ( !matching( subst, off, t_, 0, t ) ) None
            else Some( rewrite( subst( off, s_ ) ) )
        }.headOption.getOrElse( t )
      }
      rewrite( expr )
    }

    def isRedundant( given: Cls, existing: IndexedClsSet ): Option[Set[Int]] = {
      val eqs = existing.getIndex( ReflModEqIndex )
      if ( !eqs.isEmpty && given.clause.succedent.exists {
        case Eq( t, s ) => canonize( given.lctx, t, given.ass, eqs ) == canonize( given.lctx, s, given.ass, eqs )
        case _          => false
      } ) Some( Set() ) else None
    }

  }

  object SubsumptionInterreduction extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] = {
      val interreduced = newlyInferred.to[mutable.Set]
      for {
        cls1 <- interreduced
        cls2 <- interreduced if cls1 != cls2
        if interreduced contains cls1
        if cls2.ass subsetOf cls1.ass
        _ <- subsume( cls2, cls1 )
      } interreduced -= cls1
      interreduced.toSet
    }
  }

  object ForwardSubsumption extends RedundancyRule {
    def isRedundant( given: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      existing.clauses.collectFirst { case e if subsume( e, given ).isDefined => e.ass }
  }

  object BackwardSubsumption extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
      ( Set(), existing.clauses.collect { case e if subsume( given, e ).isDefined => e -> given.ass } )
  }

  def choose[T]( ts: T* ): Seq[T] = ts

  object ForwardUnitRewriting extends SimplificationRule {
    def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val unitRwrLhs = existing.getIndex( UnitRwrLhsIndex( eqSym ) )
      if ( unitRwrLhs.isEmpty ) return None

      val subst = Subst()
      require( subst.lctx.extend( given.lctx ) == 0 )
      var didRewrite = true
      var reason = Set[Int]()
      val parents = mutable.Set[ResolutionProof]()
      def rewrite( t0: Term ): Term = {
        if ( IsVar( t0 ) ) return t0
        val t = t0 match {
          case IsFn( f ) => f.map( rewrite )
          case _         => t0
        }
        unitRwrLhs.generalizations( t ).view.flatMap {
          case ( t_, s_, ltr, c1 ) =>
            val off = subst.lctx.extend( c1.lctx )
            if ( !matching( subst, off, t_, 0, t ) ) None else {
              didRewrite = true
              reason = reason.union( c1.ass )
              parents += c1.proof
              Some( rewrite( subst( off, s_ ) ) )
            }
        }.headOption.getOrElse( t )
      }

      val simpd = given.clause.map( rewrite )
      if ( !didRewrite ) None else Some {
        SimpCls( given, ResolutionProof.normalize(
          given.lctx,
          simpd,
          given.ass.union( reason ),
          parents.toSeq ) ) -> reason
      }
    }
  }

  object BackwardUnitRewriting extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred = mutable.Set[Cls]()
      val deleted = mutable.Set[( Cls, Set[Int] )]()

      val givenSet = IndexedClsSet( state ).addIndex( UnitRwrLhsIndex( eqSym ) ) + given
      for ( e <- existing.clauses ) {
        val ( i, d ) = ForwardUnitRewriting( e, givenSet )
        inferred ++= i
        deleted ++= d
      }

      ( inferred.toSet, deleted.toSet )
    }
  }

  object OrderedResolution extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val givenSet = IndexedClsSet( state ).addIndex( SelectedLitIndex ).addIndex( MaxPosLitIndex ) + given
      val existingPlusGiven = existing + given
      val inferred1 =
        for {
          ( c1, i1 ) <- givenSet.getIndex( SelectedLitIndex ).elements
          ( c2, i2 ) <- existingPlusGiven.getIndex( MaxPosLitIndex ).unifiable( c1.clause( i1 ) )
          cn <- apply( c1, i1, c2, i2 )
        } yield cn
      val inferred2 =
        for {
          ( c2, i2 ) <- givenSet.getIndex( MaxPosLitIndex ).elements
          ( c1, i1 ) <- existing.getIndex( SelectedLitIndex ).unifiable( c2.clause( i2 ) )
          cn <- apply( c1, i1, c2, i2 )
        } yield cn

      ( Set() ++ inferred1 ++ inferred2, Set() )
    }

    // i1.isAnt i2.isSuc
    def apply( c1: Cls, i1: SequentIndex, c2: Cls, i2: SequentIndex ): Option[Cls] = {
      val mgu = Subst( LCtx() )
      val off1 = mgu.lctx.extend( c1.lctx )
      val off2 = mgu.lctx.extend( c2.lctx )
      val a1 = c1.clause( i1 )
      if ( !unify( mgu, off2, c2.clause( i2 ), off1, a1 ) ) return None
      if ( c1.selected.isEmpty &&
        c1.maximal.exists( i1_ => i1_ != i1 &&
          termOrdering.lt( mgu( off1, a1 ), mgu( off1, c1.clause( i1_ ) ) ) ) ) return None
      if ( c2.maximal.exists( i2_ => i2_ != i2 &&
        termOrdering.lt( mgu( off2, c2.clause( i2 ) ), mgu( off2, c2.clause( i2_ ) ) ) ) ) return None
      Some( DerivedCls( c1, c2,
        ResolutionProof.normalize(
          mgu.lctx,
          mgu( off1, c1.clause.delete( i1 ) ) ++ mgu( off2, c2.clause.delete( i2 ) ) distinct,
          c1.ass union c2.ass,
          Seq( c1.proof, c2.proof ) ) ) )
    }
  }

  object Superposition extends InferenceRule {
    def isReductive( atom: Term, i: SequentIndex, pos: Pos ): Boolean =
      ( atom, i, pos.is ) match {
        case ( Eq( t, s ), _: Suc, 1 :: _ ) => !termOrdering.lt( s, t )
        case ( Eq( t, s ), _: Suc, 0 :: _ ) => !termOrdering.lt( t, s )
        case _                              => true
      }

    def eligible( c: Cls, off: Int, c1: Sequent[Term], mgu: Subst, i: SequentIndex ): Boolean = {
      val a = mgu( off, c1( i ) )
      def maximalIn( is: Iterable[SequentIndex] ): Boolean =
        !is.exists( i_ => i_ != i && termOrdering.lt( a, mgu( off, c1( i_ ) ) ) )
      if ( c.selected.isEmpty ) maximalIn( c.maximal )
      else maximalIn( c.selected.view.filter( _.isAnt ) ) || maximalIn( c.selected.view.filter( _.isSuc ) )
    }

    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val givenSet = IndexedClsSet( state ).
        addIndex( ForwardSuperpositionIndex( eqSym ) ).
        addIndex( BackwardSuperpositionIndex ) +
        given
      val existingPlusGiven = existing + given
      val inferred1 =
        for {
          ( c1, i1, t1, s1, ltr ) <- givenSet.getIndex( ForwardSuperpositionIndex( eqSym ) ).elements
          ( c2, i2, _, pos2 ) <- existingPlusGiven.getIndex( BackwardSuperpositionIndex ).unifiable( t1 )
          cn <- apply( c1, i1, t1, s1, ltr, c2, i2, pos2 )
        } yield cn
      val inferred2 =
        for {
          ( c2, i2, st2, pos2 ) <- givenSet.getIndex( BackwardSuperpositionIndex ).elements
          ( c1, i1, t1, s1, ltr ) <- existing.getIndex( ForwardSuperpositionIndex( eqSym ) ).unifiable( st2 )
          cn <- apply( c1, i1, t1, s1, ltr, c2, i2, pos2 )
        } yield cn

      ( Set() ++ inferred1 ++ inferred2, Set() )
    }

    // i1.isSuc, c1.clause(i1) == Eq(_, _)
    def apply( c1: Cls, i1: SequentIndex, t_ : Term, s_ : Term, leftToRight: Boolean,
               c2: Cls, i2: SequentIndex, pos2: Seq[Pos] ): Option[Cls] = {
      val mgu = Subst()
      val off1 = mgu.lctx.extend( c1.lctx )
      val off2 = mgu.lctx.extend( c2.lctx )
      val a2 = c2.clause( i2 )
      val USome( st2 ) = pos2.head( a2 )
      if ( !unify( mgu, off1, t_, off2, st2 ) ) return None
      val t__ = mgu( off1, t_ )
      val s__ = mgu( off1, s_ )
      if ( termOrdering.lt( t__, s__ ) ) return None
      val pos2_ = pos2.filter( isReductive( mgu( off2, a2 ), i2, _ ) )
      if ( pos2_.isEmpty ) return None
      if ( !eligible( c2, off2, c2.clause, mgu, i2 ) ) return None
      val a2_ = pos2_.foldRight( mgu( off2, a2 ) )( _.replace( _, s__ ) )
      Some( DerivedCls( c1, c2,
        ResolutionProof.normalize(
          mgu.lctx,
          ( a2_ +: ( mgu( off1, c1.clause.delete( i1 ) ) ++ mgu( off2, c2.clause.delete( i2 ) ) ) ) distinct,
          c1.ass ++ c2.ass,
          Seq( c1.proof, c2.proof ) ) ) )
    }
  }

  object Factoring extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          i <- given.maximal; j <- given.maximal
          if i < j && i.sameSideAs( j )
          mgu = Subst( LCtx() )
          off = mgu.lctx.extend( given.lctx )
          if unify( mgu, off, given.clause( i ), off, given.clause( j ) )
        } yield DerivedCls( given, ResolutionProof.normalize(
          mgu.lctx,
          mgu( off, given.clause.delete( i ) ),
          given.ass,
          Seq( given.proof ) ) )
      ( inferred.toSet, Set() )
    }
  }

  object UnifyingEqualityResolution extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          i <- if ( given.selected.nonEmpty ) given.selected else given.maximal if i.isAnt
          Eq( t, s ) <- Some( given.clause( i ) )
          mgu = Subst()
          off = mgu.lctx.extend( given.lctx )
          if unify( mgu, off, t, off, s )
        } yield DerivedCls( given, ResolutionProof.normalize(
          mgu.lctx,
          mgu( off, given.clause.delete( i ) ),
          given.ass,
          Seq( given.proof ) ) )
      ( inferred.toSet, Set() )
    }
  }

  object VariableEqualityResolution extends SimplificationRule {
    def simp( p: ResolutionProof ): ResolutionProof =
      p.clause.antecedent.zipWithIndex.collectFirst {
        case ( Eq( x: Var, t ), i ) if !t.fvs.contains( x ) => ( x, t, i )
        case ( Eq( t, x: Var ), i ) if !t.fvs.contains( x ) => ( x, t, i )
      } match {
        case Some( ( x, t, i ) ) =>
          val subst = Subst()
          val off = subst.lctx.extend( p.lctx )
          require( subst.unify( off, x, off, t ) )
          simp( ResolutionProof.normalize(
            subst.lctx,
            subst( off, p.clause.delete( Ant( i ) ) ),
            p.assertions,
            Seq( p ) ) )
        case None => p
      }

    override def simplify( given: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val q = simp( given.proof )
      if ( q eq given.proof ) None else Some( SimpCls( given, q ) -> Set.empty )
    }
  }

  //  object AvatarSplitting extends InferenceRule {
  //
  //    var componentCache = mutable.Map[Formula, Atom]()
  //    def boxComponent( comp: HOLSequent ): AvatarNonGroundComp = {
  //      val definition @ All.Block( vs, _ ) = universalClosure( comp.toDisjunction )
  //      AvatarNonGroundComp(
  //        componentCache.getOrElseUpdate( definition, {
  //          val tvs = typeVariables( definition ).toList
  //          val c = Const( nameGen.freshWithIndex( "split" ), To, tvs )
  //          state.ctx += Definition( c, definition )
  //          c.asInstanceOf[Atom]
  //        } ), definition, vs )
  //    }
  //
  //    val componentAlreadyDefined = mutable.Set[Atom]()
  //    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
  //      val comps = AvatarSplit.getComponents( given.clause )
  //
  //      if ( comps.size >= 2 ) {
  //        val propComps = comps.filter( freeVariables( _ ).isEmpty ).map {
  //          case Sequent( Seq( a: Atom ), Seq() ) => AvatarGroundComp( a, Polarity.InAntecedent )
  //          case Sequent( Seq(), Seq( a: Atom ) ) => AvatarGroundComp( a, Polarity.InSuccedent )
  //        }
  //        val nonPropComps =
  //          for ( c <- comps if freeVariables( c ).nonEmpty )
  //            yield boxComponent( c )
  //
  //        val split = AvatarSplit( given.proof, nonPropComps ++ propComps )
  //        var inferred = Set( DerivedCls( given, split ) )
  //        for ( comp <- propComps; if !componentAlreadyDefined( comp.atom ) ) {
  //          componentAlreadyDefined += comp.atom
  //          for ( pol <- Polarity.values )
  //            inferred += DerivedCls( given, AvatarComponent( AvatarGroundComp( comp.atom, pol ) ) )
  //        }
  //        for ( comp <- nonPropComps if !componentAlreadyDefined( comp.atom ) ) {
  //          componentAlreadyDefined += comp.atom
  //          inferred += DerivedCls( given, AvatarComponent( comp ) )
  //        }
  //
  //        ( inferred, Set( given -> Set() ) )
  //      } else {
  //        ( Set(), Set() )
  //      }
  //    }
  //
  //  }

}