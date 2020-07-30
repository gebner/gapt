package gapt.provers.slakoning

import gapt.expr._
import gapt.formats.tptp.{ TptpImporter, sequentProofToTptp }
import gapt.proofs._
import gapt.provers.{ OneShotProver, slakoning }
import gapt.provers.escargot.impl._
import gapt.utils.{ LogHandler, Maybe }
import ammonite.ops._
import gapt.expr.formula.{ All, And, Atom, Bottom, Eq, Ex, Formula, Iff, Imp, Neg, Or, Top }
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.hol.{ instantiate, universalClosure }
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.arity
import gapt.expr.ty.baseTypes
import gapt.expr.util.{ constants, freeVariables, rename, syntacticMGU, typeVariables }
import gapt.logic.Polarity
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Definition
import gapt.proofs.lk.LKProof
import gapt.proofs.nd._
import gapt.proofs.resolution.{ AvatarComponent, AvatarGroundComp, AvatarNonGroundComp, AvatarSplit, LocalResolutionRule, ResolutionProof, Subst }
import gapt.provers.escargot.LPO

import scala.collection.mutable

class SlakoningState( _ctx: MutableContext ) extends EscargotState( _ctx ) {
  val assumptionConsts: mutable.Set[Const] = mutable.Set()
  val rules: mutable.Set[Rule] = mutable.Set()
  override def selectable( a: Formula ): Boolean =
    a match {
      case Apps( p: Const, _ ) => !assumptionConsts.contains( p )
      case _                   => true
    }
  override def select( clause: HOLSequent, maximal: Vector[SequentIndex] ): Vector[SequentIndex] =
    ( maximal.filter( _.isAnt ) ++ clause.indicesWherePol( selectable, Polarity.Negative ) ).take( 1 )
}

case class PiR(
    subProof: ResolutionProof,
    i:        SequentIndex,
    rule:     PiRule ) extends LocalResolutionRule {
  require( i.isAnt )
  require( subProof.conclusion.succedent.size <= 1 )
  require( subProof.conclusion( i ) == rule.left )
  require( subProof.conclusion.succedent.isEmpty ||
    subProof.conclusion( Suc( 0 ) ) == rule.right )

  {
    val fvs = freeVariables( subProof.conclusion.delete( auxIndices.head ) )
    require( fvs.intersect( rule.eigenVars.toSet ).isEmpty )
  }

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices: Seq[Seq[SequentIndex]] = List( i +: subProof.conclusion.indicesSequent.succedent )
  override protected def mainFormulaSequent: Clause[Formula] = rule.concl
}

case class PiR2(
    subProof: ResolutionProof,
    rule:     PiRule ) extends LocalResolutionRule {
  require( subProof.conclusion.succedent.size <= 1 )
  require( subProof.conclusion.succedent.isEmpty ||
    subProof.conclusion( Suc( 0 ) ) == rule.right )

  {
    val fvs = freeVariables( subProof.conclusion.antecedent )
    require( fvs.intersect( rule.eigenVars.toSet ).isEmpty )
  }

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices: Seq[Seq[SequentIndex]] = List( subProof.conclusion.indicesSequent.succedent )
  override protected def mainFormulaSequent: Clause[Formula] = rule.concl
}

case class ExistsR( subProof: ResolutionProof, i: SequentIndex, rule: ExistsRule ) extends LocalResolutionRule {
  require( i.isAnt )
  require( subProof.conclusion( i ) == rule.premise )

  {
    val fvs = freeVariables( subProof.conclusion.delete( i ) )
    require( fvs.intersect( rule.eigenVars.toSet ).isEmpty )
  }

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices: Seq[Seq[SequentIndex]] = List( List( i ) )
  override protected def mainFormulaSequent: Clause[Formula] = rule.concl
}

case class OrR( subProof1: ResolutionProof, i: SequentIndex,
                subProof2: ResolutionProof, j: SequentIndex,
                rule: OrRule ) extends LocalResolutionRule {
  require( i.isAnt )
  require( j.isAnt )
  require( subProof1.conclusion( i ) == rule.left )
  require( subProof2.conclusion( j ) == rule.right )
  val tgt = ( subProof1.conclusion.succedent.view ++ subProof2.conclusion.succedent ).headOption
  for ( a <- subProof1.conclusion.succedent.view ++ subProof2.conclusion.succedent ) require( tgt.contains( a ) )
  override def immediateSubProofs = Seq( subProof1, subProof2 )
  override def auxIndices: Seq[Seq[SequentIndex]] =
    List(
      List( i ) ++ subProof1.conclusion.indicesSequent.succedent,
      List( j ) ++ subProof2.conclusion.indicesSequent.succedent )
  override protected def mainFormulaSequent: Clause[Formula] =
    rule.concl :++ tgt
}

case class EndR( subProof: ResolutionProof, rule: EndRule ) extends LocalResolutionRule {
  require( subProof.assertions.isEmpty )
  require( subProof.conclusion == ( Sequent() :+ rule.propAtom ) )

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( Suc( 0 ) ) )

  override protected def mainFormulaSequent: Clause[Formula] = Sequent()
}

object ContractionMacroRule {
  def apply( p: NDProof ): NDProof = {
    val dups = p.conclusion.antecedent diff p.conclusion.antecedent.distinct
    if ( dups.isEmpty ) p else apply( gapt.proofs.nd.ContractionRule( p, dups.head ) )
  }
}

case class resToND( defs: Normalizer ) {
  import gapt.proofs.nd._
  import gapt.proofs.resolution._

  def handlePi( left: Formula, eigenVars: List[Var], concl: Formula, p: NDProof ): NDProof = {
    def proveLeft( lefts: List[Formula], left: Formula ): NDProof =
      ( left: @unchecked ) match {
        case _ if lefts.contains( left ) =>
          LogicalAxiom( left )
        case Top()       => TopIntroRule
        case And( a, b ) => ContractionMacroRule( AndIntroRule( proveLeft( lefts, a ), proveLeft( lefts, b ) ) )
      }
    def go( lefts: List[Formula], evs: List[Var], concl: Formula ): NDProof = {
      val result = concl match {
        case All( x, b ) =>
          ForallIntroRule( go( lefts, evs.tail, Substitution( x -> evs.head )( b ) ), evs.head )
        case Imp( a, b ) =>
          val q1 = go( a :: lefts, evs, b )
          val q2 = if ( q1.conclusion.antecedent.contains( a ) ) q1 else WeakeningRule( q1, a )
          ImpIntroRule( q2, a )
        case Neg( a ) =>
          val q1 = go( a :: lefts, evs, Bottom() )
          val q2 = if ( q1.conclusion.antecedent.contains( a ) ) q1 else WeakeningRule( q1, a )
          NegIntroRule( q2, a )
        case _ =>
          val q1 = if ( !p.conclusion.antecedent.contains( left ) ) p else
            ImpElimRule( ImpIntroRule( p, left ), proveLeft( lefts, left ) )
          if ( q1.target == concl ) q1 else BottomElimRule( q1, concl )
      }
      require( result.target == concl )
      result
    }

    go( List(), eigenVars, concl )
  }

  def apply( res: ResolutionProof, subst: Substitution ): NDProof = {
    val result = res match {
      case Subst( q, subst2 ) =>
        apply( q, subst.compose( subst2 ) )
      case Resolution( p, i, q, j ) =>
        val p_ = apply( p, subst )
        if ( p_.conclusion.succedent.head == Bottom() ) p_ else {
          val f = defs.normalize( subst( q.conclusion( j ) ) )
          val q_ = apply( q, subst )
          q_.conclusion.indexOfOption( f, Polarity.InAntecedent ) match {
            case None => q_
            case Some( j_ ) =>
              ContractionMacroRule( ImpElimRule( ImpIntroRule( q_, j_ ), p_ ) )
          }
        }
      case Factor( p, i, j ) => apply( p, subst )
      case Taut( f ) =>
        LogicalAxiom( defs.normalize( subst( f ) ).asInstanceOf[Formula] )
      case AndR1( p, i ) => AndElim1Rule( apply( p, subst ) )
      case AndR2( p, i ) => AndElim2Rule( apply( p, subst ) )
      case Input( Sequent( Seq(), Seq( ant ) ) ) =>
        LogicalAxiom( defs.normalize( subst( ant ) ).asInstanceOf[Formula] )
      case DefIntro( p, _, _, _ ) => apply( p, subst )
      case ImpR( p, _ ) =>
        val p_ = apply( p, subst )
        val Imp( a, b ) = p_.conclusion.succedent.head
        ContractionMacroRule( ImpElimRule( p_, LogicalAxiom( a ) ) )
      case NegR( p, _ ) =>
        val p_ = apply( p, subst )
        val Neg( a ) = p_.conclusion.succedent.head
        ContractionMacroRule( NegElimRule( p_, LogicalAxiom( a ) ) )
      case AllR( p, i, t ) =>
        ForallElimRule( apply( p, subst ), subst( t ) )
      case slakoning.OrR( p, i, q, j, rule ) =>
        val p_ = apply( p, subst )
        val q_ = apply( q, subst )
        val a_ = defs.normalize( subst( p.conclusion( i ) ) )
        val b_ = defs.normalize( subst( q.conclusion( j ) ) )
        (
          p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ),
          q_.conclusion.indexOfOption( b_, Polarity.InAntecedent ) ) match {
            case ( None, _ ) => p_
            case ( _, None ) => q_
            case ( Some( i_ ), Some( j_ ) ) =>
              val p2 = if ( p_.target == Bottom() && p_.target != q_.target ) BottomElimRule( p_, q_.target ) else p_
              val q2 = if ( q_.target == Bottom() && q_.target != p_.target ) BottomElimRule( q_, p_.target ) else q_
              ContractionMacroRule( OrElimRule(
                LogicalAxiom( Or( p2.conclusion( i_ ), q2.conclusion( j_ ) ) ),
                p2, i_, q2, j_ ) )
          }
      case slakoning.PiR( p, i, PiRule( left, right, evs, _, Sequent( Seq(), Seq( concl ) ) ) ) =>
        val p_ = apply( p, Substitution() )
        val p1 = if ( p_.target != Bottom() ) p_ else
          BottomElimRule( p_, defs.normalize( right ).asInstanceOf[Formula] )
        val left_ = defs.normalize( left ).asInstanceOf[Formula]
        val concl_ = defs.normalize( concl ).asInstanceOf[Formula]
        ContractionMacroRule( subst( handlePi( left_, evs, concl_, p_ ) ) )
      case slakoning.PiR2( p, PiRule( left, right, evs, _, Sequent( Seq(), Seq( concl ) ) ) ) =>
        val p_ = apply( p, Substitution() )
        val p1 = if ( p_.target != Bottom() ) p_ else
          BottomElimRule( p_, defs.normalize( right ).asInstanceOf[Formula] )
        val left_ = defs.normalize( left ).asInstanceOf[Formula]
        val concl_ = defs.normalize( concl ).asInstanceOf[Formula]
        ContractionMacroRule( subst( handlePi( left_, evs, concl_, p_ ) ) )
      case slakoning.ExistsR( p, i, ExistsRule( premise, eigenVars, _, Sequent( Seq( concl ), Seq() ) ) ) =>
        val p_ = apply( p, Substitution() )
        val a_ = defs.normalize( p.conclusion( i ) )
        p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ) match {
          case Some( i_ ) =>
            def go( evs: List[Var], f: Formula ): NDProof = evs match {
              case ev :: evs =>
                ExistsElimRule( LogicalAxiom( f ), go( evs, instantiate( f, ev ) ), ev )
              case Nil =>
                p_
            }

            ContractionMacroRule( subst( go( eigenVars, defs.normalize( concl ).asInstanceOf[Formula] ) ) )
          case None => subst( p_ )
        }
      case AndL( p, i ) =>
        val p_ = apply( p, subst )
        val a_ @ And( l, r ) = defs.normalize( subst( p.conclusion( i ) ) )
        p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ) match {
          case None => p_
          case Some( i_ ) =>
            ContractionMacroRule( ImpElimRule( ImpIntroRule( p_, i_ ), AndIntroRule( LogicalAxiom( l ), LogicalAxiom( r ) ) ) )
        }
      case ExL( p, i, t ) =>
        val p_ = apply( p, subst )
        val a_ @ Ex( _, _ ) = defs.normalize( subst( p.conclusion( i ) ) ).asInstanceOf[Formula]
        if ( !p_.conclusion.antecedent.contains( a_ ) ) p_ else
          ContractionMacroRule( ImpElimRule(
            ImpIntroRule( p_, a_ ),
            ExistsIntroRule( LogicalAxiom( instantiate( a_, subst( t ) ) ), a_ ) ) )
      case OrL1( p, i ) =>
        val p_ = apply( p, subst )
        val a_ @ Or( l, r ) = defs.normalize( subst( p.conclusion( i ) ) )
        p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ) match {
          case None => p_
          case Some( i_ ) =>
            ImpElimRule( ImpIntroRule( p_, i_ ), OrIntro1Rule( LogicalAxiom( l ), r ) )
        }
      case OrL2( p, i ) =>
        val p_ = apply( p, subst )
        val a_ @ Or( l, r ) = defs.normalize( subst( p.conclusion( i ) ) )
        p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ) match {
          case None => p_
          case Some( i_ ) =>
            ImpElimRule( ImpIntroRule( p_, i_ ), OrIntro2Rule( LogicalAxiom( r ), l ) )
        }
      case EndR( p, _ ) => return apply( p, subst )
      case res @ Defn( _, _ ) =>
        val All.Block( xs, Iff( atom, _ ) ) = res.definitionFormula
        val p0 = LogicalAxiom( defs.normalize( atom ).asInstanceOf[Formula] )
        val p1 = ImpIntroRule( p0, Ant( 0 ) )
        val p2 = AndIntroRule( p1, p1 )
        xs.foldRight[NDProof]( p2 )( ( x, p_ ) => ForallIntroRule( p_, x, x ) )
      case Refl( t ) => EqualityIntroRule( subst( t ) )
      case Flip( p, i: Ant ) =>
        val p_ = apply( p, subst )
        val a_ @ Eq( l, r ) = defs.normalize( subst( p.conclusion( i ) ) )
        p_.conclusion.indexOfOption( a_, Polarity.InAntecedent ) match {
          case None => p_
          case Some( i_ ) =>
            ContractionMacroRule( ImpElimRule( ImpIntroRule( p_, i_ ), symm( r, l ) ) )
        }
      case Flip( p, i: Suc ) =>
        val p_ = apply( p, subst )
        if ( p_.target == Bottom() ) p_ else {
          val Eq( l, r ) = p_.target
          ImpElimRule( ImpIntroRule( symm( l, r ) ), p_ )
        }
      case res @ Paramod( p, i, ltr, q, j: Ant, ctx ) =>
        val p1 = Paramod( p, i, !ltr, Taut( res.rewrittenAuxFormula ), Suc( 0 ), ctx )
        apply( Resolution( p1, p1.occConnectors( 1 ).child( Suc( 0 ) ), q, j ), subst )
      case Paramod( p, i, ltr, q, j: Suc, ctx ) =>
        val p_ = apply( p, subst )
        if ( p_.target == Bottom() ) p_ else {
          val q_ = apply( q, subst )
          if ( q_.target == Bottom() ) q_ else {
            val Abs( x, a: Formula ) = defs.normalize( subst( ctx ) )
            ContractionMacroRule( EqualityElimRule( p_, q_, a, x ) )
          }
        }
    }

    ( result.target, res.conclusion.succedent.headOption.map( subst( _ ) ).map( defs.normalize( _ ) ) ) match {
      case ( Bottom(), _ )    =>
      case ( Bottom(), None ) =>
      case ( notBtm, None ) =>
        require( notBtm == Bottom() )
      case ( oldTgt, Some( newTgt ) ) =>
        require( oldTgt == newTgt )
    }

    result
  }

  def symm( l: Expr, r: Expr ): NDProof = {
    val x = rename( Var( "x", r.ty ), freeVariables( r ) )
    EqualityElimRule( LogicalAxiom( Eq( l, r ) ), EqualityIntroRule( r ), Eq( r, x ), x )
  }
}

class IntuitInferences( state: SlakoningState, propositional: Boolean ) extends StandardInferences( state, propositional ) {
  import state._

  object IntuitFactoring extends InferenceRule {
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          ( Apps( c: Const, _ ), i ) <- given.clause.zipWithIndex.elements
          ( Apps( d: Const, _ ), j ) <- given.clause.zipWithIndex.elements
          if i < j && i.sameSideAs( j )
          if assumptionConsts( c )
          if assumptionConsts( d )
          mgu <- unify( given.clause( i ), given.clause( j ) )
        } yield state.DerivedCls( given, Subst( given.proof, mgu ) )
      ( inferred.toSet, Set() )
    }
  }

  def isCEmptyCls( cls: Cls ): Boolean = isCEmptyCls( cls.clause )
  def isCEmptyCls( sequent: HOLSequent ): Boolean =
    sequent.forall {
      case Apps( c: Const, _ ) if assumptionConsts( c ) => true
      case _ => false
    }

  object IntuitRuleInference extends InferenceRule {

    override def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      //    for {
      //      EndRule( atom ) <- rules
      //      if !solver.isSatisfiable( Seq( -intern( atom ) ) )
      //    } return Set( DerivedCls( given, Input( Sequent() ) ) ) -> Set()
      if ( !isCEmptyCls( given ) ) return Set.empty[Cls] -> Set.empty
      val sequent = given.clause
      val fvs = freeVariables( sequent )
      rules.view.map( _.renameDisjoint( fvs ) ).flatMap {
        case rule @ PiRule( left, right, eigenVars, freeVars, concl ) =>
          syntacticMGU( sequent.succedent.map( ( right, _ ) ) ) match {
            case Some( subst0 ) =>
              val sequentWoSucc = sequent.copy( succedent = Vector() )
              val derived = ( subst0, sequentWoSucc, None ) +: ( for {
                ( a, i ) <- sequent.zipWithIndex.antecedent
                subst <- syntacticMGU( left, a, subst0 )
              } yield ( subst, sequentWoSucc.delete( i ), Some( i ) ) )
              derived.filter {
                case ( subst, der, i ) =>
                  val sevs = subst( eigenVars )
                  sevs.forall( _.isInstanceOf[Var] ) &&
                    sevs == sevs.distinct &&
                    freeVariables( der ).intersect( sevs.asInstanceOf[List[Var]].toSet ).isEmpty &&
                    freeVariables( subst( freeVars ) ).intersect( sevs.asInstanceOf[List[Var]].toSet ).isEmpty
              }.map {
                case ( subst, _, Some( i ) ) =>
                  DerivedCls( given, PiR( Subst( given.proof, subst ), i, subst( rule ) ) )
                case ( subst, _, None ) =>
                  DerivedCls( given, PiR2( Subst( given.proof, subst ), subst( rule ) ) )
              }.toSet
            case None =>
              Set.empty[Cls]
          }

        case rule @ ExistsRule( left, eigenVars, freeVars, concl ) =>
          ( for {
            ( a, i ) <- sequent.zipWithIndex.antecedent
            subst <- syntacticMGU( left, a )
            sevs = subst( eigenVars )
            if sevs.forall( _.isInstanceOf[Var] )
            if sevs == sevs.distinct
            if freeVariables( subst( sequent.delete( i ) ) ).intersect( sevs.asInstanceOf[List[Var]].toSet ).isEmpty
            if freeVariables( subst( freeVars ) ).intersect( sevs.asInstanceOf[List[Var]].toSet ).isEmpty
          } yield DerivedCls( given, ExistsR( Subst( given.proof, subst ), i, subst( rule ) ) ) ).toSet

        case rule @ OrRule( left, right, concl ) =>
          val result1 = for {
            ( a, i ) <- sequent.zipWithIndex.antecedent
            subst0 <- syntacticMGU( a, left ).toSet[Substitution]
            old0 <- existing.clauses
            if isCEmptyCls( old0 )
            old = Subst(
              old0.proof,
              Substitution( rename( freeVariables( old0.clause ), fvs ++ freeVariables( concl ) ) ) )
            ( b, j ) <- old.conclusion.zipWithIndex.antecedent
            subst <- syntacticMGU( b, right, subst0 )
            if ( Set() ++ subst( old.conclusion.succedent ) ++ subst( given.clause.succedent ) ).size <= 1
          } yield DerivedCls( given, OrR( Subst( given.proof, subst ), i, Subst( old, subst ), j, subst( rule ) ) )
          val result2 = for {
            ( a, i ) <- sequent.zipWithIndex.antecedent
            subst0 <- syntacticMGU( a, right ).toSet[Substitution]
            old0 <- existing.clauses
            if isCEmptyCls( old0 )
            old = Subst(
              old0.proof,
              Substitution( rename( freeVariables( old0.clause ), fvs ++ freeVariables( concl ) ) ) )
            ( b, j ) <- old.conclusion.zipWithIndex.antecedent
            subst <- syntacticMGU( b, left, subst0 )
            if ( Set() ++ subst( old.conclusion.succedent ) ++ subst( given.clause.succedent ) ).size <= 1
          } yield DerivedCls( given, OrR( Subst( old, subst ), j, Subst( given.proof, subst ), i, subst( rule ) ) )
          ( result1 ++ result2 ).toSet

        case rule @ EndRule( goal ) =>
          if ( sequent == ( Sequent() :+ goal ) && given.assertion.isEmpty )
            Set( DerivedCls( given, EndR( given.proof, rule ) ) )
          else
            Set()
      }.toSet -> Set()
    }
  }

  object Splitting extends InferenceRule {

    var componentCache = mutable.Map[Formula, Atom]()
    def boxComponent( comp: HOLSequent ): AvatarNonGroundComp = {
      val definition @ All.Block( vs, _ ) = universalClosure( comp.toDisjunction )
      AvatarNonGroundComp(
        componentCache.getOrElseUpdate( definition, {
          val tvs = typeVariables( definition ).toList
          val c = Const( nameGen.freshWithIndex( "split" ), To, tvs )
          state.ctx += Definition( c, definition )
          c.asInstanceOf[Atom]
        } ), definition, vs )
    }

    def getComponents( clause: HOLSequent ): List[HOLSequent] = {
      def findComp( c: HOLSequent ): HOLSequent = {
        val fvs = freeVariables( c )
        val c_ = clause.filter( freeVariables( _ ) intersect fvs nonEmpty )
        if ( c_ isSubsetOf c ) c else findComp( c ++ c_ distinct )
      }

      if ( clause.isEmpty ) {
        Nil
      } else {
        val c = findComp( clause.map( _ +: Clause(), Clause() :+ _ ).elements.head )
        c :: getComponents( clause diff c )
      }
    }

    val componentAlreadyDefined = mutable.Set[Atom]()
    def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val comps = getComponents( given.clause )

      if ( comps.size >= 2 ) {
        val propComps = comps.filter( freeVariables( _ ).isEmpty ).map {
          case Sequent( Seq( a: Atom ), Seq() ) => AvatarGroundComp( a, Polarity.InAntecedent )
          case Sequent( Seq(), Seq( a: Atom ) ) => AvatarGroundComp( a, Polarity.InSuccedent )
        }
        val nonPropComps =
          for ( c <- comps if freeVariables( c ).nonEmpty )
            yield boxComponent( c )

        val split = AvatarSplit( given.proof, nonPropComps ++ propComps )
        var inferred = Set( DerivedCls( given, split ) )
        for ( comp <- propComps; if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          for ( pol <- Polarity.values )
            inferred += DerivedCls( given, AvatarComponent( AvatarGroundComp( comp.atom, pol ) ) )
        }
        for ( comp <- nonPropComps if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          inferred += DerivedCls( given, AvatarComponent( comp ) )
        }

        ( inferred, Set( given -> Set() ) )
      } else {
        ( Set(), Set() )
      }
    }

  }

}

object Slakoning extends Slakoning( splitting = true, equality = true, propositional = false ) {
  def lpoHeuristic( cnf: Iterable[HOLSequent], extraConsts: Iterable[Const], assumptionConsts: Iterable[Const] ): LPO = {
    val consts = constants( cnf flatMap { _.elements } ) ++ extraConsts

    val boolOnTermLevel = consts exists { case Const( _, FunctionType( _, from ), _ ) => from contains To }
    val types = consts flatMap { c => baseTypes( c.ty ) }

    val atoms = for ( c <- consts; FunctionType( to, _ ) = c.ty if to == To ) yield c
    val eqs = atoms collect { case c @ EqC( _ ) => c }
    val functions = for ( c <- consts; FunctionType( to, _ ) = c.ty if to != To ) yield c

    val precedence = functions.toSeq.sortBy { arity( _ ) } ++ assumptionConsts.toSeq ++ eqs ++
      ( atoms diff eqs ).toSeq.sortBy { arity( _ ) }

    val namePrec = precedence.map( _.name ).distinct
    EscargotLogger.info( s"precedence: ${namePrec.mkString( ", " )}" )
    LPO( namePrec, ( _, t ) => !boolOnTermLevel && t == To )
  }

  def setupDefaults(
    state:     SlakoningState,
    splitting: Boolean, equality: Boolean, propositional: Boolean ) = {
    val standardInferences = new StandardInferences( state, propositional )
    import standardInferences._

    // Preprocessing rules
    state.preprocessingRules :+= DuplicateDeletion
    if ( equality ) {
      state.addIndex( UnitRwrLhsIndex )
      state.preprocessingRules :+= ForwardUnitRewriting
      state.preprocessingRules :+= VariableEqualityResolution
      state.preprocessingRules :+= OrderEquations
      state.preprocessingRules :+= EqualityResolution
      state.preprocessingRules :+= ReflexivityDeletion
    }
    state.preprocessingRules :+= TautologyDeletion
    state.preprocessingRules :+= ClauseFactoring
    state.preprocessingRules :+= DuplicateDeletion
    state.preprocessingRules :+= SubsumptionInterreduction
    state.preprocessingRules :+= ForwardSubsumption

    // Inference rules
    state.inferences :+= ForwardSubsumption
    if ( equality ) {
      state.addIndex( ReflModEqIndex )
      state.inferences :+= ReflModEqDeletion
    }
    state.inferences :+= BackwardSubsumption
    if ( equality ) {
      state.inferences :+= ForwardUnitRewriting
      state.inferences :+= BackwardUnitRewriting
    }
    //    if ( splitting ) state.inferences :+= slakoning.AvatarSplitting(state)
    state.addIndex( MaxPosLitIndex )
    state.addIndex( SelectedLitIndex )
    state.inferences :+= OrderedResolution
    state.inferences :+= Factoring
    if ( equality ) {
      state.addIndex( ForwardSuperpositionIndex )
      state.addIndex( BackwardSuperpositionIndex )
      state.inferences :+= Superposition
      state.inferences :+= UnifyingEqualityResolution
    }
  }

  def main( args: Array[String] ): Unit = {
    LogHandler.current.value = LogHandler.tstp

    val tptpInputFile = args.toSeq match {
      case Seq() =>
        println( "Usage: escargot [-v] tptp-problem.p" )
        sys.exit( 1 )
      case Seq( "-v", file ) =>
        LogHandler.verbosity.value = LogHandler.verbosity.value.increase( Seq( EscargotLogger ), 2 )
        file
      case Seq( file ) => file
    }

    val tptp = TptpImporter.loadWithIncludes( FilePath( tptpInputFile ) )
    implicit val ctx = MutableContext.guess( tptp.toSequent )
    getNDProof( tptp.toSequent ) match {
      case Some( proof ) =>
        println( "% SZS status Theorem" )
        println( "% SZS output start Proof" )
        print( sequentProofToTptp( proof ) )
        println( "% SZS output end Proof" )
      case None =>
        println( "% SZS status Unknown" )
        println( "% hopefully not a theorem" )
    }
  }
}
object NonSplittingSlakoning extends Slakoning( splitting = false, equality = true, propositional = false )
object QfUfSlakoning extends Slakoning( splitting = true, propositional = true, equality = true )

class Slakoning( splitting: Boolean, equality: Boolean, propositional: Boolean ) extends OneShotProver {
  def getNDProof( sequent: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[NDProof] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( sequent ) )
    if ( sequent.succedent.size == 1 ) {
      sequent( Suc( 0 ) ) match {
        case f @ All( x, _ ) =>
          val skC = ctx.addSkolemSym( f, reuse = false )
          return getNDProof( sequent.updated( Suc( 0 ), instantiate( f, skC ) ) ).map {
            case p if p.conclusion.succedent.head == Bottom() => p
            case p if p.conclusion.succedent.size == 1 =>
              val y = rename( x, containedNames( p ) )
              ForallIntroRule( TermReplacement( p, Map( skC -> y ) ), f, y )
          }
        case Imp( a, b ) =>
          return getNDProof( a +: sequent.updated( Suc( 0 ), b ) ).map {
            case p if !p.conclusion.antecedent.contains( a ) && p.conclusion.succedent.head == Bottom() =>
              p
            case p =>
              val p1 = if ( p.target == b ) p else BottomElimRule( p, b )
              val p2 = if ( p.conclusion.antecedent.contains( a ) ) p1 else WeakeningRule( p1, a )
              ImpIntroRule( p2, a )
          }
        case Neg( a ) =>
          return getNDProof( a +: sequent.delete( Suc( 0 ) ) ).map {
            case p if p.conclusion.antecedent.contains( a ) =>
              NegIntroRule( p, a )
            case p => p
          }
        case _ =>
      }
    }
    val hasEquality = equality && constants( sequent ).exists { case EqC( _ ) => true; case _ => false }
    val isPropositional = propositional
    val nameGen = ctx.newNameGenerator
    val clausifier = new Clausifier(
      propositional = isPropositional, structural = true, bidirectionalDefs = false,
      cse = false, ctx = ctx, nameGen = nameGen )
    sequent.antecedent.foreach( clausifier.expandAnt )
    sequent.succedent.foreach( clausifier.expandSuc )

    val state = new SlakoningState( ctx )
    state.assumptionConsts ++= clausifier.assumptionConsts
    state.rules ++= clausifier.rules
    Slakoning.setupDefaults( state, splitting, hasEquality, isPropositional )
    state.nameGen = nameGen
    state.termOrdering = Slakoning.lpoHeuristic( clausifier.cnf.map( _.conclusion ), ctx.constants, clausifier.assumptionConsts )
    EscargotLogger.info( state.assumptionConsts )
    state.newlyDerived ++= clausifier.cnf.map( state.InputCls )
    val intuitInferences = new IntuitInferences( state, propositional )
    for ( c <- state.newlyDerived ) EscargotLogger.info( c )
    EscargotLogger.info( ctx.get[Definitions] )
    for ( r <- state.rules ) EscargotLogger.info( r )
    state.inferences :+= intuitInferences.IntuitFactoring
    state.inferences :+= intuitInferences.IntuitRuleInference
    state.loop().map { proof =>
      val nd = resToND( ctx.normalizer )( proof, Substitution() )
      nd
    }
  }

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    getNDProof( seq ).map( nd => ??? ) // TODO: implement NDToLK
}
