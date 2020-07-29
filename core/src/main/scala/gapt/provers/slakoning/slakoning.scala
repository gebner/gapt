package gapt.provers.slakoning

import gapt.expr._
import gapt.formats.tptp.{ TptpImporter, TptpProblemToResolution, resolutionToTptp, sequentProofToTptp }
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.provers.{ OneShotProver, ResolutionProver, groundFreeVariables }
import gapt.provers.escargot.impl._
import gapt.utils.{ LogHandler, Maybe }
import ammonite.ops._
import gapt.expr.formula.{ All, Atom, Eq, Formula, Imp, Neg }
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.hol.instantiate
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.arity
import gapt.expr.ty.baseTypes
import gapt.expr.util.{ constants, freeVariables, rename, syntacticMatching }
import gapt.logic.Polarity
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.context.Context
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk.rules.{ ForallRightRule, ImpRightRule, NegRightRule }
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule
import gapt.proofs.resolution.Input
import gapt.provers.escargot.LPO
import gapt.provers.viper.aip.axioms.Axiom

import scala.collection.mutable

class SlakoningState( _ctx: MutableContext ) extends EscargotState( _ctx ) {
  val assumptionConsts: mutable.Set[Const] = mutable.Set()
  override def selectable( a: Formula ): Boolean =
    a match {
      case Apps( p: Const, _ ) => !assumptionConsts.contains( p )
      case _                   => true
    }
  override def select( clause: HOLSequent, maximal: Vector[SequentIndex] ): Vector[SequentIndex] =
    ( maximal.filter( _.isAnt ) ++ clause.indicesWherePol( selectable, Polarity.Negative ) ).take( 1 )
}

class IntuitRuleInference( state: EscargotState, rules: Set[Rule], assumptionSks: Set[Const] ) extends InferenceRule {
  import state._
  //  import gapt.provers.sat.Sat4j._

  val proofs: mutable.Map[Formula, LKProof] = mutable.Map()

  //  def getProof(sequent: HOLSequent): LKProof = proofs.getOrElseUpdate(sequent, {
  //    ResolutionToExpansionProof
  //  })

  override def apply( given: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
    //    for {
    //      EndRule( atom ) <- rules
    //      if !solver.isSatisfiable( Seq( -intern( atom ) ) )
    //    } return Set( DerivedCls( given, Input( Sequent() ) ) ) -> Set()
    val sequent = given.clause ++ given.assertion
    if ( constants( sequent ).intersect( assumptionSks ).nonEmpty )
      return Set.empty[Cls] -> Set.empty
    val fvs = freeVariables( sequent )
    ( sequent.succedent.size match {
      case 0 =>
        rules.map( _.renameDisjoint( fvs ) ).flatMap {
          case ImpRule( lhs, _, concl ) =>
            ( for ( ( a, i ) <- sequent.zipWithIndex.elements; subst <- syntacticMatching( lhs, a ) )
              yield DerivedCls( given, Input( sequent.delete( i ) :+ subst( concl ) ) ) ) :+
              DerivedCls( given, Input( sequent :+ concl ) )
          case AllRule( _, concl ) =>
            Seq( state.DerivedCls( given, Input( sequent :+ concl ) ) )
          case NegRule( lhs, concl ) =>
            ( for ( ( a, i ) <- sequent.zipWithIndex.elements; subst <- syntacticMatching( lhs, a ) )
              yield DerivedCls( given, Input( sequent.delete( i ) :+ subst( concl ) ) ) ) :+
              DerivedCls( given, Input( sequent :+ concl ) )
          case _ => Set.empty
        }
      case 1 =>
        val fml = sequent( Suc( 0 ) )
        rules.map( _.renameDisjoint( fvs ) ).flatMap {
          case ImpRule( lhs, rhs, concl ) =>
            syntacticMatching( rhs, fml ) match {
              case Some( subst1 ) =>
                Set() ++ ( for {
                  ( a, i ) <- sequent.zipWithIndex.elements
                  subst <- syntacticMatching( lhs, a, subst1 )
                } yield DerivedCls( given, Input( sequent.delete( i ).delete( Suc( 0 ) ) :+ subst( concl ) ) ) ) +
                  DerivedCls( given, Input( sequent.delete( Suc( 0 ) ) :+ subst1( concl ) ) )
              case _ => Set.empty[Cls]
            }
          case AllRule( prem, concl ) =>
            syntacticMatching( prem, fml ).map( subst =>
              state.DerivedCls( given, Input( sequent.delete( Suc( 0 ) ) :+ subst( concl ) ) ) ).toSet
          case EndRule( `fml` ) if sequent.antecedent.isEmpty =>
            Set( DerivedCls( given, Input( Sequent() ) ) )
          case _ => Set.empty[Cls]
        }
      case _ => Set[Cls]()
    } ) -> Set()
  }
}

object Slakoning extends Slakoning( splitting = false, equality = true, propositional = false ) {
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
    state:     EscargotState,
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
    if ( splitting ) state.inferences :+= AvatarSplitting
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
    getLKProof( tptp.toSequent ) match {
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
  override def getLKProof( sequent: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[LKProof] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( sequent ) )
    if ( sequent.succedent.size == 1 ) {
      sequent( Suc( 0 ) ) match {
        case f @ All( x, _ ) =>
          val skC = ctx.addSkolemSym( f, reuse = false )
          return getLKProof( sequent.updated( Suc( 0 ), instantiate( f, skC ) ) ).map {
            case null                                => null // FIXME
            case p if p.conclusion.succedent.isEmpty => p
            case p if p.conclusion.succedent.size == 1 =>
              val y = rename( x, containedNames( p ) )
              ForallRightRule( TermReplacement( p, Map( skC -> y ) ), f, y )
          }
        case Imp( a, b ) =>
          return getLKProof( a +: sequent.updated( Suc( 0 ), b ) ).map {
            case null                                => null // FIXME
            case p if p.conclusion.succedent.isEmpty => p
            case p if p.conclusion.succedent.size == 1 =>
              ImpRightRule( p, a, b )
          }
        case Neg( a ) =>
          return getLKProof( a +: sequent.delete( Suc( 0 ) ) ).map {
            case null => null // FIXME
            case p if p.conclusion.antecedent.contains( a ) =>
              NegRightRule( p, a )
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
    Slakoning.setupDefaults( state, splitting, hasEquality, isPropositional )
    state.assumptionConsts ++= clausifier.assumptionConsts
    state.nameGen = nameGen
    state.termOrdering = Slakoning.lpoHeuristic( clausifier.cnf.map( _.conclusion ), ctx.constants, clausifier.assumptionConsts )
    state.newlyDerived ++= clausifier.cnf.map( state.InputCls )
    val intuitInferences = new IntuitRuleInference( state, clausifier.rules.toSet, clausifier.assumptionSks.toSet )
    for ( c <- state.newlyDerived ) EscargotLogger.info( c )
    EscargotLogger.info( ctx.get[Definitions] )
    for ( r <- clausifier.rules ) EscargotLogger.info( r )
    state.inferences :+= intuitInferences
    state.loop().map( _ => null )
  }

}
