package gapt.provers.thinsnail

import gapt.formats.tptp.{ TptpImporter, TptpProblemToResolution, resolutionToTptp }
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.provers.{ ResolutionProver, groundFreeVariables }
import gapt.provers.escargot.impl._
import gapt.utils.{ LogHandler, Maybe, USome }
import ammonite.ops._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.resolution.structuralCNF

object Escargot extends Escargot( splitting = true, equality = true, propositional = false ) {
  def lpoHeuristic( consts: Set[FnSym], eqSym: FnSym, boolSym: FnSym ): LPO = {
    val boolOnTermLevel = consts.exists( f => f.argTys.contains( USome( boolSym ) ) )

    val atoms = consts.filter( _.retTy == USome( boolSym ) )
    val functions = consts.filterNot( _.retTy == USome( boolSym ) )

    val precedence = functions.toSeq.sortBy( _.arity ) ++ Seq( eqSym ) ++
      ( atoms - eqSym ).toSeq.sortBy( _.arity )

    LPO( precedence.distinct )
  }

  def setupDefaults(
    state:     EscargotState,
    splitting: Boolean, equality: Boolean, propositional: Boolean ): Unit = {
    val standardInferences = new StandardInferences( state, propositional )
    import standardInferences._

    // Preprocessing rules
    state.preprocessingRules :+= DuplicateDeletion
    if ( equality ) {
      state.addIndex( UnitRwrLhsIndex( state.eqFnSym ) )
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
    //    if ( splitting ) state.inferences :+= AvatarSplitting
    state.addIndex( MaxPosLitIndex )
    state.addIndex( SelectedLitIndex )
    state.inferences :+= OrderedResolution
    state.inferences :+= Factoring
    if ( equality ) {
      state.addIndex( ForwardSuperpositionIndex( state.eqFnSym ) )
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
    val problem = TptpProblemToResolution( tptp )
    implicit val ctx = MutableContext.guess( problem )
    getResolutionProof( structuralCNF.onProofs( TptpProblemToResolution( tptp ) ) ) match {
      case Some( proof ) =>
        println( "% SZS status Unsatisfiable" )
        println( "% SZS output start CNFRefutation" )
        print( resolutionToTptp( proof ) )
        println( "% SZS output end CNFRefutation" )
      case None =>
        println( "% SZS status Satisfiable" )
    }
  }
}
object NonSplittingEscargot extends Escargot( splitting = false, equality = true, propositional = false )
object QfUfEscargot extends Escargot( splitting = true, propositional = true, equality = true )

class Escargot( splitting: Boolean, equality: Boolean, propositional: Boolean ) extends ResolutionProver {
  override def getResolutionProof( cnf: Traversable[HOLClause] )( implicit ctx0: Maybe[MutableContext] ): Option[gapt.proofs.resolution.ResolutionProof] = {
    import gapt.expr._
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( cnf ) )
    val hasEquality = equality && cnf.flatMap( _.elements ).exists { case Eq( _, _ ) => true; case _ => false }
    val isPropositional = propositional || cnf.flatMap { freeVariables( _ ) }.isEmpty

    val state = new EscargotState( ctx )
    Escargot.setupDefaults( state, splitting, hasEquality, isPropositional )
    //    state.nameGen = rename.awayFrom( ctx.constants.toSet ++ cnf.view.flatMap( constants( _ ) ) )
    val cnf_ = cnf.map( state.InputCls )
    state.termOrdering = Escargot.lpoHeuristic( state.termCtx.allFnSyms, state.eqFnSym, state.boolTy )
    state.newlyDerived ++= cnf_
    state.loop()
  }

  //  def getAtomicLKProof( sequent: HOLClause )( implicit ctx0: Maybe[Context] ): Option[LKProof] = {
  //    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( sequent ) ).newMutable
  //    withSection { section =>
  //      val seq = section.groundSequent( sequent )
  //      getResolutionProof( seq.map( _.asInstanceOf[Atom] ).
  //        map( Sequent() :+ _, _ +: Sequent() ).elements )( ctx ) map { resolution =>
  //        UnitResolutionToLKProof( resolution )
  //      }
  //    }
  //  }
}
