package at.logic.gapt.grammars

import better.files._
import at.logic.gapt.expr._
import NSAP._
import at.logic.gapt.proofs.{ Context, HOLSequent }
import at.logic.gapt.proofs.expansion.{ InstanceTermEncoding, linearizeStrictPartialOrder }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.viper.{ SchematicInductiveProofFindingMethod, SchematicProofWithInduction }

import collection.mutable

/** Non-deterministic substitution automaton with progress condition. */
case class NSAP(
    states:      Seq[State],
    transitions: Seq[Transition]
) {
  for ( Transition( from, to, subst ) <- transitions ) {
    require( subst.domain == states( from ).vars )
    require( subst.range == states( to ).vars )

    val progressRange = freeVariables( subst( states( from ).progressVars ) )
    require( progressRange subsetOf states( to ).progressVars )
  }

  val transitionsFrom: Map[Int, Seq[Transition]] =
    transitions.groupBy( _.from ).withDefaultValue( Seq.empty )

  def accepts( subst: Substitution ): Boolean =
    accepts( 0, subst )

  def accepts( state: Int, subst: Substitution ): Boolean = {
    require( subst.domain == states( state ).vars )
    states( state ).isFinal || transitionsFrom( state ).exists {
      case Transition( _, to, transSubst ) =>
        matchSubsts( transSubst, subst ).
          exists( toSubst => accepts( to, toSubst ) )
    }
  }

  def generate( fuel: Substitution ): Set[Substitution] = generate( 0, fuel )
  def generate( state: Int, fuel: Substitution ): Set[Substitution] = {
    val State( vars, progressVars, isFinal ) = states( state )
    require( fuel.domain == progressVars )
    val fuelVars = fuel.domain.toList

    val next = for {
      trans <- transitionsFrom( state )
      fuel_ <- syntacticMatching( fuelVars.map( trans.subst( _ ) ) zip fuelVars.map( fuel( _ ) ) ).toSeq
      result <- generate( trans.to, fuel_ )
    } yield result compose trans.subst restrict vars

    if ( isFinal ) next.toSet + fuel else next.toSet
  }

  def merge( state1: Int, state2: Int ): NSAP = {
    require( states( state1 ).vars == states( state2 ).vars )
    require( states( state1 ).progressVars == states( state2 ).progressVars )
    NSAP(
      states.updated( state1, states( state1 ).copy( isFinal = states( state1 ).isFinal || states( state2 ).isFinal ) ),
      transitions.map {
        case Transition( from, to, subst ) =>
          Transition(
            if ( from == state2 ) state1 else from,
            if ( to == state2 ) state1 else to,
            subst
          )
      }
    ).gc
  }

  def gc: NSAP = {
    val reachable = states.indices.map( _ => false ).to[mutable.Seq]
    def markReachable( state: Int ): Unit =
      if ( !reachable( state ) ) {
        reachable( state ) = true
        transitionsFrom( state ).map( _.to ).foreach( markReachable )
      }
    markReachable( 0 )

    if ( reachable.forall( _ == true ) ) return this

    val newIndices = reachable.zipWithIndex.filter( _._1 ).map( _._2 ).zipWithIndex.toMap
    NSAP(
      states.zip( reachable ).filter( _._2 ).map( _._1 ),
      transitions.map { case Transition( from, to, subst ) => Transition( newIndices( from ), newIndices( to ), subst ) }.distinct
    )
  }

  def toGraphViz: String = {
    val dot = new StringBuilder
    dot ++= "digraph {\n"
    dot ++= "rankdir=LR;\n"

    for ( ( State( vs, pvs, f ), i ) <- states.zipWithIndex ) {
      val label = vs.toSeq.sortBy( _.name ).map( v => v.name + ( if ( pvs( v ) ) "*" else "" ) ).mkString( ", " ).replace( "\n", " " )
      val shape = if ( f ) "doublecircle" else "circle"
      dot ++= s"""$i [label="$i: $label", shape=$shape];"""
      dot ++= "\n"
    }

    for ( Transition( from, to, subst ) <- transitions ) {
      val label = for ( ( l, r ) <- subst.map.toSeq.sortBy( _._1.name ) if l != r )
        yield s"${l.toUntypedAsciiString} -> ${r.toUntypedAsciiString}"
      dot ++= s"""$from -> $to [label="${label.mkString( ", " ).replace( "\n", " " )}"];"""
      dot ++= "\n"
    }

    dot ++= "}\n"
    dot.result()
  }

  def toRecSchem: RecursionScheme = {
    val vars = states.map( _.vars.toSeq.sortBy( _.name ) )
    val nonTerminals = for ( ( vs, i ) <- vars.zipWithIndex ) yield HOLAtomConst( s"B$i", vs.map( _.exptype ): _* )( vs )
    val rules = for ( Transition( from, to, subst ) <- transitions )
      yield Rule( nonTerminals( to ), subst( nonTerminals( from ) ) )
    if ( states.count( _.isFinal ) == 1 ) {
      val axiom = nonTerminals( states.indexWhere( _.isFinal ) ).asInstanceOf[Const]
      RecursionScheme( axiom, rules.toSet )
    } else {
      val finalVars = states.filter( _.isFinal ).flatMap( _.vars ).distinct
      val axiom = Const( "A", FunctionType( To, finalVars.map( _.exptype ) ) )
      RecursionScheme( axiom, rules.toSet ++ states.zipWithIndex.filter( _._1.isFinal ).map( s => Rule( axiom( finalVars ), nonTerminals( s._2 ) ) ) )
    }
  }

  override def toString = {
    val out = new StringBuilder
    for ( ( s, i ) <- states.zipWithIndex ) out ++= s"$i\t$s\n"
    out ++= "\n"
    for ( t <- transitions ) out ++= s"$t\n"
    out.result()
  }
}

object NSAP {
  case class State(
      vars:         Set[Var],
      progressVars: Set[Var],
      isFinal:      Boolean
  ) {
    require( progressVars subsetOf vars )
    if ( isFinal ) require( vars.subsetOf( progressVars ) )
  }

  def matchSubsts( from: Substitution, to: Substitution ): Option[Substitution] = {
    require( from.domain == to.domain )
    syntacticMatching( from.domain.toList.map( v => from( v ) -> to( v ) ) )
  }

  case class Transition(
    from:  Int,
    to:    Int,
    subst: Substitution
  )
}

case class NsapSPWIFinder(
    paramTys:         Seq[Ty],
    instanceType:     Ty,
    grammarWeighting: Rule => Int,
    context:          Context
) extends SchematicInductiveProofFindingMethod {
  implicit def ctx = context

  val instV = Var( "y", instanceType )
  val paramVs = for ( ( t, i ) <- paramTys.zipWithIndex ) yield Var( s"x_$i", t )

  def insert( nsap: NSAP, state: Int, subst: Substitution ): NSAP = {
    require(
      subst.domain == nsap.states( state ).vars,
      s"Different variables:\n$subst\n${nsap.states( state )}"
    )

    if ( nsap.states( state ).isFinal ) return nsap

    for {
      trans <- nsap.transitionsFrom( state )
      mtch <- matchSubsts( trans.subst, subst )
    } return insert( nsap, trans.to, mtch )

    val vars = nsap.states( state ).vars.toSeq.sortBy( _.name )
    for {
      trans <- nsap.transitionsFrom( state )
      ( lgg, transSubstMap2, _ ) = leastGeneralGeneralization( vars.map( trans.subst.map ), vars.map( subst.map ) )
      if lgg.forall { !_.isInstanceOf[Var] }
    } {
      val transSubst1 = Substitution( vars zip lgg )
      val transSubst2 = Substitution( transSubstMap2 )
      require( transSubst1.range == transSubst2.domain )

      val newStateIdx = nsap.states.size
      val newState = NSAP.State(
        transSubst2.domain,
        freeVariables( transSubst1( nsap.states( state ).progressVars ) ),
        isFinal = false
      )

      val trans1 = NSAP.Transition( trans.from, newStateIdx, transSubst1 )
      val trans2 = NSAP.Transition( newStateIdx, trans.to, transSubst2 )

      val newNsap = NSAP(
        nsap.states :+ newState,
        nsap.transitions.filter( _ != trans ) :+ trans1 :+ trans2
      )
      return insert( newNsap, state, subst )
    }

    val newStateIdx = nsap.states.size
    val newState = NSAP.State( Set(), Set(), isFinal = true )
    val newTrans = NSAP.Transition( state, newStateIdx, subst )
    NSAP( nsap.states :+ newState, nsap.transitions :+ newTrans )
  }

  def checkProgress( nsap: NSAP ): Boolean = {
    val nonProgressGraph = nsap.transitions.collect {
      case Transition( from, to, subst ) if subst.restrict( nsap.states( from ).progressVars ).isIdentity =>
        from -> to
    }
    nonProgressGraph.forall( edge => edge._1 != edge._2 ) &&
      linearizeStrictPartialOrder( nsap.states.indices.toSet, nonProgressGraph.toSet ).isRight
  }

  def mergeStates( nsap: NSAP ): NSAP = {
    for {
      ( s1, i1 ) <- nsap.states.zipWithIndex
      ( s2, i2 ) <- nsap.states.zipWithIndex
      if i1 < i2
      if s1.vars == s2.vars
      if s1.progressVars == s2.progressVars
      newNSAP = nsap.merge( i1, i2 )
      if checkProgress( newNSAP )
    } return mergeStates( newNSAP )

    nsap
  }

  def mergeTransitions( nsap: NSAP ): NSAP = {
    for {
      i <- nsap.states.indices
      t1 <- nsap.transitionsFrom( i )
      t2 <- nsap.transitionsFrom( i )
      if t1 != t2
      mtch <- matchSubsts( t1.subst, t2.subst )
      newNSAP = nsap.copy( transitions = ( nsap.transitions diff Seq( t2 ) ) :+ NSAP.Transition( t1.to, t2.to, mtch ) )
      if checkProgress( newNSAP )
    } return mergeTransitions( newNSAP )

    nsap
  }

  def finalizeStates( nsap: NSAP ): NSAP = {
    val newFinalStates = for ( ( s, i ) <- nsap.states.zipWithIndex if !s.isFinal if s.vars == s.progressVars ) yield i
    NSAP(
      for ( ( s, i ) <- nsap.states.zipWithIndex ) yield s.copy( isFinal = s.isFinal || newFinalStates.contains( i ) ),
      nsap.transitions.filter { _.from != newFinalStates }
    )
  }

  def minimize( nsap: NSAP, langSubsts: Set[Substitution] ): NSAP = {
    for {
      t <- nsap.transitions.
        sortBy( x => x.subst.map.values.map( expressionSize( _ ) ).sum ).reverse
      newNSAP = nsap.copy( transitions = nsap.transitions diff Seq( t ) )
      if langSubsts.forall( newNSAP.accepts )
    } return minimize( newNSAP, langSubsts )

    nsap
  }

  def find( endSequent_ :HOLSequent, encoding: InstanceTermEncoding, context: Context,
            taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): SchematicProofWithInduction = {
    require( context == ctx )

    val initialState = NSAP.State( paramVs.toSet + instV, paramVs.toSet, isFinal = false )
    var nsap = NSAP( Seq( initialState ), Seq() )

    val grounding = Substitution( for ( v @ Var( n, t ) <- containedNames( taggedLanguage ) ) yield v -> Const( n, t ) )
    val langSubsts =
      for ( ( params, inst ) <- taggedLanguage )
        yield Substitution( ( paramVs zip grounding( params ) ) :+ ( instV -> grounding( inst ) ) )

    for ( subst <- langSubsts.toSeq.sortBy( s => s( paramVs ).map( expressionSize( _ ) ).sum ) ) {
      nsap = insert( nsap, 0, subst )
      nsap = mergeStates( nsap )
      nsap = mergeTransitions( nsap )
      nsap = finalizeStates( nsap ).gc
    }

    for ( subst <- langSubsts )
      require( nsap.accepts( 0, subst ) )

    nsap = mergeStates( nsap )
    nsap = minimize( nsap, langSubsts )
    nsap = nsap.gc

    file"nsap.dot" < nsap.toGraphViz

    //    println( nsap.toRecSchem )

    for ( subst <- langSubsts )
      require( nsap.accepts( 0, subst ) )

    new SchematicProofWithInduction {
      def lkProof( solution: Seq[LambdaExpression], prover: Prover ): LKProof = ???
      def paramVars: Seq[Var] = paramVs
      def generatedLanguage( inst: Seq[LambdaExpression] ): Set[HOLFormula] =
        nsap.generate( Substitution( paramVs zip inst ) ).
          map( _( instV ) ).
          map( encoding.decodeToSignedFormula )
      def solutionCondition: HOLFormula =
        throw new NotImplementedError( "Solution condition for NSAP unknown" )
      def endSequent: HOLSequent = endSequent_
      override def toString = nsap.toString
    }
  }
}
