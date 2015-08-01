package at.logic.gapt.provers.tactics

import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.{ HOLPosition, NaiveIncompleteMatchingAlgorithm, instantiate }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.defaultFormulaOccurrenceFactory
import at.logic.gapt.proofs.proofs.RuleTypeA
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.utils.ds.trees.LeafTree
import scalaz._

class ProofHole( val sequent: Sequent[( HOLFormula, String )] ) extends LeafTree[OccSequent](
  sequent.
    map( _._1 ).
    map( defaultFormulaOccurrenceFactory.createFormulaOccurrence( _, Seq() ) )
) with NullaryLKProof {
  sequent.elements.groupBy( _._2 ) foreach { g =>
    require( g._2.size <= 1, s"Duplicate label ${g._1}: ${g._2}" )
  }

  override def rule: RuleTypeA = InitialRuleType
}

case class ProofState( partialProof: LKProof ) {
  private val usedVars = partialProof.nodes().flatMap { case p: LKProof => variables( p.root.toHOLSequent ) }
  private val usedVarNames = usedVars map { _.sym.toString }
  private val freshVars = Stream.from( 1 ).map( i => s"x$i" ).filterNot( usedVarNames.contains )

  // FIXME: move into new Tree trait
  private def preOrder( p: LKProof ): Seq[LKProof] = p +: ( p match {
    case p: NullaryLKProof => Seq()
    case p: UnaryLKProof   => preOrder( p.uProof )
    case p: BinaryLKProof  => preOrder( p.uProof1 ) ++ preOrder( p.uProof2 )
  } )
  val holes = preOrder( partialProof ).collect { case hole: ProofHole => hole }

  def isFinished: Boolean = holes isEmpty

  def currentHole = holes headOption

  def plugHole( repl: LKProof ): ProofState = currentHole map { plugHole( _, repl ) } getOrElse this
  def plugHole( hole: ProofHole, repl: LKProof ): ProofState = {
    val repl_ = WeakeningContractionMacroRule( repl, hole.root.toHOLSequent )
    require( holes contains hole )
    require( repl_.root =^ hole.root )
    // FIXME: this only works because replaceSubproof believes a ProofHole is an axiom, and leaves it unchanged.
    ProofState( replaceSubproof( partialProof, hole, repl_ ) )
  }
}

object TacticsMonad {
  type Tactic[T] = ProofState => Option[( T, ProofState )]
  implicit val tacticMonadInstance = new Monad[Tactic] {
    override def point[A]( a: => A ): Tactic[A] = state => Some( ( a, state ) )
    override def bind[A, B]( fa: Tactic[A] )( f: ( A ) => Tactic[B] ): Tactic[B] = state =>
      fa( state ) flatMap { case ( res, newState ) => f( res )( newState ) }
  }

  def currentHole: Tactic[ProofHole] = state => state.currentHole.map( _ -> state )
  //  def plug(repl: LKProof): Tactic[Unit] = state => state.

  def refl: Tactic[Unit] = ???
  //    for ( hole <- currentHole ) yield ()
}

class TacticsProver( endSequent: HOLSequent ) {
  private var partialProof: LKProof = new ProofHole(
    endSequent.zipWithIndex.map {
      case ( a, Ant( i ) ) => a -> s"a$i"
      case ( b, Suc( i ) ) => b -> s"b$i"
    }
  )
  private val freshVars = Stream.from( 1 ).map( i => s"x$i" ).iterator

  // FIXME: move into new Tree trait
  private def preOrder( p: LKProof ): Seq[LKProof] = p +: ( p match {
    case p: NullaryLKProof => Seq()
    case p: UnaryLKProof   => preOrder( p.uProof )
    case p: BinaryLKProof  => preOrder( p.uProof1 ) ++ preOrder( p.uProof2 )
  } )
  private def holes = preOrder( partialProof ).collect { case hole: ProofHole => hole }

  private var currentHoleOption: Option[ProofHole] = holes headOption
  def currentHole = currentHoleOption.get

  def plugHole( repl: LKProof ): Unit = plugHole( currentHole, repl )
  def plugHole( hole: ProofHole, repl: LKProof ): Unit = {
    val repl_ = WeakeningContractionMacroRule( repl, hole.root.toHOLSequent )
    require( holes contains hole )
    require( repl_.root =^ hole.root )
    // FIXME: this only works because replaceSubproof believes a ProofHole is an axiom, and leaves it unchanged.
    partialProof = replaceSubproof( partialProof, hole, repl_ )
    currentHoleOption = holes headOption
  }

  def currentGoal = currentHole.sequent

  def constructProof: LKProof = CleanStructuralRules( partialProof )

  def printState = {
    def printFormula( f: ( HOLFormula, String ) ) = println( s"${f._2}: ${f._1}" )
    def printGoal( f: Sequent[( HOLFormula, String )] ) = {
      f.antecedent foreach printFormula
      println( ":-" )
      f.succedent foreach printFormula
    }
    holes.headOption match {
      case Some( current ) =>
        println( "Current goal:\n" )
        printGoal( current.sequent )
        if ( holes.size > 1 ) println( s"\n${holes.size - 1} further goals." )
      case None =>
        println( "No more goals left." )
    }
  }

  implicit def labelToCurrentSequentIndex( label: String ): SequentIndex =
    currentGoal.find( _._2 == label ).get

  def sorry = plugHole( Axiom( currentGoal.map( _._1 ) ) )

  def intro( idx: SequentIndex ) =
    ( idx, currentGoal( idx ) ) match {
      case ( Suc( _ ), ( main @ All( v, formula ), label ) ) =>
        val eigenVar = Var( freshVars.next(), v.exptype )
        val instForm = instantiate( main, eigenVar )
        val newHole = new ProofHole( currentGoal.updated( idx, instForm -> label ) )
        plugHole( ForallRightRule( newHole, instForm, main, eigenVar ) )
      case ( Ant( _ ), ( main @ Ex( v, formula ), label ) ) =>
        val eigenVar = Var( freshVars.next(), v.exptype )
        val instForm = instantiate( main, eigenVar )
        val newHole = new ProofHole( currentGoal.updated( idx, instForm -> label ) )
        plugHole( ExistsLeftRule( newHole, instForm, main, eigenVar ) )
    }

  def repeat( tactic: => Unit ) = try while ( true ) tactic catch { case _: Exception => () }

  def intros( idx: SequentIndex ): Unit = repeat { intro( idx ) }

  def intros: Unit = currentGoal.indices.foreach( intros( _ ) )

  def inst( idx: SequentIndex, termsList: Seq[LambdaExpression]* ): Unit =
    inst( idx, keep = false, termsList: _* )

  def inst( idx: SequentIndex, keep: Boolean, termsList: Seq[LambdaExpression]* ): Unit =
    ( idx, currentGoal.focus( idx ) ) match {
      case ( Ant( _ ), ( ( main, label ), rest ) ) =>
        val newHole = new ProofHole(
          ( if ( keep ) Seq( main -> s"${label}_" ) else Seq() ) ++:
            termsList.zipWithIndex.map {
              case ( terms, i ) =>
                instantiate( main, terms ) -> s"${label}_$i"
            } ++: rest
        )
        plugHole( termsList.foldLeft[LKProof]( newHole )( ForallLeftBlock( _, main, _ ) ) )
      case ( Suc( _ ), ( ( main, label ), rest ) ) =>
        val newHole = new ProofHole(
          ( if ( keep ) Seq( main -> s"${label}_" ) else Seq() ) ++:
            rest :++ termsList.zipWithIndex.map {
              case ( terms, i ) =>
                instantiate( main, terms ) -> s"${label}_$i"
            }
        )
        plugHole( termsList.foldLeft[LKProof]( newHole )( ExistsRightBlock( _, main, _ ) ) )
    }

  def elim( idx: SequentIndex ) =
    ( idx, currentGoal.focus( idx ) ) match {
      case ( Ant( _ ), ( ( main @ And( a, b ), label ), rest ) ) =>
        plugHole( AndLeftRule( new ProofHole( ( a -> s"${label}l" ) +: ( b -> s"${label}r" ) +: rest ), a, b ) )
      case ( Suc( _ ), ( ( main @ Or( a, b ), label ), rest ) ) =>
        plugHole( OrRightRule( new ProofHole( rest :+ ( a -> s"${label}l" ) :+ ( b -> s"${label}r" ) ), a, b ) )
    }

  def apply( a: SequentIndex, b: SequentIndex ) =
    ( a, b, currentGoal( a ), currentGoal( b ) ) match {
      case ( Ant( _ ), Suc( _ ), ( main @ All.Block( vars, aQf ), aLabel ), ( bQf, bLabel ) ) =>
        val matching = NaiveIncompleteMatchingAlgorithm.matchTerm( aQf, bQf ).get
        val ax = Axiom( bQf )
        val forallLeft = ForallLeftBlock( ax, main, vars.map( matching( _ ) ) )
        val weak = WeakeningMacroRule( forallLeft, currentGoal.map( _._1 ) )
        plugHole( weak )
    }

  def cases( idx: SequentIndex ) =
    ( idx, currentGoal( idx ) ) match {
      case ( Suc( _ ), ( main @ And( a, b ), label ) ) =>
        plugHole( AndRightRule(
          new ProofHole( currentGoal.updated( idx, a -> label ) ),
          new ProofHole( currentGoal.updated( idx, b -> label ) ),
          a, b
        ) )
    }

  def rewrite( eq: SequentIndex, in: SequentIndex, at: Option[HOLPosition] = None, flip: Boolean = false ): Unit = {
    val Ant( _ ) = eq
    val ( eqFormula @ All.Block( eqVars, qfEqFormula @ Eq( eqLhs, eqRhs ) ), _ ) = currentGoal( eq )
    val ( lhs, rhs ) = if ( flip ) ( eqRhs, eqLhs ) else ( eqLhs, eqRhs )
    val ( inFormula, inLabel ) = currentGoal( in )

    val pos = at.getOrElse {
      HOLPosition.getPositions( inFormula, cand => NaiveIncompleteMatchingAlgorithm.matchTerm( lhs, cand ).isDefined ).head
    }
    val Some( matching ) = NaiveIncompleteMatchingAlgorithm.matchTerm( lhs, inFormula( pos ) )

    val ax = Axiom( matching( qfEqFormula ) )
    val eqProof = ForallLeftBlock( ax, eqFormula, eqVars.map( matching( _ ) ) )

    val newInFormula = inFormula.replace( pos, matching( rhs ) )
    val newHole = new ProofHole( currentGoal.updated( in, newInFormula -> inLabel ) )
    in match {
      case Ant( _ ) =>
        plugHole( EquationLeftRule( eqProof, newHole, matching( qfEqFormula ), newInFormula, inFormula ) )
      case Suc( _ ) =>
        plugHole( EquationRightRule( eqProof, newHole, matching( qfEqFormula ), newInFormula, inFormula ) )
    }
  }

  def refl( idx: SequentIndex ): Unit =
    ( idx, currentGoal( idx ) ) match {
      case ( Suc( _ ), ( e @ Eq( x, x_ ), _ ) ) if x == x_ =>
        plugHole( Axiom( Sequent() :+ e ) )
    }

  def refl: Unit = refl( Suc( currentGoal.succedent.indexWhere {
    case ( Eq( x, x_ ), _ ) if x == x_ => true
    case _                             => false
  } ) )

  private val cutLabels = Stream.from( 0 ).map( i => s"c$i" ).iterator
  def cut( on: HOLFormula ) = {
    val cutLabel = cutLabels.next()
    val newHoleLeft = new ProofHole( currentGoal :+ ( on -> cutLabel ) )
    val newHoleRight = new ProofHole( ( on -> cutLabel ) +: currentGoal )
    plugHole( CutRule( newHoleLeft, newHoleRight, on ) )
  }

  def prover9 = plugHole( new Prover9Prover().getLKProof( currentGoal.map( _._1 ) ).get )

  def forget( idxs: SequentIndex* ) =
    plugHole( new ProofHole(
      currentGoal.
        zipWithIndex.
        filterNot( idxs contains _._2 ).
        map( _._1 )
    ) )
}
