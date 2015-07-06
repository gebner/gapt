package at.logic.gapt.grammars

import at.logic.gapt.expr.fol._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ toNNF, simplify, lcomp }
import at.logic.gapt.provers.maxsat.{ QMaxSAT, MaxSATSolver }
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

case class Rule( lhs: FOLTerm, rhs: FOLTerm ) {
  require( freeVariables( rhs ) subsetOf freeVariables( lhs ) )

  def apply( term: FOLTerm ): Option[FOLTerm] =
    FOLMatchingAlgorithm.matchTerms( lhs, term ).map( _( rhs ) )

  def apply( subst: FOLSubstitution ): Rule =
    Rule( subst( lhs ), subst( rhs ) )

  override def toString: String =
    s"$lhs -> $rhs"
}

case class RecursionScheme( rules: Set[Rule] ) {
  def language( from: FOLTerm ): Set[FOLTerm] =
    rules flatMap ( _( from ) ) match {
      case irreducible if irreducible.isEmpty => Set( from )
      case oneStepReductions                  => oneStepReductions flatMap language
    }

  override def toString: String = rules.toSeq.sortBy( _.toString ) mkString "\n"
}

object preOrderTraversal {
  def apply( term: FOLTerm ): Seq[FOLTerm] = term match {
    case FOLFunction( _, as ) => term +: ( as flatMap apply )
    case FOLVar( _ )          => Seq( term )
  }
}

object canonicalVars {
  def apply( term: FOLTerm ): FOLTerm =
    FOLSubstitution( preOrderTraversal( term ).
      collect { case v: FOLVar => v }.
      distinct.
      zipWithIndex.map { case ( v, i ) => v -> FOLVar( s"x$i" ) } )( term )
}

object TargetFilter {
  type Type = ( FOLTerm, FOLTerm ) => Option[Boolean]

  def default: Type = ( from: FOLTerm, to: FOLTerm ) =>
    FOLMatchingAlgorithm.matchTerms( to, from ) match {
      case Some( _ ) => Some( true )
      case _         => None
    }
}

class RecSchemGenLangFormula( val recursionScheme: RecursionScheme,
                              val targetFilter: TargetFilter.Type = TargetFilter.default ) {

  def ruleIncluded( rule: Rule ) = FOLAtom( s"${rule.lhs}->${rule.rhs}" )
  def derivable( from: FOLTerm, to: FOLTerm ) = FOLAtom( s"$from=>$to" )

  def reverseMatch( rule: Rule, against: FOLTerm ) =
    ( rule, against ) match {
      case ( Rule( _, FOLFunction( f, _ ) ), FOLFunction( f_, _ ) ) if f != f_ => None
      case _ =>
        val ( fvsRule, fvsAgainst ) = ( freeVariables( rule.lhs ), freeVariables( against ) )
        val rule_ = if ( fvsRule intersect fvsAgainst nonEmpty )
          rule( FOLSubstitution( rename( freeVariables( rule.lhs ), freeVariables( against ) ) ) )
        else
          rule
        FOLUnificationAlgorithm.unify( rule_.rhs, against ).headOption.map( _( rule_.lhs ) )
    }

  type Target = ( FOLTerm, FOLTerm )
  def apply( targets: Seq[Target] ): FOLFormula = {
    val edges = mutable.ArrayBuffer[( Target, Rule, Target )]()
    val goals = mutable.Set[Target]()

    val queue = mutable.Queue( targets: _* )
    val alreadyDone = mutable.Set[Target]()
    while ( queue nonEmpty ) {
      val target @ ( from, to ) = queue.dequeue()

      if ( !alreadyDone( target ) )
        recursionScheme.rules foreach { rule =>
          reverseMatch( rule, to ).map( canonicalVars( _ ) ).foreach { newTo =>
            targetFilter( from, newTo ) match {
              case Some( true ) =>
                goals += ( from -> newTo )
                edges += ( ( target, rule, from -> newTo ) )
              case Some( false ) => ()
              case None =>
                edges += ( ( target, rule, from -> newTo ) )
                queue enqueue ( from -> newTo )
            }
          }
        }

      alreadyDone += target
    }

    val reachable = mutable.Set[Target]( goals.toSeq: _* )
    var changed = true
    while ( changed ) {
      changed = false
      edges.foreach {
        case ( a, r, b ) =>
          if ( ( reachable contains b ) && !( reachable contains a ) ) {
            reachable += a
            changed = true
          }
      }
    }

    require( targets.toSet subsetOf reachable.result() )

    And( targets.map { case ( from, to ) => derivable( from, to ) } ++ ( reachable collect {
      case t @ ( from, to ) if !( goals contains t ) =>
        Imp( derivable( from, to ), Or(
          edges collect {
            case ( `t`, r, b ) if goals contains b                      => ruleIncluded( r )
            case ( `t`, r, b @ ( from_, to_ ) ) if reachable contains b => And( ruleIncluded( r ), derivable( from_, to_ ) )
          } ) )
    } ) )
  }
}

object minimizeRecursionScheme extends Logger {
  def apply( recSchem: RecursionScheme, targets: Seq[( FOLTerm, FOLTerm )],
             targetFilter: TargetFilter.Type = TargetFilter.default,
             solver: MaxSATSolver = new QMaxSAT ) = {
    val formula = new RecSchemGenLangFormula( recSchem, targetFilter )
    val hard = formula( targets )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> 1 }
    val interp = solver.solveWPM( List( hard ), soft toList ).get
    RecursionScheme( recSchem.rules.filter { rule => interp.interpret( formula.ruleIncluded( rule ) ) } )
  }
}

object SipRecSchem {

  val A = "A"
  val G = "G"

  type InstanceLanguage = ((Int, Int), Seq[FOLTerm])

  def targetFilter: TargetFilter.Type =
    ( from: FOLTerm, to: FOLTerm ) =>
      TargetFilter.default( from, to ).orElse {
        from match {
          case FOLFunction( A, List( x0, y0 ) ) =>
            to match {
              case FOLFunction( A, _ ) => Some( false )
              case FOLFunction( G, List( FOLFunction( f, _ ), _ ) ) if f != "s" && f != "0" => Some( false )
              case FOLFunction( G, List( x, _ ) ) if termSize( x ) <= termSize(x0) => None
              case FOLFunction( G, List( x, _ ) ) if termSize( x ) <= termSize(y0) => None
              case FOLFunction( G, _ ) => Some( false )
              case _ => None
            }
        }
      }

  def toSipGrammar( recSchem: RecursionScheme ) =
    SipGrammar( recSchem.rules.toSeq map {
      case Rule( FOLFunction( A, List( x: FOLVar ) ), FOLFunction( G, List( x_, u, x__ ) ) ) if x == x_ && x == x__ =>
        SipGrammar.gammaEnd -> FOLSubstitution( x -> SipGrammar.alpha )( u )
      case Rule( FOLFunction( A, List( x: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( x -> SipGrammar.alpha )( r )
      case Rule( FOLFunction( G, List( FOLFunction( "s", List( x: FOLVar ) ), y: FOLVar, z: FOLVar ) ), FOLFunction( G, List( x_, t, z_ ) ) ) if x == x_ && z == z_ =>
        SipGrammar.gamma -> FOLSubstitution( x -> SipGrammar.nu, y -> SipGrammar.gamma, z -> SipGrammar.alpha )( t )
      case Rule( FOLFunction( G, List( FOLFunction( "s", List( x: FOLVar ) ), y: FOLVar, z: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( x -> SipGrammar.nu, y -> SipGrammar.gamma, z -> SipGrammar.alpha )( r )
      case Rule( FOLFunction( G, List( FOLFunction( "0", List() ), y: FOLVar, z: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( y -> SipGrammar.beta, z -> SipGrammar.alpha )( r )
    } )

  def toTargets( instanceLanguages: Seq[InstanceLanguage] ) =
    instanceLanguages flatMap {
      case ( (x,y), l ) =>
        l map ( FOLFunction( A, Numeral( x ), Numeral(y) ) -> _ )
    }

  def normalForms( instanceLanguages: Seq[InstanceLanguage] ) = {
    val rules = Set.newBuilder[Rule]

    val Seq( x, y, z ) = Seq( "x", "y", "z" ).map( FOLVar( _ ) )

    val allTerms = instanceLanguages flatMap ( _._2 )
    val topLevelNFs = at.logic.gapt.grammars.normalForms( allTerms, Seq( x, y ) ).filter( !_.isInstanceOf[FOLVar] )
    val argumentNFs = at.logic.gapt.grammars.normalForms( FOLSubTerms( allTerms flatMap { case FOLFunction( _, as ) => as } ), Seq( x, y ) )

    for ( nf <- topLevelNFs ) {
      val fvs = freeVariables( nf )

      rules += Rule( FOLFunction( A, x, y ), nf )

      if (fvs.contains(y) && !fvs.contains(x))
        rules += Rule(FOLFunction(G, FOLFunction("0"), y), nf)
      if (fvs.contains(x) || fvs.contains(y))
        rules += Rule(FOLFunction(G, FOLFunction("s", x), y), nf)
    }

    for ( nf1 <- argumentNFs) {
      val fvs = freeVariables( nf1 )

      rules += Rule(FOLFunction(A, x, y), FOLFunction(G, x, nf1))
      rules += Rule(FOLFunction(A, x, y), FOLFunction(G, y, nf1))

      rules += Rule( FOLFunction( G, FOLFunction( "s", x ), y ), FOLFunction( G, x, nf1 ) )
    }

    RecursionScheme( rules.result() )
  }

}