package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.FOLClause
import at.logic.gapt.proofs.resolution.forgetfulPropParam
import at.logic.gapt.provers.smtlib.SmtlibSession
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.smtlib.SmtlibSession

case class BetterSolutionFinder(
    ns:                            Traversable[Int],
    numberOfConsequenceIterations: Int,
    validityChecker:               Prover,
    addImplications:               Boolean
) extends SolutionFinder {
  import SimpleInductionProof._

  def consequences( clauses: Set[FOLClause] ) =
    for (
      a <- clauses; b <- clauses;
      c <- forgetfulPropParam( Set( a, b ) ).flatten ++ resolvents( a, b )
    ) yield c.distinct.sortBy { _.hashCode }

  def resolvents( a: FOLClause, b: FOLClause ): Set[FOLClause] =
    for ( p <- a.succedent.toSet[FOLAtom]; n <- b.antecedent if p == n )
      yield a.filter( _ != p ) ++ b.filter( _ != n )

  override def findSolution( schematicSIP: SimpleInductionProof ): Option[FOLFormula] = {
    val zero = Utils.numeral( 0 )

    var clauses = ns.toSet[Int] flatMap { n =>
      val num = Utils.numeral( n )
      var clausesN = CNFp.toClauseList( canonicalSolution( schematicSIP, n ) ).map { _.distinct.sortBy { _.hashCode } }.toSet

      // generate consequences
      for ( _ <- 0 until numberOfConsequenceIterations )
        clausesN ++= consequences( clausesN )

      if ( addImplications )
        clausesN ++= ( for ( a <- clausesN; b <- clausesN; atom <- b.antecedent ) yield ( a :+ atom ).distinct.sortBy { _.hashCode } ) ++
          ( for ( a <- clausesN; b <- clausesN; atom <- b.succedent ) yield ( atom +: a ).distinct.sortBy { _.hashCode } )

      // generalize n to nu
      clausesN = clausesN.flatMap { clause =>
        val c = clause.toFormula
        val pos = c.find( num ).toSet
        pos.subsets() map { subset =>
          CNFp.toClauseList( subset.foldLeft( c ) {
            _.replace( _, nu ).asInstanceOf[FOLFormula]
          } ).head
        }
      }

      clausesN
    }

    def groundVars( e: LambdaExpression ): LambdaExpression = e match {
      case App( a, b )     => App( groundVars( a ), groundVars( b ) )
      case c: Const        => c
      case Var( name, ty ) => Const( name, ty )
    }
    def groundVarsF( f: HOLFormula ): HOLFormula = groundVars( f ).asInstanceOf[HOLFormula]

    def startSession( unsatCores: Boolean = false ) = {
      val session = validityChecker.startIncrementalSession()
      if ( unsatCores ) session.asInstanceOf[SmtlibSession].produceUnsatCores()
      session declareSymbolsIn ( ( schematicSIP.Gamma0 ++ schematicSIP.Gamma1 ++ schematicSIP.Gamma2 ).elements ++ schematicSIP.t ++ schematicSIP.u ++ Seq( FOLFunctionConst( "s", 1 ), FOLConst( "0" ) ) map groundVars )
      session
    }

    // filter out consequences from Gamma1
    clauses = for ( session <- startSession() ) yield {
      session assert groundVarsF( schematicSIP.Gamma1.toNegFormula )
      clauses.filter { clause =>
        session withScope {
          session assert -groundVars( clause.toFormula )
          session.checkSat()
        }
      }
    }

    // filter out non-consequences from Gamma0
    clauses = for ( session <- startSession() ) yield {
      session assert groundVarsF( schematicSIP.Gamma0.toNegFormula )
      clauses.filter { clause =>
        session withScope {
          session assert -groundVarsF( FOLSubstitution( nu -> zero, gamma -> beta )( clause.toFormula ) )
          !session.checkSat()
        }
      }
    }

    if ( false ) {
      clauses = CNFp.toClauseList( schematicSIP.Gamma1.toNegFormula ).asInstanceOf[List[FOLClause]].toSet ++ schematicSIP.t.toSet.flatMap { t: FOLTerm =>
        val subst = FOLSubstitution( gamma -> t )
        clauses.map( _.map( subst( _ ).asInstanceOf[FOLAtom] ) )
      }

      // generate consequences
      ( 0 until numberOfConsequenceIterations ) foreach { _ =>
        clauses ++= consequences( clauses )
      }

      val snu = FOLFunction( "s", nu )
      clauses = clauses.flatMap { clause =>
        val formula = clause.toFormula.asInstanceOf[FOLFormula]
        val positions = formula.find( snu )
        if ( positions.size == formula.find( nu ).size )
          Some( CNFp.toClauseList( positions.foldLeft( formula ) { case ( formula_, pos ) => formula_.replace( pos, nu ).asInstanceOf[FOLFormula] } ).head )
        else
          None
      }

      // filter out consequences from Gamma1
      clauses = clauses.filterNot { clause =>
        validityChecker.isValid( schematicSIP.Gamma1 :+ clause.toFormula )
      }

      clauses ++= ( for ( a <- clauses; b <- clauses ) yield ( a ++ b.swapped ).distinct )

      // filter out non-consequences from Gamma0
      clauses = clauses.filter { clause =>
        validityChecker.isValid( schematicSIP.Gamma0 :+ FOLSubstitution( nu -> zero, gamma -> beta )( clause.toFormula ) )
      }
    }

    val nu2snu = FOLSubstitution( nu -> FOLFunction( "s", nu ) )
    def findClauseDeps() = for ( session <- startSession( true ).asInstanceOf[SmtlibSession] ) yield {
      val clausesWithStepTermsT = clauses.zipWithIndex.map {
        case ( clause, i ) =>
          val label = s"c$i"
          session assert ( groundVarsF( And( schematicSIP.t.map { t => FOLSubstitution( gamma -> t )( clause.toFormula ) } ) ), label )
          label -> clause
      }.toMap
      session assert groundVarsF( schematicSIP.Gamma1.toNegFormula )
      clauses.flatMap { clause =>
        session withScope {
          session assert -groundVarsF( nu2snu( clause.toFormula ) )
          if ( session.checkSat() ) None
          else Some( clause -> ( session.getUnsatCore() map clausesWithStepTermsT toSet ) )
        }
      }.toMap
    }
    var clauseDeps = findClauseDeps()

    // filter out non-provable clauses
    while ( ( clauses diff clauseDeps.keySet ).nonEmpty ) {
      clauses = clauses intersect clauseDeps.keySet
      clauseDeps = findClauseDeps()
    }

    for ( session <- startSession( true ).asInstanceOf[SmtlibSession] ) yield {
      val clausesWithStepTermsU = clauses.zipWithIndex.map {
        case ( clause, i ) =>
          val label = s"c$i"
          session assert ( groundVarsF( And( schematicSIP.u.map { u => FOLSubstitution( nu -> alpha, gamma -> u )( clause.toFormula ) } ) ), label )
          label -> clause
      }.toMap
      session assert groundVarsF( schematicSIP.Gamma2.toNegFormula )

      if ( session.checkSat() ) None
      else Some {
        var necessaryClauses = session.getUnsatCore() map clausesWithStepTermsU toSet

        while ( !necessaryClauses.flatMap( clauseDeps( _ ) ).subsetOf( necessaryClauses ) )
          necessaryClauses ++= necessaryClauses.flatMap( clauseDeps( _ ) )

        val solution = And( necessaryClauses.map( _.toFormula.asInstanceOf[FOLFormula] ).toSeq )

        require( schematicSIP.solve( solution ).isSolved( validityChecker ) )

        solution
      }
    }
  }
}