package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.expansionTrees.{ toShallow, extractInstances }
import at.logic.gapt.proofs.resolution.{ HOLClause, Paramodulants, FOLClause }
import at.logic.gapt.provers.Prover

case class BetterSolutionFinder(
    n:                             Int,
    numberOfConsequenceIterations: Int,
    validityChecker:               Prover,
    prover:                        Prover
) extends SolutionFinder {
  import SimpleInductionProof._

  def consequences( clauses: Set[FOLClause] ) =
    for (
      a <- clauses; b <- clauses;
      c <- Paramodulants( a, b ) ++ resolvents( a, b )
    ) yield c

  def resolvents( a: FOLClause, b: FOLClause ): Set[FOLClause] =
    for ( p <- a.succedent.toSet[FOLAtom]; n <- b.antecedent if p == n )
      yield a.filter( _ != p ) ++ b.filter( _ != n )

  override def findSolution( schematicSIP: SimpleInductionProof ): Option[FOLFormula] = {
    val zero = Utils.numeral( 0 )
    val num = Utils.numeral( n )
    //    val Gamma0n = FOLSubstitution( alpha, Utils.numeral(n) )( schematicSIP.Gamma0 )
    //    val Gamma2n = FOLSubstitution( alpha, Utils.numeral(n) )( schematicSIP.Gamma2 )

    var clauses = CNFp.toClauseList( canonicalSolution( schematicSIP, n ) ).toSet

    // generate consequences
    ( 0 until numberOfConsequenceIterations ) foreach { _ =>
      clauses ++= consequences( clauses )
    }

    //    clauses ++= (for (a <- clauses; b <- clauses) yield (a ++ b.swap).distinct)

    // generalize n to nu
    clauses = clauses.flatMap { clause =>
      val c = clause.toFormula
      val pos = c.find( num ).toSet
      pos.subsets() map { subset =>
        CNFp.toClauseList( subset.foldLeft( c ) { _.replace( _, nu ) }.asInstanceOf[FOLFormula] ).head
      }
    }

    // filter out consequences from Gamma1
    clauses = clauses.filterNot { clause =>
      validityChecker.isValid( schematicSIP.Gamma1 :+ clause.toFormula )
    }

    // filter out non-consequences from Gamma0
    clauses = clauses.filter { clause =>
      validityChecker.isValid( schematicSIP.Gamma0 :+ FOLSubstitution( nu -> zero, gamma -> beta )( clause.toFormula ) )
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

      clauses ++= ( for ( a <- clauses; b <- clauses ) yield ( a ++ b.swap ).distinct )

      // filter out non-consequences from Gamma0
      clauses = clauses.filter { clause =>
        validityChecker.isValid( schematicSIP.Gamma0 :+ FOLSubstitution( nu -> zero, gamma -> beta )( clause.toFormula ) )
      }
    }

    val nu2snu = FOLSubstitution( nu -> FOLFunction( "s", nu ) )
    def findClauseDeps() = {
      val clausesWithStepTermsT = clauses.map { clause =>
        clause -> schematicSIP.t.map { t => FOLSubstitution( gamma -> t )( clause.toFormula ) }
      }
      clauses.flatMap { clause =>
        prover.getExpansionSequent(
          clausesWithStepTermsT.flatMap( _._2 ) ++: schematicSIP.Gamma1 :+ nu2snu( clause.toFormula )
        ) map { E =>
            clause -> extractInstances( E ).elements.flatMap { inst =>
              clausesWithStepTermsT.filter( _._2 contains inst ).map( _._1 )
            }.toSet
          }
      }.toMap
    }
    var clauseDeps = findClauseDeps()

    // filter out non-provable clauses
    while ( ( clauses diff clauseDeps.keySet ).nonEmpty ) {
      clauses = clauses intersect clauseDeps.keySet
      clauseDeps = findClauseDeps()
    }

    val clausesWithStepTermsU = clauses.map { clause =>
      clause -> schematicSIP.u.map { u => FOLSubstitution( nu -> alpha, gamma -> u )( clause.toFormula ) }
    }
    prover.getExpansionSequent(
      clausesWithStepTermsU.flatMap( _._2 ) ++: schematicSIP.Gamma2
    ) map { E =>
        val gamma2Deps = extractInstances( E ).elements.flatMap { inst =>
          clausesWithStepTermsU.filter( _._2 contains inst ).map( _._1 )
        }.toSet

        var necessaryClauses = gamma2Deps
        while ( !necessaryClauses.flatMap( clauseDeps( _ ) ).subsetOf( necessaryClauses ) )
          necessaryClauses ++= necessaryClauses.flatMap( clauseDeps( _ ) )

        val solution = And( necessaryClauses.map( _.toFormula.asInstanceOf[FOLFormula] ).toSeq )

        require( schematicSIP.solve( solution ).isSolved( prover ) )

        solution
      }
  }
}