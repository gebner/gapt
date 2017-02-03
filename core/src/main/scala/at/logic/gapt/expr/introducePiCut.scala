package at.logic.gapt.expr

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.Sequent

/**
 * Created by root on 26.01.17.
 */
class pi2SeHs(
    val reducedRepresentation:         Sequent[FOLFormula], // F[x\U_1] |- G[y\U_2]
    val universalEigenvariable:        FOLVar, // alpha
    val existentialEigenvariables:     List[FOLVar], // beta_1,...,beta_m
    val substitutionsForAlpha:         List[LambdaExpression], // r_1,...,r_m
    val substitutionsForBetaWithAlpha: List[LambdaExpression] // t_1(alpha),...,t_p(alpha)
) {

  require( existentialEigenvariables.length == substitutionsForAlpha.length )

  val multiplicityOfAlpha: Int = substitutionsForAlpha.length // m
  val multiplicityOfBeta: Int = substitutionsForBetaWithAlpha.length // p
  var balancedSolution: Option[FOLFormula] = None
  var noSolutionHasBeenFound: Boolean = true

  // (alpha,r_1),...,(alpha,r_m)
  //////////////////////////////
  def substitutionPairsAlpha(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsAlpha = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForAlpha.foreach( instance => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( universalEigenvariable, instance )
      substitutionPairsAlpha += buffer
    } )
    substitutionPairsAlpha.toSet
  }

  // (beta_i,t_1(alpha)),...,(beta_i,t_p(alpha))
  //////////////////////////////////////////////
  def substitutionPairsBetaI( index: Int ): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBetaI = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( existentialEigenvariables( index - 1 ), instanceB )
      substitutionPairsBetaI += buffer
    } )
    substitutionPairsBetaI.toSet
  }

  // (beta_1,t_1(alpha)),...,(beta_1,t_p(alpha)),
  //                     ...                    ,
  // (beta_m,t_1(alpha)),...,(beta_m,t_p(alpha))
  ///////////////////////////////////////////////
  def substitutionPairsBeta(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBeta = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    for ( index <- 1 to multiplicityOfAlpha ) {
      substitutionPairsBeta ++= substitutionPairsBetaI( multiplicityOfAlpha - index + 1 )
    }
    substitutionPairsBeta.toSet
  }

  // (alpha->r_1),...,(alpha->r_m)
  ////////////////////////////////
  def substitutionsAlpha(): List[Substitution] = {

    val substitutionsAlpha = scala.collection.mutable.ListBuffer[Substitution]()
    substitutionsForAlpha.foreach( instanceA => {
      substitutionsAlpha += Substitution( universalEigenvariable, instanceA )
    } )
    substitutionsAlpha.toList
  }

  // (beta_i->t_1(r_i)),...,(beta_i->t_p(r_i))
  ////////////////////////////////////////////
  def substitutionsBetaI( index: Int ): List[Substitution] = {

    val substitutionsBeta = scala.collection.mutable.ListBuffer[Substitution]()
    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) ) // (alpha->r_i)
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      substitutionsBeta += Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) )
    } )
    substitutionsBeta.toList
  }

  private def substituteRightSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.succedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = resultingSequent :+ formula
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = resultingSequent :+ subs( formula )
        } )
      }
    } )

    resultingSequent
  }

  private def substituteLeftSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.antecedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = formula +: resultingSequent
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = subs( formula ) +: resultingSequent
        } )
      }
    } )

    resultingSequent
  }

  // F[x\T_1] |- G[y\T_2]
  ///////////////////////
  def herbrandSequent(): Sequent[HOLFormula] = {

    var herbrandSequent: Sequent[HOLFormula] = Sequent() :++ reducedRepresentation.succedent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteRightSideOnce( herbrandSequent, multiplicityOfAlpha - indexM )
    }

    reducedRepresentation.antecedent.foreach( formula => {
      substitutionsForAlpha.foreach( instanceA => {
        val subs: Substitution = Substitution( universalEigenvariable, instanceA )
        herbrandSequent = subs( formula ) +: herbrandSequent
      } )
    } )

    val sequent: Sequent[HOLFormula] = herbrandSequent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteLeftSideOnce( herbrandSequent.antecedent ++: Sequent(), multiplicityOfAlpha - indexM ) :++ sequent.succedent
    }

    herbrandSequent
  }

  // The reduced representation as a formula
  //////////////////////////////////////////
  val reducedRepresentationToFormula: FOLFormula = reducedRepresentation.toImplication

  def literalsInTheDNTAsAndTheDNTAs: ( Set[FOLFormula], List[Sequent[FOLFormula]] ) = {

    val literals = scala.collection.mutable.Set[FOLFormula]()
    val DNTA = scala.collection.mutable.Set[Sequent[FOLFormula]]()

    CNFp( this.reducedRepresentationToFormula ).foreach( clause => if ( !clause.isTaut ) {
      var NTAClause: Sequent[FOLFormula] = clause
      for ( literal <- clause.succedent ) {
        NTAClause = Neg( literal ) +: NTAClause
      }
      NTAClause = NTAClause.antecedent ++: Sequent()
      val DNTABuffer = DNTA.toList
      var dontAdd: Boolean = false
      DNTABuffer.foreach( DNTAClause => {
        if ( !dontAdd ) {
          if ( NTAClause.isSubsetOf( DNTAClause ) ) {
            DNTA -= DNTAClause
          } else if ( DNTAClause.isSubsetOf( NTAClause ) ) {
            dontAdd = true
          }
        }
      } )
      if ( !dontAdd ) {
        DNTA += NTAClause // define for fol and hol sequents
      }
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )

    val DNTAList = DNTA.toList

    ( literals.toSet, DNTAList )
  }

}

class LeafIndex(
  val oneToMList: Set[Int],
  val oneToPList: Set[Int]
) {}

class LiteralWithIndexLists(
    val literal:       FOLFormula,
    val leafIndexList: List[LeafIndex],
    val numberOfDNTAs: Int
) {
  // require( numberOfDNTAs == leafIndexList.length )
}

class ClauseWithIndexLists(
    val literals: List[LiteralWithIndexLists]
) {

  // require( literals.tail.forall( _.numberOfDNTAs == literals.head.numberOfDNTAs ) )

  def numberOfDNTAs: Int = this.literals.head.numberOfDNTAs

  val leafIndexListClause: List[LeafIndex] = {

    var leafIndexListClauseBuffer: List[LeafIndex] = Nil
    for ( leafNumber <- 0 until this.literals.head.numberOfDNTAs ) {
      var leafIndexListClauseBufferM = this.literals.head.leafIndexList( leafNumber ).oneToMList
      var leafIndexListClauseBufferP = this.literals.head.leafIndexList( leafNumber ).oneToPList
      this.literals.tail.foreach( literal => {
        leafIndexListClauseBufferM = leafIndexListClauseBufferM.union( literal.leafIndexList( leafNumber ).oneToMList )
        leafIndexListClauseBufferP = leafIndexListClauseBufferP.intersect( literal.leafIndexList( leafNumber ).oneToPList )
      } )
      val leafIn = new LeafIndex( leafIndexListClauseBufferM, leafIndexListClauseBufferP )
      leafIndexListClauseBuffer = leafIndexListClauseBuffer :+ leafIn
    }
    leafIndexListClauseBuffer
  }

  val isAllowed: Boolean = {

    var bool: Boolean = false
    this.leafIndexListClause.foreach( leafNumber => {
      if ( leafNumber.oneToPList.nonEmpty ) {
        bool = true
      }
    } )
    bool
  }

  val isAllowedAtLeastAsSubformula: Boolean = {

    var bool: Boolean = true
    if ( this.isAllowed ) {
      this.leafIndexListClause.foreach( leafNumber => {
        if ( leafNumber.oneToMList.isEmpty ) {
          bool = false
        }
      } )
    }
    bool
  }

  def formula: FOLFormula = {

    var formulaBuffer: FOLFormula = literals.head.literal
    literals.tail.foreach( literal => formulaBuffer = And( formulaBuffer, literal.literal ) )
    formulaBuffer
  }

}

class ClausesWithIndexLists(
    val clauses: List[ClauseWithIndexLists]
) {

  private def leafIndexListClauses: List[LeafIndex] = {

    var emptyList: Boolean = false
    var leafIndexListClausesBuffer: List[LeafIndex] = Nil
    for ( leafNumber <- 0 until this.clauses.head.numberOfDNTAs; if !emptyList ) {
      var leafIndexListClausesBufferM = this.clauses.head.leafIndexListClause( leafNumber ).oneToMList
      var leafIndexListClausesBufferP = this.clauses.head.leafIndexListClause( leafNumber ).oneToPList
      this.clauses.tail.foreach( clause => {
        if ( !emptyList ) {
          leafIndexListClausesBufferM = leafIndexListClausesBufferM.intersect( clause.leafIndexListClause( leafNumber ).oneToMList )
          leafIndexListClausesBufferP = leafIndexListClausesBufferP.union( clause.leafIndexListClause( leafNumber ).oneToPList )
        }
        if ( leafIndexListClausesBufferM.isEmpty ) {
          emptyList = true
        }
      } )
      val leafIn = new LeafIndex( leafIndexListClausesBufferM, leafIndexListClausesBufferP )
      leafIndexListClausesBuffer = leafIndexListClausesBuffer :+ leafIn
    }
    leafIndexListClausesBuffer
  }

  def isSolution: Boolean = {

    var bool: Boolean = true
    this.leafIndexListClauses.forall( leafNumber => {
      if ( leafNumber.oneToPList.isEmpty ) {
        bool = false
      } else if ( leafNumber.oneToMList.isEmpty ) {
        bool = false
      }
      bool
    } )
  }

  def formula: FOLFormula = {

    var formulaBuffer: FOLFormula = this.clauses.head.formula
    this.clauses.tail.foreach( clause => formulaBuffer = Or( formulaBuffer, clause.formula ) )
    formulaBuffer
  }

}

object introducePi2Cut {

  def apply(
    seHs:                      pi2SeHs,
    nameOfExistentialVariable: FOLVar  = fov"yCut",
    nameOfUniversalVariable:   FOLVar  = fov"xCut"
  ): Option[FOLFormula] = {

    val nameOfExistentialVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfExistentialVariable )
    val nameOfUniversalVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfUniversalVariable )

    /*
    val literals = scala.collection.mutable.Set[FOLFormula]()
    val DNTA = scala.collection.mutable.Set[Sequent[FOLFormula]]()

    CNFp( seHs.reducedRepresentationToFormula ).foreach( clause => if ( !clause.isTaut ) {
      var NTAClause: Sequent[FOLFormula] = clause
      for ( literal <- clause.succedent ) {
        NTAClause = Neg( literal ) +: NTAClause
      }
      NTAClause = NTAClause.antecedent ++: Sequent()
      DNTA += NTAClause // define for fol and hol sequents
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )
    */

    val ( literals, dNTAList ) = seHs.literalsInTheDNTAsAndTheDNTAs

    val unifiedLiterals: Set[FOLFormula] = gStarUnify(
      seHs,
      literals,
      seHs.substitutionPairsAlpha(),
      seHs.substitutionPairsBeta(),
      seHs.universalEigenvariable,
      seHs.existentialEigenvariables,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    val literalsWithIndexLists: Set[LiteralWithIndexLists] = computeTheIndexListsForTheLiterals(
      unifiedLiterals,
      dNTAList,
      seHs,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    var numberOfAllowedClauses: Option[Int] = None
    var numberOfCheckedFormulas: Int = literalsWithIndexLists.size

    if ( literalsWithIndexLists.size > 1 ) {
      if ( seHs.noSolutionHasBeenFound ) {

        val allowedClausesWithIndexLists: Set[ClauseWithIndexLists] = checkAndBuildAllowedClausesHead(
          literalsWithIndexLists,
          seHs
        )

        numberOfAllowedClauses = Option(allowedClausesWithIndexLists.size)
        numberOfCheckedFormulas = allowedClausesWithIndexLists.size

        if ( seHs.noSolutionHasBeenFound ) {
          for ( numberOfClauses <- 2 to allowedClausesWithIndexLists.size; if seHs.noSolutionHasBeenFound ) {
            for ( subset <- allowedClausesWithIndexLists.subsets( numberOfClauses ); if seHs.noSolutionHasBeenFound ) {
              val clausesWithIndexLists = new ClausesWithIndexLists( subset.toList )
              if ( clausesWithIndexLists.isSolution ) {
                seHs.noSolutionHasBeenFound = false
                seHs.balancedSolution = Option( clausesWithIndexLists.formula )
              }
              numberOfCheckedFormulas += 1
            }
          }
        }
      }
    }

    println( "Number of non-tautological leaves" )
    println( dNTAList.length )
    println( "Number of unified literals" )
    println( unifiedLiterals.size )
    numberOfAllowedClauses match {
      case Some( t ) => {
        println( "Number of allowed clauses" )
        println( t )
      }
      case None =>
    }
    println( "Number of checked Formulas" )
    println( numberOfCheckedFormulas )

    if ( !seHs.noSolutionHasBeenFound ) {
      seHs.balancedSolution
    } else {
      None
    }

  }

  private def checkAndBuildAllowedClausesHead(
    literalsWithIndexLists: Set[LiteralWithIndexLists],
    seHs:                   pi2SeHs
  ): ( Set[ClauseWithIndexLists] ) = {

    var allowedClausesWithIndexListsMutable = scala.collection.mutable.Set[ClauseWithIndexLists]()
    val literalsWithIndexListsMutable = scala.collection.mutable.Set( literalsWithIndexLists.toList: _* )

    for ( literalWithIndexLists <- literalsWithIndexLists ) {
      val clause = new ClauseWithIndexLists( List( literalWithIndexLists ) )
      allowedClausesWithIndexListsMutable += clause
      if ( !clause.isAllowedAtLeastAsSubformula ) {
        literalsWithIndexListsMutable -= literalWithIndexLists
      }
    }

    checkAndBuildAllowedClauses(
      literalsWithIndexListsMutable,
      allowedClausesWithIndexListsMutable,
      seHs,
      2
    ).toSet

  }

  private def checkAndBuildAllowedClauses(
    literalsWithIndexLists:       scala.collection.mutable.Set[LiteralWithIndexLists],
    allowedClausesWithIndexLists: scala.collection.mutable.Set[ClauseWithIndexLists],
    seHs:                         pi2SeHs,
    subsetSize:                   Int
  ): ( scala.collection.mutable.Set[ClauseWithIndexLists] ) = {

    for ( subset <- literalsWithIndexLists.subsets( subsetSize ); if seHs.noSolutionHasBeenFound ) {
      val clauseWithIndexLists = new ClauseWithIndexLists( subset.toList )
      if ( clauseWithIndexLists.isAllowed ) {
        allowedClausesWithIndexLists += clauseWithIndexLists
        val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
        if ( clausesWithIndexLists.isSolution ) {
          seHs.noSolutionHasBeenFound = false
          seHs.balancedSolution = Option( clausesWithIndexLists.formula )
        }
      } else if ( !clauseWithIndexLists.isAllowedAtLeastAsSubformula ) {
        for ( literal <- subset ) {
          literalsWithIndexLists -= literal
        }
      }
    }

    if ( seHs.noSolutionHasBeenFound && ( literalsWithIndexLists.size > subsetSize ) ) {
      checkAndBuildAllowedClauses(
        literalsWithIndexLists,
        allowedClausesWithIndexLists,
        seHs,
        subsetSize + 1
      )
    } else {
      allowedClausesWithIndexLists
    }

  }

  private def computeTheIndexListsForTheLiterals(
    unifiedLiterals:       Set[FOLFormula],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    y:                     FOLVar,
    x:                     FOLVar
  ): ( Set[LiteralWithIndexLists] ) = {

    val literalWithIndexListsSet = scala.collection.mutable.Set[LiteralWithIndexLists]()

    for ( literal <- unifiedLiterals; if seHs.noSolutionHasBeenFound ) {

      var foundEmptyMOrPList: Boolean = false
      var foundNonEmptyPList: Boolean = false
      var leafOfIndexList: List[LeafIndex] = Nil

      for ( leaf <- nonTautologicalLeaves ) {

        var leafIndexP = Set[Int]()
        var leafIndexM = Set[Int]()

        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs = Substitution( ( x, seHs.universalEigenvariable ), ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = subs( literal ).asInstanceOf[FOLFormula] +: Sequent()
          if ( subsetSequent.isSubsetOf( leaf ) ) {
            leafIndexP += existsIndex
          }
        }

        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution( ( x, seHs.substitutionsForAlpha( forallIndex ) ), ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = Neg( subs( literal ).asInstanceOf[FOLFormula] ) +: Sequent()
          if ( !leaf.intersect( subsetSequent ).isEmpty ) {
            leafIndexM += forallIndex
          }

        }

        if ( leafIndexM.isEmpty || leafIndexP.isEmpty ) {
          foundEmptyMOrPList = true
        }
        if ( leafIndexP.nonEmpty ) {
          foundNonEmptyPList = true
        }
        val leafIndex = new LeafIndex( leafIndexM, leafIndexP )
        leafOfIndexList = leafOfIndexList :+ leafIndex

      }

      val literalWithIndexLists = new LiteralWithIndexLists( literal, leafOfIndexList, nonTautologicalLeaves.length )

      if ( foundNonEmptyPList ) {

        literalWithIndexListsSet += literalWithIndexLists

        if ( !foundEmptyMOrPList ) {
          val clauseWithIndexLists = new ClauseWithIndexLists( List( literalWithIndexLists ) )
          val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
          if ( clausesWithIndexLists.isSolution ) {
            seHs.noSolutionHasBeenFound = false
            seHs.balancedSolution = Option( clausesWithIndexLists.formula )
          }
        }
      }

    }

    literalWithIndexListsSet.toSet

  }

}