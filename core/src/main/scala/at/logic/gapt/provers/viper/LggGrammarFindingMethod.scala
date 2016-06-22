package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ RecursionScheme, instantiateRS, leastGeneralGeneralization, leastGeneralGeneralization1 }
import at.logic.gapt.proofs.{ Context, FiniteContext }

import scala.collection.mutable

case class LggGrammarFindingMethod(
    paramTys: Seq[Ty],
    context:  FiniteContext
) extends InductiveGrammarFindingMethod {
  implicit def ctx = context

  def find( taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): RecursionScheme = {
    val instanceLanguages = taggedLanguage.groupBy( _._1 ).mapValues( _.map( _._2 ) )

    val constructors = context.typeDefs.flatMap {
      case Context.InductiveType( _, cs ) => cs
      case _                              => Seq()
    }

    val instanceCombinations = instanceLanguages map {
      case ( inst, lang ) =>
        val instSubterms = inst.flatMap( instantiateRS.subTerms ).map {
          case Apps( ctr: Const, args ) if constructors( ctr ) => args.toSet
          case _ => Set[LambdaExpression]()
        }

        val combs = mutable.Map[LambdaExpression, Set[Substitution]]().withDefaultValue( Set() )
        for {
          r1 <- lang
          r2 <- lang
          if r1 != r2
          ( lgg, sigma1, sigma2 ) = leastGeneralGeneralization( r1, r2 )
          if instSubterms.exists( sigma1.values.toSet subsetOf _ )
          if instSubterms.exists( sigma2.values.toSet subsetOf _ )
        } combs( lgg ) ++= Seq( Substitution( sigma1 ), Substitution( sigma2 ) )

        println( inst )
        for ( ( lgg, substs ) <- combs ) {
          println( lgg )
          for ( subst <- substs ) println( s" $subst" )
        }
        println()

        inst -> combs.toMap
    }

    ???
  }
}
