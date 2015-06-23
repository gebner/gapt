package at.logic.gapt.grammars

import TratGrammar._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution

import scala.collection.{ mutable, GenTraversable }
import scala.collection.mutable.ListBuffer

class LangToTree {
  val axiom = FOLVar( "A0" )
  val productions = ListBuffer[Production]()

  var i = 0
  def newNonTerminal(): FOLVar = {
    i += 1
    FOLVar( s"A$i" )
  }

  def insert( t: FOLTerm ): Unit = t match {
    case FOLFunction( f, as ) =>
      productions += axiom -> FOLFunction( f, as map insertSubterm )
  }

  private def insertSubterm( t: FOLTerm ): FOLVar = t match {
    case FOLFunction( f, as ) =>
      val newNT = newNonTerminal()
      productions += newNT -> FOLFunction( f, as map insertSubterm )
      newNT
  }

  def toGrammar: TratGrammar =
    TratGrammar( axiom, productions )
}

object LangToTree {
  def apply( lang: GenTraversable[FOLTerm] ): TratGrammar = {
    val langToTree = new LangToTree
    lang foreach langToTree.insert
    langToTree toGrammar
  }
}

object mergeNTs {
  def apply( g: TratGrammar, a1: FOLVar, a2: FOLVar ) = {
    val subst = FOLSubstitution( a2 -> a1 )
    try {
      Some( TratGrammar( g.axiom, g.productions map {
        case ( a, t ) =>
          subst( a ).asInstanceOf[FOLVar] -> subst( t )
      } ) )
    } catch {
      case _: IllegalArgumentException => None
    }
  }
}

object allMerges {
  def apply( g: TratGrammar ): Seq[TratGrammar] = {
    g.nonTerminals.flatMap { a1 =>
      g.nonTerminals.flatMap {
        case a2 if a1.toString <= a2.toString =>
          mergeNTs( g, a1, a2 )
        case _ => None
      }
    }
  }
}