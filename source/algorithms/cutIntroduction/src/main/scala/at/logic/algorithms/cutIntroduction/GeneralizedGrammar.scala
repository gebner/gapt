/*
 * Grammar that generates a list of terms T
 * 
 * NOTE: This is not the implementation of a grammar in the usual sense.
 * Here we keep only two sets, U and S, for the grammar with start symbol 'τ',
 * non-terminal 'α' and production rules 
 * P = { τ -> u | u in U} union { α -> s | s in S } 
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.calculi.occurrences._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.dssupport.MapSupport._
import at.logic.utils.logging.Logger
import at.logic.utils.executionModels.searchAlgorithms.SetNode
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.{DFS, BFS, setSearch}
import Deltas._


/** Creates a grammar from a decomposition (u,S).
  */
class GeneralizedGrammar(u0: List[FOLTerm], s0: types.S, ev: String) {

  val u = u0
  val s = s0
  val eigenvariable = ev

  // Is this the best solution?
  var flatterms: FlatTermSet = null

  /** Returns the size of the grammar, i.e. |u| + |s| */
  def size = u.size + safeHead(s, Nil).length //s.foldLeft(0)((n,sPart) => n + sPart.size)

  /** Returns the set of eigenvariables that occur in u. */
  def eigenvariables = u.flatMap(collectVariables).distinct

  /** Returns the number of eigenvariables that occur in this grammar. Equals this.eigenvariables.length. */
  def numVars = s.length

  /** Collects the variables occurring in a FOL term. */
  /*private def collectEigenvariables(u : types.U) : List[FOLVar] = u match {
    case Function(_,terms) => terms.map(collectEigenvariables).foldLeft(Nil:List[FOLVar])(_ ++ _)
    case FOLVar(x) => List(FOLVar(x))
  }*/

/*
  def strictSuperGrammarOf(g : Grammar) = 
    // U o S \supset U' o S'
    // U \supset U' and S \supset S'
    g.u.forall(e => u.contains(e)) && g.s.forall(e => s.contains(e)) &&
    // |U| > |U'| or |S| > |S'|
    (u.size > g.u.size || s.size > g.s.size)
*/

  def toPrettyString : String = "{ " + u.foldRight("")((ui, str) => str + ui + ", ") + " } o { " + s.foldRight("") ((si, str) => str + si + ", " ) + " }" 
  override def toString() : String = {
    "{ " + u.foldRight("")((ui, str) => str + ui + ", ") + " } o { " + s.foldRight("") ((si, str) => str + si + ", " ) + " }"
  }
}

/** Takes a set of terms and, using DeltaG, computes the set of smallest grammars that generate it.
  */
object ComputeGeneralizedGrammars extends Logger {
  // Uses findValidGrammar2.
  def apply(terms: FlatTermSet, delta: DeltaVector) : List[GeneralizedGrammar] = apply(terms.termset, delta).map{ case g => g.flatterms = terms; g }

  def apply(terms: List[FOLTerm], delta: DeltaVector) : List[GeneralizedGrammar] = {
    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = "α"
    
    //debug( "3rd version - computing delta-table" )
    val deltatable = new GeneralizedDeltaTable(terms, eigenvariable, delta)
    //debug( "done computing delta-table" )
    //deltatable.printStats( { s => trace( "  " + s ) } )

    //debug( "reading off grammars from delta-table" )
    findValidGrammars(terms, deltatable, eigenvariable).sortWith((g1, g2) => g1.size < g2.size )
  }


  /** Finds valid, minimum-size grammars based on a list of terms and a generalized delta table.
    * 
    *
    * This method is an adaptation of Grammar.findValidGrammars.
    *
    * @param terms The terms to be compressed.
    * @param deltatable A generalized delta table for terms.
    * @param eigenvariable The name of eigenvariables to introduce.
    */
  def findValidGrammars(terms: List[FOLTerm], deltatable: GeneralizedDeltaTable, eigenvariable: String) : List[GeneralizedGrammar] = {
    
    //Helper functions for grammars

    //The number of variables in a decomposition
    def numVars(s: types.S) = s.size
    //The sum of the sizes of the s-vectors
    def ssize(s: types.S) = s.map(vec => vec.size).foldLeft(0)(_ + _)
    //The number of terms this grammar compresses (grammars that "compress" only one terms are useless and
    //hence discarded here.)
    def numTerms(s: types.S, t: List[FOLTerm]) = if (s.size != 0) s.head.size else t.size


    // This gets decremented as iterating through the delta table reveals
    // smaller and smaller grammars. The initial value is the size of the trivial decomposition
    // (alpha,terms)
    var smallestGrammarSize = terms.size


    // Exact computation of the smallest coverings. Returns only these. Memory-aware implementation.
    // s is the key of the delta table and pairs is a list of (u,T), where s applied to u = T.
    def smallestCoverExact(s: types.S, pairs: List[(types.U, List[FOLTerm])]) = {

      // |U| + |S| < |T|
      // We only need to consider subsets of size |smallestGrammar| - |S| or less
      val maxSubsetSize = smallestGrammarSize - ssize(s)

      trace("[smallestCoverExact] terms: " + terms)
      trace("[smallestCoverExact] maxSubsetSize: " + maxSubsetSize)

      // Trying a lazy list so that not all subsets are computed at once. 
      // BUT not sure if I am getting the behavior I expect...

      //val subsets = all subsets pairs of size (1..maxSubsetSize)
      lazy val subsets = (1 to maxSubsetSize).toList.foldLeft(Iterator[Set[(types.U, List[FOLTerm])]]()) {
        case (acc, i) => pairs.toSet.subsets(i) ++ acc
      }

      // Supposedly these subsets are in increasing order of size, 
      // so the lazy structure will not have to load the bigger ones.
      var coverSize = maxSubsetSize

      //Returns the smallest subset {(u1,T1),...,(un,Tn)} of a line in the delta table
      //such that. Union(T1,...,Tn) + C = terms, where C are some constant terms.
      def getSmallestSubsets(subsets: Iterator[Set[(types.U, List[FOLTerm])]]) : List[List[FOLTerm]] = {
        if(subsets.hasNext) {

          trace("[smallestCoverExact]    hasNext!")

          val set = subsets.next()

          trace("[smallestCoverExact]    set=" + set)

          if(set.size <= coverSize) {
            trace("[smallestCoverExact]    set.size < coverSize!")
            //Create the union of the pairs in the subset and check whether it amounts to <terms>
            val (u, t) = set.foldLeft( ( List[types.U](), List[FOLTerm]() ) ) { case (acc, (u, t)) => 
              ( u :: acc._1, tailRecUnion(t, acc._2) )
            }

            trace("[smallestCoverExact]    (u,t)=(" + u + ", " + t + ")")
            val difference = terms.diff(t)
            trace("[smallestCoverExact]    difference=" + difference)

            //Union(T1,...,Tn) = terms => we are finished
            if(difference.size == 0) {
              trace("[smallestCoverExact]    OUTCOME: no difference!")
              trace("[smallestCoverExact]             coversize=" + set.size)
              coverSize = set.size
              u :: getSmallestSubsets(subsets) 
            } 
            //Some constant terms need to be added => add the difference to coverSize
            else if(u.size + difference.size <= coverSize) {
              coverSize = u.size + difference.size
              (u ++ difference) :: getSmallestSubsets(subsets) 
            } 
            else {
              trace("[smallestCoverExact]    OUTCOME: difference too large!")
              getSmallestSubsets(subsets)
            }
         
          } else {
            trace("[smallestCoverExact]    NOT set.size < coverSize!")
            List()
          }
        } else List()
      }

      val coverings = getSmallestSubsets(subsets)

      trace("[smallestCoverExact] coverSize: " + coverSize)

      smallestGrammarSize = ssize(s) + coverSize

      trace("[smallestCoverExact] new smallestGrammarSize: " + smallestGrammarSize)
      coverings
    }

    trace("STARTING FOLDING")
    trace("smallestGrammarSize= " + smallestGrammarSize)

    trace("---------------------------------------------")
    trace("DTG Contents: ")
    trace(deltatable.table.toString)
    trace("---------------------------------------------")

    //Go through the rows of the delta table and find the smallest
    //covering in each row.
    deltatable.table.foldLeft(List[GeneralizedGrammar]()) {case (grammars, (s, pairs)) =>

      // Ignoring entries where s.size == 1 because they are trivial
      // grammars with the function symbol on the right.
      trace("[folding DTG] checking grammar: " + s)

      if(numTerms(s, safeHead(pairs, (null, Nil))._2) > 1) {

        trace("[folding DTG] - passed size check")

        // Add the trivial decomposition {alpha_0} o s if s only has one vector
        val ev = FOLVar(new VariableStringSymbol(eigenvariable + "_0"))
        val newpairs = if(s.size == 1 && s.head.forall(e => terms.contains(e)) ) { (ev, s.head) :: pairs } else pairs

        trace("    | newpairs:")
        trace(newpairs.toString())

        // Whenever we find a smaller S-vector,
        // we add the grammars in its row to the list of returned ones.
        if(ssize(s) < smallestGrammarSize) {      

          trace("[folding DTG] - passed s.size with ssize=" + ssize(s) + ", smallestGrammarSize=" + smallestGrammarSize)              
          val coverings = smallestCoverExact(s, newpairs)

          trace("[folding DTG] coverings: " + coverings)

          coverings.foldLeft(grammars) { case (acc, u) =>
            (new GeneralizedGrammar(u, s, eigenvariable) ) :: acc                   
          }                                                   
        } else grammars                                       
                                                                                                                            
      } else {
        trace("[folding DTG] +++FAILED SIZE CHECK+++ s     =" + s)
        trace("                                      pairs =" + pairs)
        grammars
      }
    }
  }

}

