package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees._

import scala.collection.mutable

object structuralCNF {

  sealed trait Justification
  case class ProjectionFromEndSequent( projection: ExpansionSequent ) extends Justification
  case class Definition( index: SequentIndex, expansion: ExpansionTree ) extends Justification

  def apply( formula: HOLFormula ): ( Set[HOLClause], Map[HOLClause, Justification], Map[HOLAtomConst, LambdaExpression] ) = {
    val cnf = mutable.Set[HOLClause]()
    val proofs = mutable.Map[HOLClause, Justification]()
    val defs = mutable.Map[LambdaExpression, HOLAtomConst]()

    val symsInFormula = constants( formula ) map { _.name }
    val skolemSyms = new SkolemSymbolFactory().getSkolemSymbols.map { _.toString() }.filter { s => !symsInFormula.contains( s ) }.iterator
    val abbrevSyms = Stream.from( 0 ).map { i => s"X$i" }.filter { s => !symsInFormula.contains( s ) }.iterator

    // We do a clausification similar to forward proof search in Ral.
    // (But we handle Skolemization more as an afterthought here.)

    // Since we want a CNF of formula, we start with the singleton set of sequents (:- formula).
    expand( Sequent() :+ formula, es => ProjectionFromEndSequent( es.swapped ) )

    // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.
    // In each step we simplify the sequents in this set and make them more like clauses.

    // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
    def expand( seq: HOLSequent, backTrans: ExpansionSequent => Justification ): Unit = {
      val ant = mutable.Buffer[HOLFormula]()
      val suc = mutable.Buffer[HOLFormula]()
      lazy val freeVars = mutable.Set[Var]( freeVariables( seq ).toSeq: _* )
      var trivial = false

      def left( f: HOLFormula ): ( ExpansionSequent => ExpansionTree ) = f match {
        case All( x, a ) => right( Ex( x, -a ) )
        case Ex( x, a )  => right( All( x, -a ) )
        case And( a, b ) =>
          val fa = left( a )
          val fb = left( b )
          es => ETAnd( fa( es ), fb( es ) )
        case Neg( a ) =>
          val fa = right( a )
          es => ETNeg( fa( es ) )
        case Top() => es => ETTop
        case Bottom() =>
          trivial = true
          es => ETBottom
        case _ =>
          if ( !ant.contains( f ) ) ant += f
          es => es( Ant( ant indexOf f ) )
      }

      def right( f: HOLFormula ): ( ExpansionSequent => ExpansionTree ) = f match {
        case All( x, a ) =>
          val eigen = rename( x, freeVars.toList )
          freeVars += eigen
          val fa = right( Substitution( x -> eigen )( a ) )
          es => ETWeakQuantifier( f, fa( es ) -> eigen ).asInstanceOf[ExpansionTree]
        case Ex( x, a ) =>
          val fvs = freeVariables( f ).toSeq
          val skolem = Const( skolemSyms.next, FunctionType( x.exptype, fvs map { _.exptype } ) )
          val fa = right( Substitution( x -> skolem( fvs: _* ) )( a ) )
          es => ETSkolemQuantifier( f, skolem, fa( es ) )
        case Or( a, b ) =>
          val fa = right( a )
          val fb = right( b )
          es => ETOr( fa( es ), fb( es ) )
        case Imp( a, b ) =>
          val fa = left( a )
          val fb = right( b )
          es => ETImp( fa( es ), fb( es ) )
        case Neg( a ) =>
          val fa = left( a )
          es => ETNeg( fa( es ) )
        case Bottom() => es => ETBottom
        case Top() =>
          trivial = true
          es => ETTop
        case _ =>
          if ( !suc.contains( f ) ) suc += f
          es => es( Suc( suc indexOf f ) )
      }

      val expandBackTranfs = seq.map( left, right )

      if ( !trivial && ant.intersect( suc ).isEmpty )
        split(
          Sequent( ant.toSeq, suc.toSeq ),
          es => backTrans( expandBackTranfs.map( _( es ) ) )
        )
    }

    // Then we simplify the connectives which correspond to nested conjunctions, e.g. (:- a&b) turns into (:- a) and (:- b).
    // In order to combat exponential blow-up, we do something special if there are two or more such elements:
    // we introduce a definition for the first one.
    def split( seq: HOLSequent, backTrans: ExpansionSequent => Justification ): Unit = {
      seq.zipWithIndex.elements collect {
        case ( And( a, b ), i: Suc ) => i
        case ( Or( a, b ), i: Ant )  => i
        case ( Imp( a, b ), i: Ant ) => i
      } match {
        case splits if splits.size > 1 =>
          abbrev( seq, splits.head, backTrans )
        case Seq( i ) => splitAt( seq, i, backTrans )
        case Seq() =>
          val clause = seq.map { _.asInstanceOf[HOLAtom] }
          cnf += clause
          proofs( clause ) = backTrans( clause map ETAtom )
      }
    }

    def splitAt( seq: HOLSequent, i: SequentIndex, backTrans: ExpansionSequent => Justification ): Unit =
      ( seq( i ), i ) match {
        case ( And( a, b ), i: Suc ) =>
          splitAt( seq.updated( i, a ), i, es => backTrans( es.updated( i, ETAnd( es( i ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETAnd( ETWeakening( a ), es( i ) ) ) ) )
        case ( Or( a, b ), i: Ant ) =>
          splitAt( seq.updated( i, a ), i, es => backTrans( es.updated( i, ETOr( es( i ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETOr( ETWeakening( a ), es( i ) ) ) ) )
        case ( Imp( a, b ), i: Ant ) =>
          val aIdx = Suc( seq.succedent.size )
          splitAt( seq.delete( i ) :+ a, aIdx, es => backTrans( es.delete( aIdx ).insertAt( i, ETImp( es( aIdx ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETImp( ETWeakening( a ), es( i ) ) ) ) )
        case _ => expand( seq, backTrans )
      }

    // Here, we replace the formula at index i with a definition, and continue with
    // both the abbreviated sequent, and (the necessary part of) the definition.
    def abbrev( seq: HOLSequent, i: SequentIndex, backTrans: ExpansionSequent => Justification ): Unit = {
      val f = seq( i )
      val fvs = freeVariables( f ).toSeq
      val const = defs.getOrElseUpdate(
        Abs( fvs, f ),
        HOLAtomConst( abbrevSyms.next(), fvs map { _.exptype }: _* )
      )
      val repl = const( fvs: _* )
      if ( i isAnt ) {
        expand( Sequent( Seq( f ), Seq( repl ) ), es => Definition( es indexOf ETAtom( repl ), es( Ant( 0 ) ) ) )
      } else {
        expand( Sequent( Seq( repl ), Seq( f ) ), es => Definition( es indexOf ETAtom( repl ), es( Suc( 0 ) ) ) )
      }
      split( seq.updated( i, repl ), es => backTrans( es.updated( i, ETAtom( repl ) ) ) )
    }

    ( cnf.toSet, proofs.toMap, defs.map( _.swap ).toMap )
  }

}
