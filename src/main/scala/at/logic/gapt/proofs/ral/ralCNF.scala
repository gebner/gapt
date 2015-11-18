package at.logic.gapt.proofs.ral

import at.logic.gapt.expr.hol.SkolemSymbolFactory
import at.logic.gapt.expr._
import at.logic.gapt.proofs.ral.RalProof.Label
import at.logic.gapt.proofs._

import scala.collection.mutable

object ralCNF {

  def apply( sequent: HOLSequent ): ( Set[RalProof], Map[Const, LambdaExpression] ) = {
    val alreadyVisited = mutable.Set[Sequent[( Label, HOLFormula )]]()
    val cnf = mutable.Set[RalProof]()
    val defs = mutable.Map[Const, LambdaExpression]()

    val skolemSymbols = new SkolemSymbolFactory().getSkolemSymbols.iterator
    //    val symsInSequent = constants( sequent ) map { _.name }
    val defSymbols = Stream from 1 map { i => s"X$i" } iterator

    def visit( p: RalProof ): Unit =
      if ( !alreadyVisited( p.conclusion ) ) {
        alreadyVisited += p.conclusion

        if ( p.formulas.isTaut ) return

        p.formulas.zipWithIndex foreach {
          case ( Top(), i: Ant )       => return visit( RalTopF( p, i ) )
          case ( Top(), i: Suc )       => return
          case ( Bottom(), i: Suc )    => return visit( RalBottomT( p, i ) )
          case ( Bottom(), i: Ant )    => return
          case ( Neg( _ ), i: Ant )    => return visit( RalNegF( p, i ) )
          case ( Neg( _ ), i: Suc )    => return visit( RalNegT( p, i ) )
          case ( And( _, _ ), i: Ant ) => return visit( RalAndF( p, i ) )
          case ( Or( _, _ ), i: Suc )  => return visit( RalOrT( p, i ) )
          case ( Imp( _, _ ), i: Suc ) => return visit( RalImpT( p, i ) )

          case ( All( x, f ), i: Suc ) =>
            val eigen = rename( x, freeVariables( p.formulas.elements ).toList )
            return visit( RalAllT( p, i, eigen ) )
          case ( Ex( x, f ), i: Ant ) =>
            val eigen = rename( x, freeVariables( p.formulas.elements ).toList )
            return visit( RalExF( p, i, eigen ) )

          case ( All( x, f ), i: Ant ) =>
            return visit( RalAllF( p, i, skolemSymbols.next ) )
          case ( Ex( x, f ), i: Suc ) =>
            return visit( RalExT( p, i, skolemSymbols.next ) )

          case _ =>
        }

        def abbreviate( i: SequentIndex ) = {
          val f = p.formulas( i )
          val freeVars = freeVariables( f ).toSeq
          val abbrev = HOLAtomConst( defSymbols.next, freeVars map { _.exptype }: _* )
          val definition = RalInitial( Sequent() :+ ( Label() -> ( abbrev( freeVars: _* ) <-> f ) ) )
          defs( abbrev ) = Abs( freeVars, f )
          if ( i isSuc ) {
            visit( RalCut( p, Seq( i ), RalImpT( RalAndT2( definition, Suc( 0 ) ), Suc( 0 ) ), Seq( Ant( 0 ) ) ) )
            visit( RalAndT1( definition, Suc( 0 ) ) )
          } else {
            visit( RalCut( RalImpT( RalAndT1( definition, Suc( 0 ) ), Suc( 0 ) ), Seq( Suc( 0 ) ), p, Seq( i ) ) )
            visit( RalAndT2( definition, Suc( 0 ) ) )
          }
        }

        val splits = p.formulas.zipWithIndex.elements filter {
          case ( And( _, _ ), i: Suc ) => true
          case ( Or( _, _ ), i: Ant )  => true
          case ( Imp( _, _ ), i: Ant ) => true
          case _                       => false
        }

        if ( splits.size > 1 ) // define the first one
          return abbreviate( splits.head._2 )

        p.formulas.zipWithIndex foreach {
          case ( And( _, _ ), i: Suc ) =>
            visit( RalAndT1( p, i ) )
            visit( RalAndT2( p, i ) )
            return
          case ( Or( _, _ ), i: Ant ) =>
            visit( RalOrF1( p, i ) )
            visit( RalOrF2( p, i ) )
            return
          case ( Imp( _, _ ), i: Ant ) =>
            visit( RalImpF1( p, i ) )
            visit( RalImpF2( p, i ) )
            return

          case _ =>
        }

        cnf += p
      }

    for ( f <- sequent.antecedent ) visit( RalInitial( Sequent() :+ ( Label() -> f ) ) )
    for ( f <- sequent.succedent ) visit( RalInitial( ( Label() -> f ) +: Sequent() ) )

    ( cnf.toSet, defs.toMap )
  }

}
