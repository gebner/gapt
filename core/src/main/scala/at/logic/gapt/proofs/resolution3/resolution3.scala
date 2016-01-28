package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

trait ResolutionProof extends SequentProof[HOLFormula, ResolutionProof]

trait NullaryResolutionProof extends ResolutionProof with ContextRule[HOLFormula, ResolutionProof] {
  def immediateSubProofs = Seq()
  def auxIndices = Seq()
}

trait UnaryResolutionProof extends ResolutionProof with ContextRule[HOLFormula, ResolutionProof] {
  def subProof: ResolutionProof
  def immediateSubProofs = Seq( subProof )
}

abstract class OneFormulaRule extends UnaryResolutionProof {
  def idx: SequentIndex
  def auxIndices = Seq( Seq( idx ) )

  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ): ResolutionProof
}

case class Inp( sequent: HOLSequent ) extends NullaryResolutionProof {
  def mainFormulaSequent = sequent
}

case class Refl( term: LambdaExpression ) extends NullaryResolutionProof {
  def mainFormulaSequent = Sequent() :+ ( term === term )
}

case class EqAx( equation: HOLAtom, formula: HOLFormula, positions: Seq[LambdaPosition], leftToRight: Boolean ) extends NullaryResolutionProof {
  val ( t, s ) = equation match { case Eq( t_, s_ ) => if ( leftToRight ) t_ -> s_ else s_ -> t_ }
  for ( pos <- positions ) require( formula( pos ) == t )
  val newFormula = positions.foldLeft( formula )( ( f, pos ) => f.replace( pos, s ).asInstanceOf[HOLFormula] )
  def mainFormulaSequent = equation +: formula +: Sequent() :+ newFormula
}

case class Taut( formula: HOLFormula ) extends NullaryResolutionProof {
  def mainFormulaSequent = formula +: Sequent() :+ formula
}

case class Subst( subProof: ResolutionProof, substitution: Substitution ) extends ResolutionProof {
  val conclusion = subProof.conclusion map { substitution( _ ) }

  def auxIndices = Seq( subProof.conclusion.indices )
  def mainIndices = conclusion.indices
  def immediateSubProofs = Seq( subProof )
  def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion, subProof.conclusion.indicesSequent map { Seq( _ ) } ) )
}

case class Res( subProof1: ResolutionProof, idx1: Suc, subProof2: ResolutionProof, idx2: Ant ) extends ResolutionProof with ContextRule[HOLFormula, ResolutionProof] {
  require( subProof1.conclusion( idx1 ) == subProof2.conclusion( idx2 ) )
  def auxIndices = Seq( Seq( idx1 ), Seq( idx2 ) )
  def mainFormulaSequent = Sequent()
  def immediateSubProofs = Seq( subProof1, subProof2 )
}

case class Fac( subProof: ResolutionProof, idx1: SequentIndex, idx2: SequentIndex ) extends UnaryResolutionProof {
  require( idx1 sameSideAs idx2 )
  require( subProof.conclusion( idx1 ) == subProof.conclusion( idx2 ) )
  val mainFormula = subProof.conclusion( idx1 )
  def mainFormulaSequent = if ( idx1.isSuc ) Sequent() :+ mainFormula else mainFormula +: Sequent()
  def auxIndices = Seq( Seq( idx1, idx2 ) )
}

case class Def( subProof: ResolutionProof, idx: SequentIndex, by: HOLFormula ) extends OneFormulaRule {
  def mainFormulaSequent = if ( idx.isSuc ) Sequent() :+ by else by +: Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex )
}

case class TopL( subProof: ResolutionProof, idx: Ant ) extends OneFormulaRule {
  val Top() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Ant] )
}

case class BottomR( subProof: ResolutionProof, idx: Suc ) extends OneFormulaRule {
  val Bottom() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Suc] )
}

case class NegL( subProof: ResolutionProof, idx: Ant ) extends OneFormulaRule {
  val Neg( aux ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ aux
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Ant] )
}

case class NegR( subProof: ResolutionProof, idx: Suc ) extends OneFormulaRule {
  val Neg( aux ) = subProof.conclusion( idx )
  def mainFormulaSequent = aux +: Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Suc] )
}

case class AndL( subProof: ResolutionProof, idx: Ant ) extends OneFormulaRule {
  val And( left, right ) = subProof.conclusion( idx )
  def mainFormulaSequent = left +: right +: Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Ant] )
}

case class OrR( subProof: ResolutionProof, idx: Suc ) extends OneFormulaRule {
  val Or( left, right ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ left :+ right
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Suc] )
}

case class ImpR( subProof: ResolutionProof, idx: Suc ) extends OneFormulaRule {
  val Imp( left, right ) = subProof.conclusion( idx )
  def mainFormulaSequent = left +: Sequent() :+ right
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Suc] )
}

case class AndR( subProof: ResolutionProof, idx: Suc, which: Boolean ) extends OneFormulaRule {
  val And( left, right ) = subProof.conclusion( idx )
  val mainFormula = if ( !which ) left else right
  def mainFormulaSequent = Sequent() :+ mainFormula
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Suc] )
}

case class OrL( subProof: ResolutionProof, idx: Ant, which: Boolean ) extends OneFormulaRule {
  val Or( left, right ) = subProof.conclusion( idx )
  val mainFormula = if ( !which ) left else right
  def mainFormulaSequent = mainFormula +: Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Ant] )
}

case class ImpL( subProof: ResolutionProof, idx: Ant, which: Boolean ) extends OneFormulaRule {
  val Imp( left, right ) = subProof.conclusion( idx )
  def mainFormulaSequent =
    if ( !which ) Sequent() :+ left
    else right +: Sequent()
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex.asInstanceOf[Ant] )
}

case class WeakQ( subProof: ResolutionProof, idx: SequentIndex, freshVar: Var ) extends OneFormulaRule {
  val ( bound, qfFormula ) = subProof.conclusion( idx ) match {
    case All( b, qf ) if idx isSuc => ( b, qf )
    case Ex( b, qf ) if idx isAnt  => ( b, qf )
  }
  val mainFormula = Substitution( bound -> freshVar )( qfFormula )
  val mainFormulaSequent =
    if ( idx isAnt ) mainFormula +: Sequent()
    else Sequent() :+ mainFormula
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex )
}

case class Sk( subProof: ResolutionProof, idx: SequentIndex, skolemTerm: LambdaExpression ) extends OneFormulaRule {
  val ( bound, qfFormula ) = subProof.conclusion( idx ) match {
    case All( b, qf ) if idx isAnt => ( b, qf )
    case Ex( b, qf ) if idx isSuc  => ( b, qf )
  }
  val mainFormula = Substitution( bound -> skolemTerm )( qfFormula )
  val mainFormulaSequent =
    if ( idx isAnt ) mainFormula +: Sequent()
    else Sequent() :+ mainFormula
  def copyInference( newSubProof: ResolutionProof, newIndex: SequentIndex ) = copy( subProof = newSubProof, idx = newIndex )
}
