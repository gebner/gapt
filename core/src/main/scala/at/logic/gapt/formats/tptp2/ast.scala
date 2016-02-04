package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr.{ LambdaExpression, FOLFormula, HOLFormula }
import at.logic.gapt.proofs.HOLClause

object definitions {
  type TptpFile = Seq[TptpInput]
  type GeneralTerm = LambdaExpression
  type InfoItem = GeneralTerm
}
import definitions._

sealed trait TptpInput {
  override def toString = tptpToString.tptpInput( this )
}
sealed abstract class TptpFormulaInput extends TptpInput {
  def name: String
  def role: FormulaRole
  def annotations: Option[Annotations]
}
// how to encode?  thf(someName, type, foo: $tType)
case class ThfFormula( name: String, role: FormulaRole, formula: HOLFormula, annotations: Option[Annotations] ) extends TptpFormulaInput
case class TffFormula( name: String, role: FormulaRole, formula: HOLFormula, annotations: Option[Annotations] ) extends TptpFormulaInput
case class FofFormula( name: String, role: FormulaRole, formula: FOLFormula, annotations: Option[Annotations] ) extends TptpFormulaInput
case class CnfFormula( name: String, role: FormulaRole, formula: HOLFormula, annotations: Option[Annotations] ) extends TptpFormulaInput
case class IncludeDirective( fileName: String, formulaSelection: Seq[String] ) extends TptpInput

sealed abstract class FormulaRole( val name: String )
case object Axiom extends FormulaRole( "axiom" )
case object Hypothesis extends FormulaRole( "hypothesis" )
case object Definition extends FormulaRole( "definition" )
case object Type extends FormulaRole( "type" )
case object Assumption extends FormulaRole( "assumption" )
case object Lemma extends FormulaRole( "lemma" )
case object Theorem extends FormulaRole( "theorem" )
case object Corollary extends FormulaRole( "corollary" )
case object Conjecture extends FormulaRole( "conjecture" )
case object NegatedConjecture extends FormulaRole( "negated_conjecture" )
case object Question extends FormulaRole( "question" )
case object Plain extends FormulaRole( "plain" )
case object Answer extends FormulaRole( "answer" )
case object FiDomain extends FormulaRole( "fi_domain" )
case object FiFunctors extends FormulaRole( "fi_functors" )
case object FiPredicates extends FormulaRole( "fi_predicates" )
case object Unknown extends FormulaRole( "unknown" )

case class Annotations( source: Source, usefulInfo: Seq[InfoItem] )

sealed trait Source {
  override def toString = tptpToString.source( this )
}
case class DagSource( name: String ) extends Source
case class InferenceRecord( inferenceRule: String, usefulInfo: Seq[InfoItem], parentInfo: Seq[ParentInfo] ) extends Source
case class InternalSource( introType: String, introInfo: Seq[InfoItem] ) extends Source
case class FileSource( fileName: String, fileInfo: Option[String] ) extends Source
case class Theory( theoryName: String, usefulInfo: Seq[InfoItem] ) extends Source
case class CreatorSource( creatorName: String, usefulInfo: Seq[InfoItem] ) extends Source

case class ParentInfo( source: Source, parentDetails: Seq[GeneralTerm] )
