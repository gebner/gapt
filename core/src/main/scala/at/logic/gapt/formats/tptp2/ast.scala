package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr.{ LambdaExpression, FOLFormula, HOLFormula }
import at.logic.gapt.proofs.HOLClause

object definitions {
  type TptpFile = Seq[TptpInput]
  type GeneralTerm = LambdaExpression
  type FormulaRole = String
  type InfoItem = GeneralTerm
}
import definitions._

sealed trait TptpInput {
  override def toString = tptpToString.tptpInput( this )
}
// how to encode?  thf(someName, type, foo: $tType)
case class TptpFormulaInput( language: String, name: String, role: FormulaRole, formula: HOLFormula, annotations: Option[Annotations] ) extends TptpInput
case class IncludeDirective( fileName: String, formulaSelection: Seq[String] ) extends TptpInput

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
