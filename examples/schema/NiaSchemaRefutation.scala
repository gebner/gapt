package gapt.examples

import gapt.expr._
import gapt.proofs.ceres._
import gapt.proofs.gaptic._

object NiaSchemaRefutation extends TacticsProof( NiaSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "omega" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  val sequentForm = Viperize( le"omegaSFAF n" )
}
