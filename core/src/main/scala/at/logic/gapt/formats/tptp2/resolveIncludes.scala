package at.logic.gapt.formats.tptp2

import at.logic.gapt.formats.tptp2.definitions.TptpFile

object resolveIncludes {
  def apply( tptpFile: TptpFile, resolver: String => TptpFile ): TptpFile =
    tptpFile flatMap {
      case IncludeDirective( fileName, formulaSelection ) =>
        apply( resolver( fileName ), resolver )
      case input => Seq( input )
    }

}
