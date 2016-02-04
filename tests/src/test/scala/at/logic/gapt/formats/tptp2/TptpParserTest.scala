package at.logic.gapt.formats.tptp2

import org.specs2.mutable.Specification

class TptpParserTest extends Specification {

  def loadTPTP( fileName: String ) =
    resolveIncludes(
      Seq( IncludeDirective( fileName, Seq() ) ),
      fileName => TptpParser.parseString( io.Source.fromInputStream(
        getClass.getClassLoader.getResourceAsStream( fileName )
      ).mkString, fileName )
    )

  "gra014p1" in {
    loadTPTP( "GRA014+1.p" )
    ok
  }

  "grp069m1" in {
//    skipped
    TptpParser.loadFile( "/home/gebner/.nix-profile/share/tptp/Problems/GRP/GRP069-1.p" )
    ok
  }

}
