package at.logic.gapt.formats.tptp2

import at.logic.gapt.expr._
import org.parboiled2._

import scala.util.{ Failure, Success }

class TptpParser( val input: ParserInput ) extends Parser {
  import CharPredicate._

  def Ws = rule { quiet( ( ( anyOf( " \t \n" ) | comment ).* ) ) }
  def Comma = rule { "," ~ Ws }

  def TPTP_file: Rule1[Seq[TptpInput]] = rule { Ws ~ TPTP_input.* ~ EOI }

  def TPTP_input = rule { annotated_formula | include }

  def annotated_formula = rule { thf_annotated | tff_annotated | fof_annotated | cnf_annotated | tpi_annotated }
  def tpi_annotated = rule { "\0" ~ push( null ) } // FIXME
  def thf_annotated = rule { "thf(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ thf_formula ~ annotations ~ ")." ~ Ws ~> ( ThfFormula( _, _, _, _ ) ) }
  def tff_annotated = rule { "\0" ~ push( null ) } // FIXME
  def fof_annotated = rule { "fof(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ fof_formula ~ annotations ~ ")." ~ Ws ~> ( FofFormula( _, _, _, _ ) ) }
  def cnf_annotated = rule { "cnf(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ cnf_formula ~ annotations ~ ")." ~ Ws ~> ( CnfFormula( _, _, _, _ ) ) }
  def formula_role = rule {
    ( ( "axiom" ~ push( Axiom ) ) | ( "hypothesis" ~ push( Hypothesis ) ) | ( "definition" ~ push( Definition ) ) | ( "assumption" ~ push( Assumption ) ) |
      ( "lemma" ~ push( Lemma ) ) | ( "theorem" ~ push( Theorem ) ) | ( "corollary" ~ push( Corollary ) ) | ( "conjecture" ~ push( Conjecture ) ) |
      ( "negated_conjecture" ~ push( NegatedConjecture ) ) | ( "plain" ~ push( Plain ) ) | ( "type" ~ push( Type ) ) |
      ( "fi_domain" ~ push( FiDomain ) ) | ( "fi_functors" ~ push( FiFunctors ) ) | ( "fi_predicates" ~ push( FiPredicates ) ) | ( "unknown" ~ push( Unknown ) ) ) ~ Ws
  }
  def annotations = rule { ( Comma ~ source ~ optional_info ~> ( ( s, o ) => Annotations( s, o ) ) ).? }

  def thf_formula: Rule1[HOLFormula] = rule { "" ~ push( Top() ) }

  def fof_formula = rule { ( fof_logic_formula ~> ( _.asInstanceOf[FOLFormula] ) ) | fof_sequent }
  def fof_logic_formula: Rule1[HOLFormula] = rule { fof_binary_formula | fof_unitary_formula }
  def fof_binary_formula = rule { fof_binary_nonassoc | fof_binary_assoc }
  def fof_binary_nonassoc = rule { fof_unitary_formula ~ binary_connective ~ fof_unitary_formula ~> ( ( a, c, b ) => c( a, b ) ) }
  def fof_binary_assoc = rule {
    fof_unitary_formula ~ ( assoc_connective ~ fof_unitary_formula ~> ( ( _, _ ) ) ).* ~> ( ( first, rest ) =>
      rest.foldLeft( first ) { case ( acc, ( conn, formula ) ) => conn( acc, formula ) } )
  }
  def fof_unitary_formula: Rule1[HOLFormula] = rule { fof_quantified_formula | fof_unary_formula | atomic_formula | "(" ~ Ws ~ fof_logic_formula ~ ")" ~ Ws }
  def fof_quantified_formula = rule { fol_quantifier ~ "[" ~ Ws ~ fof_variable_list ~ "]" ~ Ws ~ ":" ~ Ws ~ fof_unitary_formula ~> ( ( q: QuantifierHelper, vs, m ) => q.Block( vs, m ) ) }
  def fof_variable_list = rule { variable.+.separatedBy( Comma ) }
  def fof_unary_formula = rule { ( unary_connective ~ fof_unitary_formula ~> ( ( c, f ) => c( f ) ) ) | fol_infix_unary }

  def fof_sequent = rule { "\0" ~ push( Top() ) } // FIXME

  def cnf_formula = rule { fof_formula } // atomic_formula can be $true or $false and clashes with our concept of clauses

  def atomic_formula = rule { defined_atomic_formula | plain_atomic_formula } // FIXME
  def plain_atomic_formula = rule { atomic_word ~ ( "(" ~ Ws ~ arguments ~ ")" ~ Ws ).? ~> ( ( p, as ) => mkAtom( p, as.getOrElse( Seq() ) ) ) }
  def defined_atomic_formula = rule { defined_plain_formula | defined_infix_formula } // FIXME
  def defined_plain_formula = rule { defined_prop } // FIXME
  def defined_prop = rule { ( "$true" ~ push( Top() ) | "$false" ~ push( Bottom() ) ) ~ Ws }
  def defined_infix_formula = rule { term ~ "=" ~ Ws ~ term ~> ( Eq( _, _ ) ) }

  def fol_infix_unary = rule { term ~ "!=" ~ Ws ~ term ~> ( _ !== _ ) }

  def fol_quantifier = rule { ( "!" ~ push( at.logic.gapt.expr.All ) | "?" ~ push( Ex ) ) ~ Ws }
  def binary_connective = rule {
    ( ( "<=>" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => a <-> b ) ) |
      ( "=>" ~ push( Imp( _: LambdaExpression, _: LambdaExpression ) ) ) |
      ( "<=" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => Imp( b, a ) ) ) |
      ( "<~>" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a <-> b ) ) ) |
      ( "~|" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a | b ) ) ) |
      ( "~&" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a & b ) ) ) ) ~ Ws
  }
  def assoc_connective = rule { ( "|" ~ push( Or ) | "&" ~ push( And ) ) ~ Ws }
  def unary_connective = rule { "~" ~ push( Neg ) ~ Ws }

  def term: Rule1[LambdaExpression] = rule { function_term | variable }
  def function_term = rule { ( atomic_word | atomic_defined_word | atomic_system_word ) ~ ( "(" ~ Ws ~ term.+.separatedBy( Comma ) ~ ")" ~ Ws ).? ~> ( ( hd, as ) => mkTerm( hd, as.getOrElse( Seq() ) ) ) }
  def variable = rule { capture( upper_word ) ~ Ws ~> ( FOLVar( _: String ) ) }
  def arguments = rule { term.+.separatedBy( Comma ) }

  def source: Rule1[Source] = rule { dag_source | internal_source | external_source }
  def dag_source = rule { ( name ~> ( DagSource( _ ) ) ) | inference_record }
  def inference_record = rule { "inference(" ~ Ws ~ atomic_word ~ Comma ~ useful_info ~ Comma ~ "[" ~ Ws ~ parent_info.*.separatedBy( Comma ) ~ "]" ~ Ws ~ ")" ~ Ws ~> ( InferenceRecord( _, _, _ ) ) }
  def parent_info = rule { source ~ parent_details ~> ( ParentInfo( _, _ ) ) }
  def parent_details = rule { ( ":" ~ Ws ~ general_list ).? ~> ( _.getOrElse( Seq() ) ) }

  def internal_source = rule { "introduced(" ~ Ws ~ intro_type ~ optional_info ~ ")" ~ Ws ~> ( InternalSource( _, _ ) ) }
  def intro_type = rule { atomic_word }

  def external_source = rule { file_source | theory | creator_source }
  def file_source = rule { "file(" ~ Ws ~ file_name ~ file_info ~ ")" ~ Ws ~> ( FileSource( _, _ ) ) }
  def file_info = rule { ( Comma ~ name ).? }
  def theory = rule { "theory(" ~ Ws ~ theory_name ~ optional_info ~ ")" ~ Ws ~> ( Theory( _, _ ) ) }
  def theory_name = rule { atomic_word }
  def creator_source = rule { "creator(" ~ Ws ~ creator_name ~ optional_info ~ ")" ~ Ws ~> ( CreatorSource( _, _ ) ) }
  def creator_name = rule { atomic_word }

  def optional_info = rule { ( Comma ~ useful_info ).? ~> ( ( oi: Option[Seq[LambdaExpression]] ) => oi.getOrElse( Seq() ) ) }
  def useful_info = rule { general_list }

  def include = rule { "include(" ~ Ws ~ file_name ~ formula_selection ~ ")." ~ Ws ~> ( IncludeDirective( _, _ ) ) }
  def formula_selection = rule { ( "," ~ Ws ~ "[" ~ name.*.separatedBy( Comma ) ~ "]" ~ Ws ).? ~> ( _.getOrElse( Seq() ) ) }

  def mkTerm( sym: String, args: Seq[LambdaExpression] ): LambdaExpression =
    Apps( Const( sym, FunctionType( Ti, args.map( _.exptype ) ) ), args )
  def mkAtom( sym: String, args: Seq[LambdaExpression] ): HOLAtom =
    Apps( Const( sym, FunctionType( To, args.map( _.exptype ) ) ), args ).asInstanceOf[HOLAtom]

  def general_list: Rule1[Seq[LambdaExpression]] = rule { "[" ~ Ws ~ general_term.*.separatedBy( Comma ) ~ "]" ~ Ws }
  def general_terms = rule { general_term.+.separatedBy( Comma ) }
  def general_term: Rule1[LambdaExpression] = rule {
    general_data ~ ( ":" ~ general_term ).? ~> ( ( d, to ) => to.fold( d )( t => mkTerm( ":", Seq( d, t ) ) ) ) |
      general_list ~> ( mkTerm( "[]", _: Seq[LambdaExpression] ) )
  }
  def general_data: Rule1[LambdaExpression] = rule {
    ( atomic_word ~> ( FOLConst( _ ) ) ) | general_function |
      variable | ( number ~> ( FOLConst( _ ) ) ) | ( distinct_object ~> ( FOLConst( _ ) ) ) |
      formula_data
  }
  def general_function = rule { atomic_word ~ "(" ~ Ws ~ general_terms ~ ")" ~ Ws ~> mkTerm _ }
  def formula_data = rule { atomic_defined_word ~ "(" ~ Ws ~ general_terms ~ ")" ~ Ws ~> mkTerm _ }

  // DEVIATION: Vampire uses defined words such as $spl0, so we allow atomic_{system,defined}_word as well here
  def name: Rule1[String] = rule { atomic_word | atomic_system_word | atomic_defined_word | integer }
  def atomic_word = rule { ( capture( lower_word ) ~ Ws ) | single_quoted }
  def atomic_defined_word = rule { capture( '$' ~ lower_word ) ~ Ws }
  def atomic_system_word = rule { capture( "$$" ~ lower_word ) ~ Ws }

  def number = rule { integer /* TODO: | rational | real */ }

  def file_name = rule { single_quoted }

  def comment = rule { comment_line | comment_block }
  // DEVIATION: Axioms/PUZ005-0.ax uses tab in comment
  def comment_line = rule { '%' ~ CharPredicate( 32.toChar to 126.toChar, '\t' ).* }
  def comment_block = rule { "/*" ~ not_star_slash ~ oneOrMore( "*" ) ~ "/" }
  def not_star_slash = rule { ( noneOf( "*" ).* ~ oneOrMore( "*" ) ~ noneOf( "/*" ) ).* ~ noneOf( "*" ).* }

  def single_quoted = rule { '\'' ~ sg_char.+ ~ '\'' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  def distinct_object = rule { '"' ~ do_char.* ~ '"' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  def alpha_numeric = rule { UpperAlpha | LowerAlpha | Digit | "_" }
  def upper_word = rule { UpperAlpha ~ alpha_numeric.* }
  def lower_word = rule { LowerAlpha ~ alpha_numeric.* }

  def integer = rule { capture( CharPredicate( "+-" ).? ~ ( "0" | ( Digit19 ~ Digit.* ) ) ) ~ Ws }

  def do_char = rule { capture( CharPredicate( ']' to '~', ' ' to '&', '(' to '[' ) ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\\"" ~ push( "\"" ) ) }
  def sg_char = rule { capture( CharPredicate( ']' to '~', ' ' to '&', '(' to '[' ) ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\'" ~ push( "'" ) ) }
}

object TptpParser {
  def parseString( input: String, sourceName: String = "<string>" ): Seq[TptpInput] = {
    val parser = new TptpParser( input )
    parser.TPTP_file.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( s"Parse error in $sourceName:\n" +
          parser.formatError( error, new ErrorFormatter( showTraces = true ) ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value
    }
  }

  def parseFile( fileName: String ): Seq[TptpInput] =
    parseString( io.Source.fromFile( fileName ).mkString, fileName )
  def loadFile( fileName: String ): Seq[TptpInput] =
    resolveIncludes( Seq( IncludeDirective( fileName, Seq() ) ), parseFile )

  def main( args: Array[String] ): Unit =
    print( loadFile( args.head ).mkString )
}
