package gapt.proofs.expansion

import gapt.expr._
import gapt.proofs.lk.{ LKProof, LKToExpansionProof }

/**
 * Deskolemization of expansion trees.
 *
 * We first gather the skolem terms in a given [[ExpansionProof]] from the [[ETSkolemQuantifier]]s.
 * Then replace each [[ETSkolemQuantifier]] by [[ETStrongQuantifier]], and each skolem term within, by a fresh eigenvariable.
 */
object deskolemizeET {
  def apply( lkProof: LKProof ): LKProof =
    ExpansionProofToLK( deskolemizeET( LKToExpansionProof( lkProof ) ) ).right.get

  def apply( expansionProof: ExpansionProof, removeCongruences: Boolean = true ): ExpansionProof = {
    val woCongrs = if ( removeCongruences ) removeSkolemCongruences( expansionProof ) else expansionProof
    val skolemsAboveCuts = eliminateMerges( moveSkolemNodesToCuts( woCongrs ) )
    val deskolemized = replaceByEigenvariables( skolemsAboveCuts )
    eliminateCutsET( deskolemized )
  }

  def replaceByEigenvariables( expansionProof: ExpansionProof ): ExpansionProof = {
    val nameGenerator = rename.awayFrom( containedNames( expansionProof ) )
    val skolemTerms = expansionProof.subProofs.collect { case ETSkolemQuantifier( _, skT, _, _ ) => skT }
    val repl = skolemTerms.map { t => ( t, Var( nameGenerator.fresh( "v" ), t.ty ) ) }.toMap

    ExpansionProof( replace( expansionProof.expansionSequent, repl ) )
  }

  def replace( es: ExpansionSequent, repl: PartialFunction[Expr, Expr] ): ExpansionSequent =
    for ( e <- es ) yield replace( e, repl )

  def replace( et: ExpansionTree, repl: PartialFunction[Expr, Expr] ): ExpansionTree = et match {
    case ETMerge( child1, child2 )   => ETMerge( replace( child1, repl ), replace( child2, repl ) )

    case ETWeakening( formula, pol ) => ETWeakening( TermReplacement( formula, repl ), pol )
    case ETAtom( atom, pol )         => ETAtom( TermReplacement( atom, repl ), pol )
    case ETDefinition( sh, ch ) =>
      ETDefinition( TermReplacement( sh, repl ), replace( ch, repl ) )

    case ETTop( _ ) | ETBottom( _ ) => et
    case ETNeg( child )             => ETNeg( replace( child, repl ) )
    case ETAnd( child1, child2 )    => ETAnd( replace( child1, repl ), replace( child2, repl ) )
    case ETOr( child1, child2 )     => ETOr( replace( child1, repl ), replace( child2, repl ) )
    case ETImp( child1, child2 )    => ETImp( replace( child1, repl ), replace( child2, repl ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        TermReplacement( shallow, repl ),
        instances.map {
          case ( selectedTerm, child ) =>
            ( TermReplacement( selectedTerm, repl ), replace( child, repl ) )
        } )
    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], replace( child, repl ) )
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( skolemTerm, repl ).asInstanceOf[Var],
        replace( child, repl ) )
  }
}

