package gapt.provers.slakoning

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.hol.HOLAtomConst
import gapt.expr.formula.prop.PropAtom
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.logic.Polarity
import gapt.proofs._
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Definition
import gapt.proofs.resolution._
import gapt.utils.NameGenerator

import scala.collection.mutable

object structuralCNF {
  def apply(
    endSequent:        HOLSequent,
    propositional:     Boolean    = false,
    structural:        Boolean    = true,
    bidirectionalDefs: Boolean    = false,
    cse:               Boolean    = false )(
    implicit
    ctx: MutableContext = MutableContext.guess( endSequent ) ): Set[ResolutionProof] = {
    if ( !propositional )
      require( freeVariables( endSequent ).isEmpty, "end-sequent has free variables" )

    onProofs(
      endSequent.map( Sequent() :+ _, _ +: Sequent() ).map( Input ).elements,
      propositional, structural, bidirectionalDefs, cse )
  }

  def onProofs(
    proofs:            Iterable[ResolutionProof],
    propositional:     Boolean                   = false,
    structural:        Boolean                   = true,
    bidirectionalDefs: Boolean                   = false,
    cse:               Boolean                   = false )(
    implicit
    ctx: MutableContext = MutableContext.guess( proofs ) ): Set[ResolutionProof] = {
    val clausifier = new Clausifier( propositional, structural, bidirectionalDefs, cse, ctx, ctx.newNameGenerator )
    if ( cse ) proofs foreach clausifier.analyze
    proofs foreach clausifier.expand
    clausifier.cnf.toSet
  }
}

sealed trait Rule {
  def renameDisjoint( fvs: Set[Var] ): Rule
}
case class PiRule( left: Atom, right: Atom, eigenVars: List[Var], freeVars: Set[Var], concl: HOLSequent ) extends Rule {
  require( eigenVars.toSet.intersect( freeVars ).isEmpty )
  override def renameDisjoint( fvs: Set[Var] ): PiRule =
    Substitution( rename( freeVars ++ eigenVars, fvs ) )( this )
}
object PiRule {
  implicit val closedUnderSub: ClosedUnderSub[PiRule] = ( sub, rule ) =>
    PiRule(
      sub( rule.left ).asInstanceOf[Atom],
      sub( rule.right ).asInstanceOf[Atom],
      rule.eigenVars.map( sub( _ ).asInstanceOf[Var] ),
      freeVariables( sub( rule.freeVars ) ),
      sub( rule.concl ) )
}
case class OrRule( left: Atom, right: Atom, concl: HOLSequent ) extends Rule {
  override def renameDisjoint( fvs: Set[Var] ): OrRule =
    Substitution( rename( freeVariables( concl ), fvs ) )( this )
}
object OrRule {
  implicit val closedUnderSub: ClosedUnderSub[OrRule] = ( sub, rule ) =>
    OrRule(
      sub( rule.left ).asInstanceOf[Atom],
      sub( rule.right ).asInstanceOf[Atom],
      sub( rule.concl ) )
}
case class ExistsRule( premise: Atom, eigenVars: List[Var], freeVars: Set[Var], concl: HOLSequent ) extends Rule {
  require( eigenVars.toSet.intersect( freeVars ).isEmpty )
  override def renameDisjoint( fvs: Set[Var] ): ExistsRule =
    Substitution( rename( freeVariables( premise ), fvs ) )( this )
}
object ExistsRule {
  implicit val closedUnderSub: ClosedUnderSub[ExistsRule] = ( sub, rule ) =>
    ExistsRule(
      sub( rule.premise ).asInstanceOf[Atom],
      rule.eigenVars.map( sub( _ ).asInstanceOf[Var] ),
      freeVariables( sub( rule.freeVars ) ),
      sub( rule.concl ) )
}
case class EndRule( propAtom: PropAtom ) extends Rule {
  override def renameDisjoint( fvs: Set[Var] ): Rule = this
}

object Pi {
  def unapply( e: Expr ): Some[( List[Var], List[Expr], Expr )] =
    e match {
      case All( x, Pi( xs, as, b ) ) =>
        // TODO: rename x
        Some( ( x :: xs, as, b ) )
      case Neg( a ) =>
        Some( ( Nil, a :: Nil, Bottom() ) )
      case Imp( a, Pi( xs, as, b ) ) =>
        Some( ( xs, a :: as, b ) )
      case b =>
        Some( ( Nil, Nil, b ) )
    }
}

class Clausifier(
    propositional: Boolean, structural: Boolean,
    bidirectionalDefs: Boolean, cse: Boolean,
    ctx:     MutableContext,
    nameGen: NameGenerator ) {
  val cnf = mutable.Set[ResolutionProof]()
  val defs = mutable.Map[Expr, HOLAtomConst]()
  val skConsts = mutable.Map[Expr, Const]()
  val rules: mutable.Set[Rule] = mutable.Set()
  val assumptionConsts: mutable.Set[Const] = mutable.Set()

  def mkAbbrevSym() = nameGen.freshWithIndex( "D" )
  def mkIntuitSym() = nameGen.freshWithIndex( "I" )

  val subExprs: mutable.Map[Expr, Int] = mutable.Map()
  val commonSubExprs: mutable.Set[Expr] = mutable.Set()
  def analyze( f: Formula ): Int = {
    subExprs.get( f ) match {
      case Some( compl ) =>
        if ( compl > 1 ) commonSubExprs += f
        compl
      case None =>
        val compl = f match {
          case _: Atom     => 1
          case Neg( a )    => analyze( a )
          case And( a, b ) => analyze( a ) + analyze( b )
          case Or( a, b )  => analyze( a ) + analyze( b )
          case Imp( a, b ) => analyze( a ) + analyze( b )
          case All( _, a ) => 1 + analyze( a )
          case Ex( _, a )  => 1 + analyze( a )
          case _           => 0
        }
        subExprs( f ) = compl
        compl
    }
  }
  def analyze( p: ResolutionProof ): Unit =
    p.conclusion.foreach( analyze )

  def isDefn( p: ResolutionProof ): Boolean = {
    def isDefnPlusAllR( p: ResolutionProof ): Boolean =
      p match {
        case Defn( _, _ )    => true
        case AllR( q, _, _ ) => isDefnPlusAllR( q )
        case _               => false
      }

    p match {
      case ImpR( AndR1( q, _ ), _ ) => isDefnPlusAllR( q )
      case ImpR( AndR2( q, _ ), _ ) => isDefnPlusAllR( q )
      case _                        => false
    }
  }

  def expandAnt( fml: Formula ): Unit =
    expand( Input( Sequent() :+ fml ) )

  def expandSuc( fml: Formula ): Unit = {
    require( freeVariables( fml ).isEmpty )
    val cA = addPredicateDef( fml )
    expand( defnClause( cA, Nil, Polarity.InAntecedent ) )
    assumptionConsts += cA
    rules += EndRule( cA.asInstanceOf[PropAtom] )
  }

  private val alreadyHandledPred = mutable.Set[Const]()

  // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.

  // In each step we simplify the sequents in this set and make them more like clauses.

  // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
  def expand( p: ResolutionProof ): Unit = {
    p.conclusion.zipWithIndex.elements.collectFirst {
      case ( f, i ) if cse && commonSubExprs.contains( f ) && !isDefn( p ) =>
        abbrev( p, i )

      case ( Ex( x, a ), i: Ant ) if !propositional =>
        ExL( p, i, rename( x, freeVariables( p.conclusion ) ) )
      case ( All( x, a ), i: Suc ) if p.conclusion.succedent.size == 1 && !propositional =>
        AllR( p, i, rename( x, freeVariables( p.conclusion ) ) )

      case ( Top(), i: Ant ) => TopL( p, i )
      case ( Bottom(), i: Suc ) => BottomR( p, i )
      case ( Top(), i: Suc ) => return
      case ( Bottom(), i: Ant ) => return

      case ( Neg( a ), i: Suc ) if p.conclusion.succedent.size == 1 => NegR( p, i )

      case ( And( a, b ), i: Ant ) => AndL( p, i )
      case ( Imp( a, b ), i: Suc ) if p.conclusion.succedent.size == 1 => ImpR( p, i )

      case ( And( Top(), _ ), i: Suc ) => AndR2( p, i )
      case ( And( _, Top() ), i: Suc ) => AndR1( p, i )
      case ( Or( _, Bottom() ), i: Ant ) => OrL1( p, i )
      case ( Or( Bottom(), _ ), i: Ant ) => OrL2( p, i )
      case ( Imp( Top(), _ ), i: Ant ) => ImpL2( p, i )

      case ( And( Bottom(), _ ), i: Suc ) => AndR1( p, i )
      case ( And( _, Bottom() ), i: Suc ) => AndR2( p, i )
      case ( Or( Top(), _ ), i: Ant ) => OrL1( p, i )
      case ( Or( _, Top() ), i: Ant ) => OrL2( p, i )
      //      case ( Imp( Bottom(), _ ), i: Ant ) => ImpL1( p, i ) FIXME
      case ( Imp( _, Top() ), i: Ant ) => ImpL2( p, i )

    } match {
      case Some( p_ ) => expand( p_ )
      case None =>
        if ( !p.conclusion.isTaut ) intuit( Factor( p ) )
    }
  }

  def intuit( p: ResolutionProof ): Unit = {
    p.conclusion.zipWithIndex.elements.collectFirst {
      case ( f @ Pi( xs, as, b ), i: Ant ) if xs.nonEmpty || as.nonEmpty =>
        require( xs.distinct == xs ) // TODO
        val ( defIntro, ( const, fvs, pol ) ) = abbrevCore( p, i )
        if ( !alreadyHandledPred( const ) ) {
          alreadyHandledPred += const
          val fvsA = freeVariables( as ).toList
          val fvsB = freeVariables( b ).toList
          val cA = addPredicateDefI( Abs( fvsA, And( as ) ) )
          val cB = addPredicateDefI( Abs( fvsB, b ) )
          expand( defnClause( cA, fvsA, Polarity.InSuccedent ) )
          expand( defnClause( cB, fvsB, Polarity.InAntecedent ) )
          assumptionConsts += cA
          assumptionConsts += cB
          rules += PiRule(
            cA( fvsA ).asInstanceOf[Atom],
            cB( fvsB ).asInstanceOf[Atom],
            xs,
            freeVariables( f ),
            Sequent() :+ const( fvs ).asInstanceOf[Atom] )
        }
        defIntro

      case ( f @ Ex.Block( xs, a ), i: Suc ) if xs.nonEmpty =>
        val ( defIntro, ( const, fvs, pol ) ) = abbrevCore( p, i )
        if ( !alreadyHandledPred( const ) ) {
          alreadyHandledPred += const
          val fvsA = freeVariables( a ).toList
          val cA = addPredicateDefI( Abs( fvsA, a ) )
          expand( defnClause( cA, fvsA, Polarity.InSuccedent ) )
          assumptionConsts += cA
          rules += ExistsRule(
            cA( fvsA ).asInstanceOf[Atom],
            xs,
            freeVariables( f ),
            const( fvs ).asInstanceOf[Atom] +: Sequent() )
        }
        defIntro

      case ( Or( a, b ), i: Suc ) =>
        val ( defIntro, ( const, fvs, pol ) ) = abbrevCore( p, i )
        if ( !alreadyHandledPred( const ) ) {
          alreadyHandledPred += const
          val fvsA = freeVariables( a ).toList
          val fvsB = freeVariables( b ).toList
          val cA = addPredicateDefI( Abs( fvsA, a ) )
          val cB = addPredicateDefI( Abs( fvsB, b ) )
          expand( defnClause( cA, fvsA, Polarity.InSuccedent ) )
          expand( defnClause( cB, fvsB, Polarity.InSuccedent ) )
          assumptionConsts += cA
          assumptionConsts += cB
          rules += OrRule(
            cA( fvsA ).asInstanceOf[Atom],
            cB( fvsB ).asInstanceOf[Atom],
            const( fvs ).asInstanceOf[Atom] +: Sequent() )
        }
        defIntro

    } match {
      case Some( p_ ) => intuit( Factor( p_ ) )
      case None =>
        if ( !p.conclusion.isTaut ) split( Factor( p ) )
    }
  }

  // Then we simplify the connectives which correspond to nested conjunctions, e.g. (:- a&b) turns into (:- a) and (:- b).
  // In order to combat exponential blow-up, we do something special if there are two or more such elements:
  // we introduce a definition for the first one.
  def split( p: ResolutionProof ): Unit = {
    p.conclusion.zipWithIndex.elements.collectFirst {
      case ( Ex( _, _ ) | Imp( _, _ ) | All( _, _ ) | Neg( _ ), i: Suc ) => i
    } match {
      case Some( i ) => return expand( abbrev( p, i ) )
      case _         =>
    }
    p.conclusion.zipWithIndex.elements collect {
      case ( And( a, b ), i: Suc ) => i
      case ( Or( a, b ), i: Ant )  => i
      case ( Imp( a, b ), i: Ant ) => i
    } match {
      case splits if structural && ( splits.size > 1 || ( splits.size == 1 && p.conclusion.size > 3 ) ) =>
        expand( abbrev( p, splits.head ) )
      case Seq( i, _* ) => splitAt( p, i )
      case Seq()        => cnf += p
    }
  }

  def splitAt( p: ResolutionProof, i: SequentIndex ): Unit =
    ( p.conclusion( i ), i ) match {
      case ( f, _ ) if cse && commonSubExprs( f ) && !isDefn( p ) => expand( p )
      case ( And( a, b ), i: Suc ) =>
        splitAt( AndR1( p, i ), p.conclusion.indices.last )
        splitAt( AndR2( p, i ), p.conclusion.indices.last )
      case ( Or( a, b ), i: Ant ) =>
        splitAt( OrL1( p, i ), Ant( 0 ) )
        splitAt( OrL2( p, i ), Ant( 0 ) )
      case _ => expand( p )
    }

  // Here, we replace the formula at index i with a definition, and continue with
  // both the abbreviated sequent, and (the necessary part of) the definition.
  def abbrev( p: ResolutionProof, i: SequentIndex ): DefIntro = {
    val ( defIntro, ( const, fvs, pol ) ) = abbrevCore( p, i )
    expandDef( const, fvs, i.polarity )
    defIntro
  }

  def abbrevCore( p: ResolutionProof, i: SequentIndex ): ( DefIntro, ( HOLAtomConst, List[Var], Polarity ) ) = {
    val f = p.conclusion( i )
    val fvs = freeVariables( f ).toList
    val definedFormula = Abs( fvs, f )
    val const = defs.getOrElseUpdate( definedFormula, addPredicateDef( definedFormula ) )
    DefIntro( p, i, Definition( const, definedFormula ), fvs ) -> ( const, fvs, i.polarity )
  }

  def addPredicateDef( absFml: Expr ): HOLAtomConst =
    ctx.addDefinition( absFml, mkAbbrevSym(), reuse = false ).asInstanceOf[HOLAtomConst]

  def addPredicateDefI( absFml: Expr ): HOLAtomConst =
    ctx.addDefinition( absFml, mkIntuitSym(), reuse = false ).asInstanceOf[HOLAtomConst]

  def defnClause( const: HOLAtomConst, fvs: List[Var], pol: Polarity ): ResolutionProof = {
    val defn = fvs.foldLeft[ResolutionProof]( Defn( const, ctx.definition( const ).get ) )( AllR( _, Suc( 0 ), _ ) )
    ImpR( if ( pol.inAnt ) AndR2( defn, Suc( 0 ) ) else AndR1( defn, Suc( 0 ) ), Suc( 0 ) )
  }

  val alreadyDefined: mutable.Set[( Const, Polarity )] = mutable.Set()
  def expandDef( const: HOLAtomConst, fvs: List[Var], pol: Polarity ): Unit = {
    if ( alreadyDefined( const -> pol ) && ( !bidirectionalDefs || alreadyDefined( const -> !pol ) ) ) return
    if ( pol.inAnt || bidirectionalDefs ) {
      alreadyDefined += ( const -> Polarity.InAntecedent )
      expand( defnClause( const, fvs, Polarity.InAntecedent ) )
    }
    if ( pol.inSuc || bidirectionalDefs ) {
      alreadyDefined += ( const -> Polarity.InSuccedent )
      expand( defnClause( const, fvs, Polarity.InSuccedent ) )
    }
  }

}
