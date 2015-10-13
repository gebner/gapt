
/*
 * ReductiveCutElim.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant, Sequent, SequentIndex }
import at.logic.gapt.prooftool.prooftool

class ReductiveCutElimException( msg: String ) extends Exception( msg )

/**
 * This object implements a version of Gentzen's cut-elimination
 * proof for our sequent calculus LK. For details, please
 * refer to the documentation of the apply methods.
 */

object ReductiveCutElimination {
  // This list stores a list of subproofs that are reduced
  // during the run of the algorithm.
  private var proofList: List[LKProof] = Nil
  private var steps = false

  /**
   * After calling apply with steps = true, the list of
   * proofs arising during cut-elimination can be obtained
   * from this method.
   *
   * @return The list of proofs arising during cut-elimination
   * after apply() has been called. Nil otherwise.
   */
  def proofs = proofList
  def proofs_=( plist: List[LKProof] ) = proofList = plist

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof parameterized by a strategy given by pred_cut and
   * pred_done.
   *
   * The method traverses an LKProof recursively from the bottom
   * up. When it reaches a cut, the method calls pred_cut(global, sub),
   * where global is complete proof under consideration, while sub
   * is the subproof of global ending in the cut. If this call returns
   * true, the cut is reduced using the usual Gentzen cut-elimination
   * rules. If the call returns false, the traversion continues.
   *
   * After every application of a reduction, pred_done(global) is called.
   * If it returns true, the algorithm terminates, returning the current proof.
   * If it returns false, the algorithm continues to traverse the proof.
   *
   * This means that pred_cut and pred_done allow the definition of a (not necessarily
   * terminating!) cut-elimination strategy. A standard implementation (reducing
   * left-uppermost cuts until the proof is cut-free) is provided by another
   * apply method in this class.
   *
   * Note: We assume that proof is regular, i.e. that an eigenvariable
   * of a quantifier rule in proof is used by exactly one such quantifier rule.
   * Further regularization is done during cut-elimination whenever necessary.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param _steps Collect the list of subproofs arising during cut-elimination.
   * This list can be obtained by the proofs method.
   * @param pred_done A predicate deciding when to terminate the algorithm.
   * @param pred_cut A predicate deciding whether or not to reduce a cut encountered
   * when traversing the proof.
   *
   * @return The proof as it is after pred_done returns true.
   */
  def apply( proof: LKProof, _steps: Boolean, pred_done: LKProof => Boolean, pred_cut: ( LKProof, LKProof ) => Boolean ): LKProof = {
    steps = _steps

    proofList = proof :: Nil
    // var pr = regularize(proof)
    var pr = proof
    do {
      def pred( local: LKProof ) = pred_cut( pr, local )
      val p = cutElim( pr )( pred )
      pr = cleanStructuralRules( p )
      if ( steps ) proofList = proofList ::: ( pr :: Nil )
    } while ( !pred_done( pr ) && !isCutFree( pr ) )
    if ( !steps ) proofList = proofList ::: ( pr :: Nil )
    pr
  }

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param steps Collect the list of subproofs arising during cut-elimination.
   * @return The cut-free proof.
   */
  def apply( proof: LKProof, steps: Boolean = false ) = eliminateAllByUppermost( proof, steps )

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param steps Collect the list of subproofs arising during cut-elimination.
   * @return The cut-free proof.
   */
  def eliminateAllByUppermost( proof: LKProof, steps: Boolean ): LKProof =
    apply( proof, steps, { x => false },
      { ( _, cut ) =>
        cut match {
          case CutRule( leftSubProof, _, rightSubProof, _ ) =>
            isCutFree( leftSubProof ) && isCutFree( rightSubProof )
        }
      } )

  /**
   * This method checks whether a proof is cut-free.
   *
   * @param proof The proof to check for cut-freeness.
   * @return True if proof does not contain the cut rule, False otherwise.
   */
  def isCutFree( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ )         => true
    case UnaryLKProof( _, subProof ) => isCutFree( subProof )
    case p: CutRule                  => false
    case BinaryLKProof( _, leftSubProof, rightSubProof ) =>
      isCutFree( leftSubProof ) && isCutFree( rightSubProof )
  }

  // Implements the Gentzen cut-reduction rules.
  private def cutElim( proof: LKProof )( implicit pred: LKProof => Boolean ): LKProof = proof match {
    case InitialSequent( _ ) =>
      proof

    case WeakeningLeftRule( subProof, formula ) =>
      WeakeningLeftRule( cutElim( subProof ), formula )

    case WeakeningRightRule( subProof, formula ) =>
      WeakeningRightRule( cutElim( subProof ), formula )

    case ContractionLeftRule( subProof, _, _ ) =>
      ContractionLeftRule( cutElim( subProof ), proof.mainFormulas.head )

    case ContractionRightRule( subProof, _, _ ) =>
      ContractionRightRule( cutElim( subProof ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      AndRightRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head )

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule( cutElim( subProof ), proof.mainFormulas.head )

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      OrLeftRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head )

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule( cutElim( subProof ), proof.mainFormulas.head )

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      ImpLeftRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head )

    case ImpRightRule( subProof, _, _ ) =>
      ImpRightRule( cutElim( subProof ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ ) =>
      NegLeftRule( cutElim( subProof ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ ) =>
      NegRightRule( cutElim( subProof ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ ) =>
      ForallLeftRule( cutElim( subProof ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, eigen, _ ) =>
      ForallRightRule( cutElim( subProof ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      ExistsLeftRule( cutElim( subProof ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      ExistsRightRule( cutElim( subProof ), proof.mainFormulas.head, term )

    case EqualityLeftRule( subProof, _, _, _ ) =>
      EqualityLeftRule( cutElim( subProof ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case EqualityRightRule( subProof, _, _, _ ) =>
      EqualityRightRule( cutElim( subProof ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case cut @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      if ( pred( proof ) )
        reduceCut( cut )
      else
        CutRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.auxFormulas.head.head )
  }

  private def reduceCut( cut: CutRule ): LKProof = {
    val reduced = reduceGrade( cut.leftSubProof, cut.aux1, cut.rightSubProof, cut.aux2 )
    require(
      reduced.endSequent multiSetEquals cut.endSequent,
      s"reduceCut(${cut.leftSubProof.longName}, ${cut.rightSubProof.longName}) changed the end-sequent"
    )
    reduced
  }

  // Grade reduction rules:
  private def reduceGrade( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex ): LKProof =
    ( left, right ) match {

      case ( LogicalAxiom( _ ), _ ) => right

      case ( _, LogicalAxiom( _ ) ) => left

      case ( ReflexivityAxiom( s ), TheoryAxiom( sequent ) ) =>
        TheoryAxiom( sequent.delete( aux2 ) )

      case ( ReflexivityAxiom( s ), right: EqualityRule ) if right.mainEqIndex == aux2 =>
        CutRule( left, aux1, right.subProof, right.getOccConnector.parents( aux2 ).head )

      case ( ReflexivityAxiom( s ), right @ EqualityLeftRule( subProof, eq, a, pos ) ) if right.mainIndex == aux2 =>
        val cut = CutRule(
          EqualityRightRule( WeakeningLeftRule( left, subProof.conclusion( eq ) ), Ant( 0 ), Suc( 0 ), pos ), Suc( 0 ),
          subProof, a
        )
        ContractionLeftRule( cut, cut.getLeftOccConnector.children( Ant( 0 ) ).head, cut.getRightOccConnector.children( eq ).head )

      case ( TopAxiom, WeakeningLeftRule( subProof, Top() ) ) if right.mainIndices.head == aux2 =>
        subProof

      case ( WeakeningRightRule( subProof, Bottom() ), BottomAxiom ) if left.mainIndices.head == aux1 =>
        subProof

      case ( TheoryAxiom( leftSequent ), TheoryAxiom( rightSequent ) ) =>
        TheoryAxiom( leftSequent.delete( aux1 ) ++ rightSequent.delete( aux2 ) )

      case ( l @ WeakeningRightRule( subProof, main ), r ) if l.mainIndices.head == aux1 => // The left cut formula is introduced by weakening
        WeakeningMacroRule( subProof, subProof.endSequent ++ r.endSequent )

      case ( l, r @ WeakeningLeftRule( subProof, main ) ) if aux2 == right.mainIndices.head => // The right cut formula is introduced by weakening
        WeakeningMacroRule( subProof, l.endSequent.antecedent, l.endSequent.succedent )

      case ( AndRightRule( llSubProof, a1, lrSubProof, a2 ), AndLeftRule( rSubProof, a3, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lrSubProof, a2, rSubProof, a4 )
        val o = tmp.getRightOccConnector
        CutRule( llSubProof, a1, tmp, o.children( a3 ).head )

      case ( OrRightRule( lSubProof, a1, a2 ), OrLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftOccConnector
        CutRule( tmp, o.children( a2 ).head, rrSubProof, a4 )

      case ( ImpRightRule( lSubProof, a1, a2 ), ImpLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftOccConnector
        CutRule( tmp, o.children( a2 ).head, rrSubProof, a4 )

      case ( NegRightRule( lSubProof, a1 ), NegLeftRule( rSubProof, a2 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        CutRule( rSubProof, a2, lSubProof, a1 )

      case ( ForallRightRule( lSubProof, a1, eigen, _ ), ForallLeftRule( rSubProof, a2, f, term, _ ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val lSubProofNew = applySubstitution( Substitution( eigen, term ) )( lSubProof )
        CutRule( lSubProofNew, rSubProof, right.auxFormulas.head.head )

      case ( ExistsRightRule( lSubProof, a2, f, term, _ ), ExistsLeftRule( rSubProof, a1, eigen, _ ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val rSubProofNew = applySubstitution( Substitution( eigen, term ) )( rSubProof )
        CutRule( lSubProof, rSubProofNew, left.auxFormulas.head.head )

      case ( DefinitionRightRule( lSubProof, a1, main1 ), DefinitionLeftRule( rSubProof, a2, main2 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        CutRule( lSubProof, a1, rSubProof, a2 )

//      case ( left @ EqualityRightRule( lSubProof, eq, a, pos ), right: EqualityRule )
//        if left.mainIndex == aux1 && right.mainEqIndex == aux2 =>
//        val cut =
//          CutRule( lSubProof, a,
//            EqualityLeftRule(
//              WeakeningLeftRule( right, lSubProof.conclusion( eq ) ),
//              Ant( 0 ), aux2 + 1, pos
//            ), Ant( 0 ) )
//        ContractionLeftRule( cut, cut.getLeftOccConnector.children( eq ).head, cut.getRightOccConnector.children( Ant( 1 ) ).head )

      case ( left @ EqualityRightRule( lSubProof, eq, a, pos ), right: EqualityRule )
        if left.mainIndex == aux1 && right.mainEqIndex == aux2 && (right.leftToRight != (pos.head == 2)) =>
        val cut =
          CutRule( lSubProof, a,
            EqualityLeftRule(
              WeakeningLeftRule( right, lSubProof.conclusion( eq ) ),
              Ant( 0 ), aux2 + 1, pos
            ), Ant( 0 ) )
        ContractionLeftRule( cut, cut.getLeftOccConnector.children( eq ).head, cut.getRightOccConnector.children( Ant( 1 ) ).head )

      case ( left: EqualityRightRule, right @ EqualityLeftRule( rSubProof, eq, a, pos ) ) if left.mainIndex == aux1 && right.mainIndex == aux2 =>
        val cut = CutRule(
          EqualityRightRule(
            WeakeningLeftRule( left, rSubProof.conclusion( eq ) ),
            Ant( 0 ), left.mainIndex, pos
          ), left.mainIndex,
          rSubProof, a
        )
        ContractionLeftRule( cut, cut.getLeftOccConnector.children( Ant( 0 ) ).head, cut.getRightOccConnector.children( eq ).head )

      case _ => reduceRankLeft( left, aux1, right, aux2 )
    }

  private def reduceRankLeft( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex ): LKProof = {

    left match {
      case l @ WeakeningLeftRule( subProof, main ) =>
        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )

        WeakeningLeftRule( cutSub, main )

      case l @ WeakeningRightRule( subProof, main ) =>
        WeakeningRightRule( CutRule( subProof, l.getOccConnector.parents( aux1 ).head, right, aux2 ), main )

      case l @ ContractionLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )

        val ( a1New, a2New ) = ( cutSub.getLeftOccConnector.children( a1 ).head, cutSub.getLeftOccConnector.children( a2 ).head )
        ContractionLeftRule( cutSub, a1New, a2New )

      case l @ ContractionRightRule( subProof, a1, a2 ) =>
        if ( l.mainIndices.head == aux1 ) { // The left cut formula is the main formula of the contraction: Duplicate right proof
          val rReg = regularize( right )
          val tmp = CutRule( subProof, a1, right, aux2 )
          val tmp2 = CutRule( tmp, tmp.getLeftOccConnector.children( a2 ).head, rReg, aux2 )
          val tmp3 = ContractionMacroRule( tmp2, left.endSequent.delete( aux1 ) ++ right.endSequent.delete( aux2 ) )
          regularize( tmp3 )
        } else { // The contraction operates on the context: Swap the inferences
          val aux1Sub = l.getOccConnector.parents( aux1 ).head
          val cutSub = CutRule( subProof, aux1Sub, right, aux2 )
          val ( a1New, a2New ) = ( cutSub.getLeftOccConnector.children( a1 ).head, cutSub.getLeftOccConnector.children( a2 ).head )
          ContractionRightRule( cutSub, a1New, a2New )
        }

      //Following line is redundant when eliminating uppermost cut
      case l @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftOccConnector.parents( aux1 )
        val aux1Right = l.getRightOccConnector.parents( aux1 )

        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            CutRule( cutSub, cutSub.getLeftOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            CutRule( leftSubProof, a1, cutSub, cutSub.getLeftOccConnector.children( a2 ).head )
        }

      case l @ DefinitionLeftRule( subProof, a, main ) =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        DefinitionLeftRule( cutSub, aNew, main )

      case l @ DefinitionRightRule( subProof, a, main ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        DefinitionRightRule( cutSub, aNew, main )

      case l @ AndLeftRule( subProof, a1, a2 ) =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftOccConnector.children( a1 ).head, cutSub.getLeftOccConnector.children( a2 ).head )
        AndLeftRule( cutSub, a1New, a2New )

      case l @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) if left.mainIndices.head != aux1 =>
        val aux1Left = l.getLeftOccConnector.parents( aux1 )
        val aux1Right = l.getRightOccConnector.parents( aux1 )

        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            AndRightRule( cutSub, cutSub.getLeftOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            AndRightRule( leftSubProof, a1, cutSub, cutSub.getLeftOccConnector.children( a2 ).head )
        }

      case l @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftOccConnector.parents( aux1 )
        val aux1Right = l.getRightOccConnector.parents( aux1 )

        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            OrLeftRule( cutSub, cutSub.getLeftOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            OrLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftOccConnector.children( a2 ).head )
        }

      case l @ OrRightRule( subProof, a1, a2 ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftOccConnector.children( a1 ).head, cutSub.getLeftOccConnector.children( a2 ).head )
        OrRightRule( cutSub, a1New, a2New )

      case l @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftOccConnector.parents( aux1 )
        val aux1Right = l.getRightOccConnector.parents( aux1 )

        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            ImpLeftRule( cutSub, cutSub.getLeftOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftOccConnector.children( a2 ).head )
        }

      case l @ ImpRightRule( subProof, a1, a2 ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftOccConnector.children( a1 ).head, cutSub.getLeftOccConnector.children( a2 ).head )
        ImpRightRule( cutSub, a1New, a2New )

      case l @ NegLeftRule( subProof, a ) =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        NegLeftRule( cutSub, aNew )

      case l @ NegRightRule( subProof, a ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        NegRightRule( cutSub, aNew )

      case l @ ForallLeftRule( subProof, a, f, term, quant ) =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        ForallLeftRule( cutSub, aNew, f, term, quant )

      case l @ ForallRightRule( subProof, a, eigen, quant ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        ForallRightRule( cutSub, aNew, eigen, quant )

      case l @ ExistsLeftRule( subProof, a, eigen, quant ) =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        ExistsLeftRule( cutSub, aNew, eigen, quant )

      case l @ ExistsRightRule( subProof, a, f, term, quant ) if left.mainIndices.head != aux1 =>

        val aux1Sub = l.getOccConnector.parents( aux1 ).head
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftOccConnector.children( a ).head
        ExistsRightRule( cutSub, aNew, f, term, quant )

      case l @ EqualityLeftRule( subProof, eq, a, pos ) =>
        val cutSub = CutRule( subProof, l.getOccConnector.parents( aux1 ).head, right, aux2 )
        EqualityLeftRule(
          cutSub,
          cutSub.getLeftOccConnector.children( eq ).head,
          cutSub.getLeftOccConnector.children( a ).head,
          pos
        )

      case l @ EqualityRightRule( subProof, eq, a, pos ) if l.mainIndex != aux1 =>
        val cutSub = CutRule( subProof, l.getOccConnector.parents( aux1 ).head, right, aux2 )
        EqualityRightRule(
          cutSub,
          cutSub.getLeftOccConnector.children( eq ).head,
          cutSub.getLeftOccConnector.children( a ).head,
          pos
        )

      case _ =>
        reduceRankRight( left, aux1, right, aux2 )
    }
  }
  private def reduceRankRight( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex ): LKProof = {

    right match {

      case r @ WeakeningLeftRule( subProof, main ) =>
        if ( aux2 == right.mainIndices.head ) {
          WeakeningMacroRule( subProof, left.endSequent.antecedent, left.endSequent.succedent )
        } else {
          WeakeningLeftRule( CutRule( left, aux1, subProof, r.getOccConnector.parents( aux2 ).head ), main )
        }

      case r @ WeakeningRightRule( subProof, main ) =>

        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        WeakeningRightRule( cutSub, main )

      case r @ ContractionLeftRule( subProof, a1, a2 ) =>
        if ( r.mainIndices.head == aux2 ) {
          // The right cut formula is the main formula of the contraction: Duplicate left proof
          val proofReg = regularize( left )
          val tmp = CutRule( left, aux1, subProof, a1 )
          val tmp2 = CutRule( proofReg, aux1, tmp, tmp.getRightOccConnector.children( a2 ).head )
          val tmp3 = ContractionMacroRule( tmp2, left.endSequent.delete( aux1 ) ++ right.endSequent.delete( aux2 ) )
          regularize( tmp3 )
        } else {
          // The contraction operates on the context: Swap the inferences
          val aux2Sub = r.getOccConnector.parents( aux2 ).head
          val cutSub = CutRule( left, aux1, subProof, aux2Sub )
          val ( a1New, a2New ) = ( cutSub.getRightOccConnector.children( a1 ).head, cutSub.getRightOccConnector.children( a2 ).head )
          ContractionLeftRule( cutSub, a1New, a2New )
        }

      case r @ ContractionRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightOccConnector.children( a1 ).head, cutSub.getRightOccConnector.children( a2 ).head )
        ContractionRightRule( cutSub, a1New, a2New )

      //Following line is redundant when eliminating uppermost cut
      case r @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftOccConnector.parents( aux2 )
        val aux2Right = r.getRightOccConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            CutRule( cutSub, cutSub.getRightOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            CutRule( leftSubProof, a1, cutSub, cutSub.getRightOccConnector.children( a2 ).head )
        }

      case r @ DefinitionLeftRule( subProof, a, main ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        DefinitionLeftRule( cutSub, aNew, main )

      case r @ DefinitionRightRule( subProof, a, main ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        DefinitionLeftRule( cutSub, aNew, main )

      case r @ AndLeftRule( subProof, a1, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightOccConnector.children( a1 ).head, cutSub.getRightOccConnector.children( a2 ).head )
        AndLeftRule( cutSub, a1New, a2New )

      case r @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftOccConnector.parents( aux2 )
        val aux2Right = r.getRightOccConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            AndRightRule( cutSub, cutSub.getRightOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            AndRightRule( leftSubProof, a1, cutSub, cutSub.getRightOccConnector.children( a2 ).head )
        }

      case r @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Left = r.getLeftOccConnector.parents( aux2 )
        val aux2Right = r.getRightOccConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            OrLeftRule( cutSub, cutSub.getRightOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            OrLeftRule( leftSubProof, a1, cutSub, cutSub.getRightOccConnector.children( a2 ).head )
        }

      case r @ OrRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightOccConnector.children( a1 ).head, cutSub.getRightOccConnector.children( a2 ).head )
        OrRightRule( cutSub, a1New, a2New )

      case r @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Left = r.getLeftOccConnector.parents( aux2 )
        val aux2Right = r.getRightOccConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            ImpLeftRule( cutSub, cutSub.getRightOccConnector.children( a1 ).head, rightSubProof, a2 )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getRightOccConnector.children( a2 ).head )
        }

      case r @ ImpRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightOccConnector.children( a1 ).head, cutSub.getRightOccConnector.children( a2 ).head )
        ImpRightRule( cutSub, a1New, a2New )

      case r @ NegLeftRule( subProof, a ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        NegLeftRule( cutSub, aNew )

      case r @ NegRightRule( subProof, a ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        NegRightRule( cutSub, aNew )

      case r @ ForallLeftRule( subProof, a, f, term, quant ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        ForallLeftRule( cutSub, aNew, f, term, quant )

      case r @ ForallRightRule( subProof, a, eigen, quant ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        ForallRightRule( cutSub, aNew, eigen, quant )

      case r @ ExistsLeftRule( subProof, a, eigen, quant ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        ExistsLeftRule( cutSub, aNew, eigen, quant )

      case r @ ExistsRightRule( subProof, a, f, term, quant ) =>
        val aux2Sub = r.getOccConnector.parents( aux2 ).head
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightOccConnector.children( a ).head
        ExistsRightRule( cutSub, aNew, f, term, quant )

      case r @ EqualityLeftRule( subProof, eq, a, pos ) if r.mainEqIndex != aux2 && r.mainIndex != aux2 =>
        val cutSub = CutRule( left, aux1, subProof, r.getOccConnector.parents( aux2 ).head )
        EqualityLeftRule(
          cutSub,
          cutSub.getRightOccConnector.children( eq ).head,
          cutSub.getRightOccConnector.children( a ).head,
          pos
        )

      case r @ EqualityRightRule( subProof, eq, a, pos ) if r.mainEqIndex != aux2 =>
        val cutSub = CutRule( left, aux1, subProof, r.getOccConnector.parents( aux2 ).head )
        EqualityRightRule(
          cutSub,
          cutSub.getRightOccConnector.children( eq ).head,
          cutSub.getRightOccConnector.children( a ).head,
          pos
        )

      case _ =>
        throw new ReductiveCutElimException( "Can't match the case: Cut(" + left.longName + ", " + right.longName + ")" )
    }
  }
}