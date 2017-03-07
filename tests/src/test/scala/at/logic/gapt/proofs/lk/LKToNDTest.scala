package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd.NDProof
import at.logic.gapt.proofs.{ Ant, SequentIndex, SequentMatchers, Suc }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToNDTest extends Specification with SatMatchers with SequentMatchers {

  def checkEquality( nd: NDProof, lk: LKProof, focus: SequentIndex ) = {
    lk.endSequent.size == nd.endSequent.size &&
      lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) &&
      lk.endSequent.antecedent.forall( nd.endSequent.antecedent.contains( _ ) ) &&
      lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x => nd.endSequent.antecedent.contains( Neg( x ) ) )
  }

  "The LK to ND translation" should {

    /*
    "translate DeMorgan's law" in {
    }
    */

    "translate OrLeft 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( OrLeftRule( _, _, hof"A | A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 3" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( OrLeftRule( _, _, hof"A | D" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 4 with focus 3" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( OrLeftRule( _, _, hof"A | D" ) ).
        qed

      val focus = Suc( 3 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 5 with focus 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        u( NegRightRule( _, hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Suc( 2 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpRight 1 with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpRight 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrRight 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrRight 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | -B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate NegLeft followed by NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( NegRightRule( _, hof"-A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate WeakeningRight followed by ContractRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( ContractionRightRule( _, hof"A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate Cut 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate Cut 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpLeft with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( ImpLeftRule( _, _, hof"A -> B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpLeft with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( ImpLeftRule( _, _, hof"A -> B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate LEM" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegRightRule( _, hof"A" ) ).
        u( OrRightRule( _, hof"A | -A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate WeakeningRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate example 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningRightRule( _, hof"D" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        u( NegLeftRule( _, hof"A | B" ) ).
        u( OrRightRule( _, hof"C | D" ) ).
        qed
      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )
      checkEquality( nd, lk, focus ) mustEqual true
    }
  }
}

