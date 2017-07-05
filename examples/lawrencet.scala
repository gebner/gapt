import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, simplify, toNNF }
import at.logic.gapt.provers.smtlib.Z3

object lawrencet extends TacticsProof {
  ctx += TBase( "nat" )
  ctx += hoc"0: nat"
  ctx += hoc"s: nat>nat"
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"d: nat>nat"

  val G1 = le"^y d 0 = 0 & y + 0 = y"
  //  val G1 = le"^(y:nat) d 0 = 0"
  val G2 = le"^x ^y d (s x) = s (s (d x)) & y + s x = s (y + x)"
  val G3 = le"^x d x = x + x"

  def psi( phi: Expr ) =
    normalize( le"^x ^y ($phi x y | ($G1 y & x = 0)) & (x = y -> $G3 y)" )

  def theta2( phi: Expr ) =
    normalize( le"!x!y ($G2 x y & $phi x y -> $phi (s x) y)" )

  def weaken( psi: Formula, phi: Const, pol: Polarity = Polarity.Positive ): Formula =
    psi match {
      case And( a, b )                   => weaken( a, phi, pol ) & weaken( b, phi, pol )
      case Or( a, b )                    => weaken( a, phi, pol ) | weaken( b, phi, pol )
      case Imp( a, b )                   => weaken( a, phi, !pol ) --> weaken( b, phi, pol )
      case Neg( a )                      => -weaken( a, phi, !pol )
      case Top() | Bottom() | Eq( _, _ ) => psi
      case Apps( `phi`, _ )              => if ( pol.positive ) Top() else Bottom()
    }

  val phi0 = hoc"φ: nat>nat>o"
  def phi( n: Int ): Expr = if ( n == 0 ) phi0 else psi( phi( n - 1 ) )
  val All.Block( _, tpsi: Formula ) = normalize( theta2( phi( 2 ) ) )
  val delta = simplify( weaken( tpsi, phi0 ) )
  println( delta.toSigRelativeString )
  println( Z3.isValid( delta ) )
}