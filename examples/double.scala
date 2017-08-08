import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.expr._

object double extends TacticsProof {
  ctx += TBase("n")
  ctx += hoc"0: n"
  ctx += hoc"s: n>n"
  ctx += hoc"d: n>n"
  ctx += hoc"'+': n>n>n"

  val th = hof"d 0 = 0 & !x d (s x) = s (s (d x))" &
    hof"!x x + 0 = x & !x !y x + s y = s (x + y)"

  val f =
    hof"""$th -> !phi -(
         !y phi 0 y &
         !x!y (phi x y -> phi (s x) y) &
         !x (phi x x -> d x = x + x)
    )"""
}