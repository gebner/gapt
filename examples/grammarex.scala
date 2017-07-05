import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object grammarex extends TacticsProof {
  ctx += Context.InductiveType(
    ty"tk",
    hoc"tl: tk", hoc"tr: tk", hoc"tp: tk", hoc"tx: tk", hoc"ty: tk"
  )
  ctx += Context.InductiveType(
    ty"expr",
    hoc"ex: expr", hoc"ey: expr", hoc"ep: expr>expr>expr"
  )
  ctx += Context.InductiveType(
    "ty:list ?a",
    hoc"cons: ?a > list ?a > list ?a",
    hoc"nil: list ?a"
  )

  ctx += hoc"'+': list ?a > list ?a > list ?a"
  ctx += hoc"s: ?a > list ?a"
  val appTh = Seq(
    hoa"(nil : list ?a) + x = x",
    hoa"x + (nil : list ?a) = x",
    hoa"(x : list ?a) + (y + z) = (x + y) + z",
    hoa"cons(x:?a, y) = s(x) + y"
  )

  ctx += hoc"lin: expr > list tk"
  val linTh = Seq(
    hoa"lin ex = tx", hoa"lin ey = ty",
    hoa"lin (ep x y) = s(tl) + lin x + s(tp) + lin y + s(tr)"
  )

  val ts = Seq( le"e" )

}