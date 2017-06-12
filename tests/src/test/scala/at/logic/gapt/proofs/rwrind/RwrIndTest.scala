package at.logic.gapt.proofs.rwrind

import org.specs2.mutable.Specification
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{Context, Suc}

class RwrIndTest extends Specification{

  "double" in {
    import at.logic.gapt.examples.tip.prod.prop_01._
    val th = Vector(hoa"d 0 = 0", hoa"d (S x) = S (S (d x))",
      hoa"0 + y = y", hoa"S x + y = S (x + y)")
    val p1 = Input(hoa"d x = x + x")
    val p2 = Expand(p1, Suc(0), ltr = true, le"x+x",
      Vector(hoa"0 + x = x", hoa"S x + y = S (x + y)"))
    val p3 = Refl(SimplifyMacro(p2, Suc(0), th), Suc(1))
    val p4 = Refl(SimplifyMacro(p3, Suc(0), th), Suc(0))
//    println(p4)
    ok
  }

  "length rev" in {
    var ctx = Context()
    ctx += Context.Sort("i")
    ctx += Context.InductiveType("list", hoc"nil: list", hoc"cons: i>list>list")
    ctx += Context.InductiveType("nat", hoc"0: nat", hoc"s: nat")
    ctx += hoc"length: list>nat"
    ctx += hoc"append: list>list>list"
    ctx += hoc"rev: list>list"

    val th_len = Vector(hoa"length nil = 0", hoa"length (cons x y) = s (length y)")
    val th_app = Vector( hoa"append nil y = y", hoa"append (cons x y) z = cons x (append y z)")
    val th_rev = Vector( hoa"rev nil = nil", hoa"rev (cons x y) = append (rev y) (cons x nil)" )
    val th = th_len ++ th_app ++ th_rev

    var p: RwrIndProof = Input(hoa"length (rev x) = length x")
    p = Expand(p, Suc(0), ltr = true, le"rev x", th_rev)
    p = Refl(p, Suc(0))
    p = Lemma(p, hoa"length(append(y, cons(x_0, nil))) = length(cons(x_0, y)) ")
    p = SimplifyMacro(p, Suc(1), th)
    p = Expand(p, Suc(1), ltr = true, le"length y", th_len)
    p = SimplifyMacro(p, Suc(1), th)
    p = Refl(p, Suc(2))
    p = SimplifyMacro(p, Suc(0), th)
    p = Refl(p, Suc(1))
    p = SimplifyMacro(p, Suc(0), th)
    p = Refl(p, Suc(0))
    println(p)
    ok
  }

}
