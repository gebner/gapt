package at.logic.gapt.examples

import kodkod.ast.{Expression, Formula, Relation, Variable}
import kodkod.ast.RelationPredicate.Function
import kodkod.engine.{IncrementalSolver, Solution}
import kodkod.engine.config.Options
import kodkod.instance.{Bounds, Universe}


object doublekodkod extends Script{

  val zero = Relation.unary("0")
  val s_ = Relation.binary("s")
  val d_ = Relation.binary("d")
  val plus_ = Relation.ternary("+")

  def s(e: Expression) = e.join(s_)
  def d(e: Expression) = e.join(d_)
  def plus(a: Expression, b: Expression) = b join a join plus_

  val nat = Expression.UNIV

  def function_(r: Relation, d1: Expression, d2: Expression, v: Expression): Formula = {
    val x = Variable.unary("x")
    val y = Variable.unary("y")
    val z = y join x join r
    (z.one and z.in(v)).forAll(x.oneOf(d1) and y.oneOf(d2))
  }

  val x = Variable.unary("x")
  val y = Variable.unary("y")

  val theory= Formula.and(
    s_.function(nat, nat),
    d_.function(nat, nat),
    function_(plus_, nat, nat, nat),
    d(zero) eq zero,
    (d(s(x)) eq s(s(d(x)))).forAll(x oneOf nat),
    (plus(x, zero) eq x).forAll(x oneOf nat),
    (plus(x, s(y)) eq s(plus(x,y))).forAll(x oneOf nat)
  )

  val opts = new Options
  val solver = new IncrementalSolver(opts)

  val u = new Universe(for (i <- 0 to 2) yield s"x$i")
  val b = new Bounds(u)

  def loop(solution: Solution): Solution = {
    if (solution.unsat) return solution

    
  }

  loop(solver.solve(theory, b))

  val phi = Relation.binary("φ")

}