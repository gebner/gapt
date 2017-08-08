package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import cats.implicits._

object finiteDomainInstantiation {

  case class Environment(
                        domains: Map[TBase, Set[Expr]],
                        functions: Map[Var, Map[List[Expr], Expr]]
                        )

  def apply(f: Formula, domains: Map[TBase, Set[Expr]]): Formula =
    apply(f)(Environment(domains, functions = Map())).asInstanceOf[Formula]

  def enumerate(t: Ty)(implicit env: Environment): Option[Vector[Map[List[Expr], Expr]]] =
    t match {
      case t: TBase =>
        env.domains.get(t).map(
          _.view.map(x => Map(List[Expr]() -> x)).toVector)
      case (t1: TBase) -> t2 =>
        for {
          d1 <- env.domains.get(t1)
          d2 <- enumerate(t2)
        } yield
          d1.toList.traverse[List, Map[List[Expr], Expr]](x1 =>
            d2.map(x2 => x2.map{case (k,v) => (x1::k, v)}).toList)
            .map(Map() ++ _.flatten).toVector
      case _ => None
    }

  def apply(e: Expr)(implicit  env: Environment): Expr =
    e match {
      case Apps(v: Var, as) if env.functions.contains(v) =>
        val as_ = as.map(apply)
        env.functions(v)(as_)
      case All(x, a) =>
        enumerate(x.ty) match {
          case Some(vs) =>
            And(for (v <- vs) yield
              apply(a)(env.copy(functions = env.functions.updated(x, v))))
          case None => All(x, apply(a))
        }
      case Ex(x, a) =>
        enumerate(x.ty) match {
          case Some(vs) =>
            Or(for (v <- vs) yield
              apply(a)(env.copy(functions = env.functions.updated(x, v))))
          case None => All(x, apply(a))
        }
      case App(a, b) => App(apply(a), apply(b))
      case Abs(x, a) => Abs(x, apply(a))
    }

}
