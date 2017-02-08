package at.logic.gapt.formats.tip

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existentialClosure, universalClosure }
import at.logic.gapt.proofs.{ Context, Sequent }

case class TipConstructor( constr: Const, projectors: Seq[Const] ) {
  val FunctionType( datatype, fieldTypes ) = constr.exptype
  require( fieldTypes.size == projectors.size )
  projectors foreach { case Const( _, FunctionType( to, from ) ) => require( from == Seq( datatype ) ) }

  def arity = projectors size

  def projectorDefinitions: Seq[HOLFormula] = {
    val fieldVars = fieldTypes.zipWithIndex.map { case ( t, i ) => Var( s"x$i", t ) }
    ( projectors, fieldVars ).zipped map { ( p, f ) => p( constr( fieldVars: _* ) ) === f }
  }
}
case class TipDatatype( t: TBase, constructors: Seq[TipConstructor] ) {
  constructors foreach { ctr => require( ctr.datatype == t ) }
}

case class TipFun( fun: Const, definitions: Seq[HOLFormula] )

case class TipProblem(
    ctx:   Context,
    sorts: Seq[TBase], datatypes: Seq[TipDatatype],
    uninterpretedConsts: Seq[Const], functions: Seq[TipFun],
    assumptions: Seq[HOLFormula], goal: HOLFormula
) {
  def constructorInjectivity =
    for {
      TipDatatype( ty, ctrs ) <- datatypes
      if ty != To // FIXME
      ( TipConstructor( ctr1, _ ), i1 ) <- ctrs.zipWithIndex
      ( TipConstructor( ctr2, _ ), i2 ) <- ctrs.zipWithIndex
      if i1 < i2 // ignore symmetric pairs
      FunctionType( _, args1 ) = ctr1.exptype
      FunctionType( _, args2 ) = ctr2.exptype
    } yield universalClosure(
      ctr1( ( for ( ( t, j ) <- args1.zipWithIndex ) yield Var( s"x$j", t ) ): _* ) !==
        ctr2( ( for ( ( t, j ) <- args2.zipWithIndex ) yield Var( s"y$j", t ) ): _* )
    )

  def projections =
    for {
      TipDatatype( ty, ctrs ) <- datatypes
      if ty != To
      tipCtr @ TipConstructor( ctr, projs ) <- ctrs
      argVars = for ( ( t, i ) <- tipCtr.fieldTypes.zipWithIndex ) yield Var( s"x_$i", t )
      ( proj, i ) <- projs.zipWithIndex
    } yield universalClosure( hof"$proj ${ctr( argVars )} = ${argVars( i )}" )

  def caseDistinctions =
    for {
      TipDatatype( ty, ctrs ) <- datatypes
      if ty != To
      x = Var( "x", ty )
    } yield All( x, Or( for ( TipConstructor( ctr, projs ) <- ctrs )
      yield x === ctr( projs.map( _( x ) ) ) ) )

  def toSequent = existentialClosure(
    datatypes.flatMap( _.constructors ).flatMap( _.projectorDefinitions ) ++:
      functions.flatMap( _.definitions ) ++:
      constructorInjectivity ++:
      assumptions ++:
      projections ++:
      caseDistinctions ++:
      Sequent()
      :+ goal
  )

  def context: Context = ctx
}
