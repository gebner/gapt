package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Numeral, FOLPosition, FOLSubTerms }
import at.logic.gapt.expr.fol.thresholds.{ atMost, exactly }
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.sat4j.Sat4j

trait TraRule {
  def readRegs: Set[Int]
  def writeRegs: Set[Int]

  def rwRegs = readRegs union writeRegs
}

case class TraLeftRule( funSym: Const, dstRegs: Seq[Int], src: Int ) extends TraRule {
  require( dstRegs.size == Arity( funSym.exptype ) )

  def readRegs = Set( src )
  def writeRegs = dstRegs.toSet
  override def toString = s"$funSym(${dstRegs mkString ","}) <- $src"
}

case class TraRightRule( funSym: Const, dst: Int, srcRegs: Seq[Int] ) extends TraRule {
  require( srcRegs.size == Arity( funSym.exptype ) )

  def readRegs = srcRegs.toSet
  def writeRegs = Set( dst )
  override def toString = s"$dst <- $funSym(${srcRegs mkString ","})"
}

case class TraMoveRule( dst: Int, src: Int ) extends TraRule {
  def readRegs = Set( src )
  def writeRegs = Set( dst )
  override def toString = s"$dst <- $src"
}

case object TraNopRule extends TraRule {
  def readRegs = Set()
  def writeRegs = Set()
}

case class TraTrans( oldState: Int, newState: Int, rule: TraRule ) {
  override def toString = s"$oldState [$rule] $newState"
}

case class Tra( states: Set[Int], initial: Int,
                numRegs:     Int,
                transitions: Set[TraTrans] ) {
  transitions foreach {
    case TraTrans( o, n, rule ) =>
      require( states contains o )
      require( states contains n )
      rule.rwRegs foreach { r =>
        require( r >= 0 && r < numRegs )
      }
  }

  override def toString = transitions.toSeq.sortBy[Int]( _.oldState ).mkString( "\n" )
}

case class TraSatEnc(
    t:       FOLTerm,
    numRegs: Int, numStates: Int,
    acceptingAssignment: Map[Int, FOLTerm] = Map(),
    rightRegs:           Set[Int]          = Set()
) {
  val subTerms = FOLSubTerms( t )

  type State = Int
  //  val states = 0 to FOLPosition.getPositions( t ).size + 3
  val states = 0 until numStates

  val regs = 0 until numRegs

  val unassigned = FOLConst( "_|_" )

  def regVal( s: State, r: Int, v: Option[FOLTerm] ): FOLAtom =
    FOLAtom( "regVal", FOLConst( s toString ), FOLConst( r toString ),
      v getOrElse unassigned )

  val possibleVals = subTerms.toSeq.map { Some( _ ) } ++ Seq( None )

  val oneVal = And( for ( s <- states; r <- regs ) yield exactly oneOf { for ( v <- possibleVals ) yield regVal( s, r, v ) } )

  val initialAssignment = And( regs map { i =>
    regVal( 0, i, if ( i == 0 ) Some( t ) else None )
  } )

  import scalaz._
  import Scalaz._

  val consts = constants( t )
  val possibleLeftRules =
    for (
      funSym <- consts;
      dstRegs <- ( 0 until Arity( funSym.exptype ) ).toList.traverse( i => regs.toList );
      src <- regs
    ) yield TraLeftRule( funSym, dstRegs, src )
  val possibleRightRules =
    for (
      funSym <- consts;
      srcRegs <- ( 0 until Arity( funSym.exptype ) ).toList.traverse( i => regs.toList );
      dst <- regs if rightRegs contains dst
    ) yield TraRightRule( funSym, dst, srcRegs )
  val possibleMoveRules =
    for ( dst <- regs; src <- regs ) yield TraMoveRule( dst, src )
  val possibleRules = possibleLeftRules ++ possibleRightRules ++ Seq( TraNopRule )

  def pickedRule( s: State, r: TraRule ) =
    FOLAtom( "pickedRule", FOLConst( s toString ), FOLConst( r toString ) )

  val oneRulePerState = And(
    for ( s <- states.reverse.tail ) yield exactly oneOf { for ( r <- possibleRules toSeq ) yield pickedRule( s, r ) }
  )

  val correctTransitions = And(
    for ( s <- states.reverse.tail; rule <- possibleRules ) yield {
      val unreadRetainValues = And( for ( r <- regs diff rule.readRegs.toSeq; v <- possibleVals if v isDefined )
        yield regVal( s, r, v ) --> regVal( s + 1, r, v ) )
      val untouchedStayTheSame = And( for ( r <- regs diff rule.rwRegs.toSeq; v <- possibleVals )
        yield regVal( s, r, v ) <-> regVal( s + 1, r, v ) )
      val readsAreDefined = And( for ( src <- rule.readRegs.toSeq ) yield -regVal( s, src, None ) )
      val ruleTransCorr = rule match {
        case TraMoveRule( src, dst ) if src == dst =>
          And( for ( v <- possibleVals ) yield regVal( s + 1, dst, v ) <-> regVal( s, src, v ) )
        case TraMoveRule( src, dst ) if src != dst =>
          regVal( s, dst, None ) & regVal( s + 1, src, None ) & And(
            for ( v <- possibleVals ) yield regVal( s + 1, dst, v ) <-> regVal( s, src, v )
          )
        case TraLeftRule( funSym, dstRegs, src ) =>
          val srcRegUndef = if ( dstRegs contains src ) Top() else regVal( s + 1, src, None )
          And( for ( v <- possibleVals ) yield regVal( s, src, v ) --> ( v match {
            case Some( Apps( `funSym`, args ) ) =>
              And( for ( ( r2, v2: FOLTerm ) <- dstRegs zip args )
                yield regVal( s + 1, r2, Some( v2 ) ) )
            case _ => Bottom()
          } ) ) & srcRegUndef
        case TraRightRule( funSym, dst, srcRegs ) =>
          val srcRegsUndef = And( for ( src <- srcRegs if src != dst ) yield regVal( s + 1, src, None ) )
          And( for ( v <- possibleVals ) yield regVal( s + 1, dst, v ) --> ( v match {
            case Some( Apps( `funSym`, args ) ) =>
              And( for ( ( r2, v2: FOLTerm ) <- srcRegs zip args )
                yield regVal( s, r2, Some( v2 ) ) )
            case _ => Bottom()
          } ) ) & srcRegsUndef
        case TraNopRule => Top()
      }
      pickedRule( s, rule ) --> ( unreadRetainValues & untouchedStayTheSame & readsAreDefined & ruleTransCorr )
    }
  )

  def acceptingState( s: State ) =
    And( for ( r <- regs ) yield regVal( s, r, acceptingAssignment.get( r ) ) )

  val isAccepting = acceptingState( states last )

  val formula = initialAssignment & oneVal & oneRulePerState & correctTransitions & isAccepting

  def solve(): Option[Tra] =
    new Sat4j().solve( formula ) map { interp =>
      Tra( states.toSet, states.head, numRegs,
        ( for ( s <- states.reverse.tail; r <- possibleRules if interp.interpret( pickedRule( s, r ) ) )
          yield TraTrans( s, s + 1, r ) ) toSet )
    } orElse {
      //      println( new Prover9Prover().getRobinsonProof( formula +: Sequent() ).get )
      None
    }
}
