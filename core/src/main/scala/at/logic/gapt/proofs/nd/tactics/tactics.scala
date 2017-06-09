package at.logic.gapt.proofs.nd.tactics
import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.{ Context, HOLSequent, NDSequent, Sequent, Suc }
import cats.syntax.traverse._
import cats.syntax.either._
import cats.instances.list._
import cats.instances.either._

private[tactics] trait TacticTypes {
  type TacticResult[+X] = Either[TacticException, X]
  type Goal = NDSequent[Formula]

  def nothingElim[T]: Nothing => T = _ =>
    throw new IllegalArgumentException

  implicit def tacticToTactic0( tac: Tactic[Nothing] ): Tactic0 =
    Tactic0( tac )
}

trait Tactic[+T] {
  def solve( goal: Goal, continuation: T => Tactic0 ): TacticResult[NDProof]

  def flatMap[S]( f: T => Tactic[S] ): Tactic[S] = ( goal, continuation ) =>
    solve( goal, t => goal_ => f( t ).solve( goal_, continuation ) )

  def cases[S]( f: T => Tactic[S] ): Tactic[S] = flatMap( f )

  def next[S]( that: => Tactic[S] ): Tactic[S] = flatMap( _ => that )
  def >>[S]( that: => Tactic[S] ): Tactic[S] = next( that )

  def |[S >: T]( that: Tactic[S] ): Tactic[S] = ( goal, cont ) =>
    solve( goal, cont ) match {
      case r @ Right( _ ) => r
      case Left( _ )      => that.solve( goal, cont )
    }
}

trait Tactic0 extends Tactic[Nothing] {
  def solve( goal: Goal, cont: Nothing => Tactic0 ) = solve0( goal )

  def solve0( goal: Goal ): TacticResult[NDProof]
}
object Tactic0 {
  def apply( tac: Tactic[Nothing] ): Tactic0 =
    goal => tac.solve( goal, nothingElim )
}

case class TacticException( goal: NDSequent[Formula], msg: String, cause: Option[Throwable] = None, committed: Boolean = false )
  extends Exception( s"$msg\n${implicitly[HOLSequent]( goal ).toString}", cause.orNull )

private[tactics] trait TacticDefs {

  def Lemma( goal: HOLSequent )( tac: Tactic[Nothing] ): NDProof = {
    require( goal.succedent.size == 1 )
    Lemma( NDSequent( goal.antecedent, goal.succedent.head ) )( tac )
  }

  def Lemma( goal: NDSequent[Formula] )( tac: Tactic[Nothing] ): NDProof =
    tac.solve( goal, nothingElim ) match {
      case Left( err )    => throw err
      case Right( proof ) => proof
    }

  def Lemma( goal: Formula )( tac: Tactic[Nothing] ): NDProof =
    Lemma( NDSequent( Seq(), goal ) )( tac )

  def goal: Tactic[Goal] = ( goal, cont ) => cont( goal ).solve0( goal )
  def target: Tactic[Formula] = ( goal, cont ) => cont( goal.conclusion ).solve0( goal )

  def intro: Tactic[Expr] = ( goal, cont ) =>
    goal.conclusion match {
      case Imp( a, b ) =>
        cont( a ).solve0( a +: goal :- b ).map( ImpIntroRule( _, Right( a ) ) )
      case f @ All( x0, _ ) =>
        val x = rename( x0, freeVariables( goal ) )
        cont( x ).solve0( goal :- instantiate( f, x ) ).map( ForallIntroRule( _, f, x ) )
      case f => Left( TacticException( goal, s"cannot introduce $f" ) )
    }

  def try_[T]( tac: Tactic[T] ): Tactic[Option[T]] =
    ( goal, cont ) => tac.solve( goal, t => goal =>
      cont( Some( t ) ).solve0( goal ).leftMap( _.copy( committed = true ) ) ).
      recoverWith { case ex if !ex.committed => cont( None ).solve0( goal ) }

  def pure[T]( t: T ): Tactic[T] = ( goal, cont ) => cont( t ).solve0( goal )
  def skip: Tactic[Unit] = pure( () )

  def intros: Tactic[Unit] = try_( intro ).flatMap { case Some( _ ) => intros case None => skip }

  trait From[+T] extends Tactic[T] {
    def from( tac: Tactic[Nothing] ): Tactic[T]
    def solve( goal: Goal, continuation: T => Tactic0 ): TacticResult[NDProof] =
      from( assumption ).solve( goal, continuation )
  }
  def have( step: Formula ): From[Unit] =
    from => ( goal, later ) => for {
      stepProof <- from.solve0( goal :- step )
      laterProof <- later( () ).solve0( step +: goal )
    } yield ImpElimRule( ImpIntroRule( laterProof, Right( step ) ), stepProof )

  def sorry: Tactic0 = goal => {
    println( s"sorry: ${NDSequent.toSequent( goal )}" )
    Right( TheoryAxiom( goal.conclusion ) )
  }

  def assumption: Tactic0 = goal => {
    val fixedVars = PreSubstitution( freeVariables( goal ).map( v => v -> v ) )
    val nameGen = rename.awayFrom( freeVariables( goal ) )
    val concl = goal.conclusion

    def find( f: Formula, p: => NDProof ): Option[NDProof] =
      syntacticMatching( List( f -> concl ), fixedVars ).headOption match {
        case Some( subst ) =>
          Some( if ( subst.isIdentity ) p else subst( p ) )
        case None => f match {
          case And( a, b ) =>
            find( a, AndElim1Rule( p ) ) orElse find( b, AndElim2Rule( p ) )
          case f @ All( x0, _ ) =>
            val x = nameGen.fresh( x0 )
            find( instantiate( f, x ), ForallElimRule( p, x ) )
          case _ => None
        }
      }

    goal.assumptions.view.flatMap( a => find( a, LogicalAxiom( a ) ) ).headOption match {
      case Some( p ) => Right( p )
      case None      => Left( TacticException( goal, "not an assumption" ) )
    }
  }

  def induction( v: String )( implicit ctx: Context ): Tactic[String] =
    ( goal, cont ) => freeVariables( goal ).find( _.name == v ) match {
      case Some( v_ ) => induction( v_ ).solve( goal, cont )
      case None       => Left( TacticException( goal, s"variable $v does not occur in goal" ) )
    }

  def induction( v: Var )( implicit ctx: Context ): Tactic[String] =
    ( goal, cases ) => {
      def fromOption[X]( o: Option[X], msg: String ): TacticResult[X] =
        o match {
          case Some( x ) => Right( x )
          case None      => Left( TacticException( goal, msg ) )
        }

      def mkCase( ctor: Const ): TacticResult[InductionCase] = {
        val FunctionType( _, argTypes ) = ctor.ty
        val nameGen = rename.awayFrom( freeVariables( goal ) )
        val evs = argTypes map { at => nameGen.fresh( ( if ( at == v.ty ) v else Var( "x", at ) ): Var ) }
        val hyps = evs.filter( _.ty == v.ty ).map( ev => Substitution( v -> ev )( goal.conclusion ) )
        val subGoal = hyps ++: goal :- Substitution( v -> ctor( evs ) )( goal.conclusion )
        //        if ( !cases.isDefinedAt( ctor.name ) ) return Left( TacticException( subGoal, s"no induction case for $ctor given" ) )
        cases( ctor.name ).solve0( subGoal ).map { proof =>
          val proof_ = hyps.foldLeft( proof )( ( proof, hyp ) =>
            if ( proof.conclusion.antecedent.contains( hyp ) ) proof
            else WeakeningRule( proof, hyp ) )
          InductionCase( proof_, ctor, hyps.map( proof_.conclusion.indexOfInAnt _ ), evs )
        }
      }

      for {
        ctors <- fromOption( ctx.getConstructors( v.ty ), s"${v.ty} is not an inductive data type" )
        indCases <- ctors.toList.traverse( mkCase( _ ) )
      } yield InductionRule( indCases, Abs( v, goal.conclusion ), v )
    }

  def elim( what: Formula ): From[Int] = from => ( goal, later ) => {
    var i = 0
    def go( p: NDProof, first: Boolean = false ): TacticResult[NDProof] =
      p.conclusion( Suc( 0 ) ) match {
        case Or( a, b ) =>
          for {
            pa <- go( LogicalAxiom( a ) )
            pb <- go( LogicalAxiom( b ) )
          } yield OrElimRule( p, pa, pb )
        case f @ Ex( x0, _ ) =>
          val x = rename( x0, freeVariables( p.conclusion :+ goal.conclusion ) )
          val g = instantiate( f, x )
          for {
            q <- go( LogicalAxiom( g ) )
          } yield ExistsElimRule( p, q, x )
        case _ if first =>
          Left( TacticException( goal, s"cannot eliminate $what" ) )
        case f =>
          i += 1
          later( i ).solve0( f +: goal )
      }

    from.solve0( goal :- what ).flatMap( go( _, first = true ) )
  }

  def elimold( cases: ( Formula, Tactic0 )* ): Tactic0 = goal => {
    val casesMap = cases.toMap

    def find( f: Formula ): Option[Tactic0] =
      casesMap.get( f ) match {
        case Some( tac ) => Some( tac )
        case None =>
          f match {
            case Or( a, b ) =>
              for {
                ta <- find( a )
                tb <- find( b )
              } yield ( goal => for {
                pa <- ta.solve0( a +: goal )
                pb <- tb.solve0( b +: goal )
              } yield OrElimRule( LogicalAxiom( f ), pa, pb ) ): Tactic0
            case _ => None
          }
      }

    goal.assumptions.view.flatMap( find ).headOption match {
      case Some( tac ) => tac.solve0( goal )
      case None        => Left( TacticException( goal, s"cannot eliminate using cases ${cases.map( _._1 ) ++: Sequent()}" ) )
    }
  }

  def suffices( newGoal: Formula ): From[Unit] =
    from => ( goal, cont ) => have( newGoal ).from( cont( () ) ).solve( goal, _ => from )
}
