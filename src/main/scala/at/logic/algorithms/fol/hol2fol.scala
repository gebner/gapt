package at.logic.algorithms.fol.hol2fol

import at.logic.calculi.lk.base.FSequent
import at.logic.language.fol._
import at.logic.language.hol
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.replacements.{ Replacement, getAllPositions2 }
import at.logic.language.lambda._
import at.logic.language.lambda.symbols.{ StringSymbol, SymbolA }
import at.logic.language.lambda.types.{ FunctionType, TA, Ti, To }
import at.logic.language.schema.{ IntZero, IntegerTerm, Succ, foConst, foVar, indexedFOVar }

object reduceHolToFol extends reduceHolToFol
/**
 * Creates a FOL formula from a HOL formula, but applies transformations which do _not_ preserve validity!
 * Transformations applied:
 *
 *  - Replace all subterms (\x.t) by a constant. The scope parameter is needed to pass existing term-constant mappings.
 *  - Change the type of constants and variables s.t. they are first order (i.e. Const("c", To->Ti) is mapped to FOLConst("c",Ti)
 *  - Logical operators inside the term structure are replaced by first order terms
 *
 * @note Make sure you need all of these tricks. If you have a HOL formula which actually is a FOL formula, use
 *       [[convertHolToFol]]. To replace abstraction subterms, use [[replaceAbstractions]]. Both have clear and easily
 *       revertible semantics.
 *
 */
class reduceHolToFol {

  /**
   * Convenience method when only a single expression is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param term a HOL expression to convert
   * @return the reduced FOL expression
   */
  def apply( term: HOLExpression ): FOLExpression = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply( term, emptymap, counter )._1
  }

  /**
   * Convenience method when only a single fsequent is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply( fs: FSequent ): FSequent = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply( fs, emptymap, counter )._1
  }

  /**
   * Convenience method when a single  list of fsequents is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply( fs: List[FSequent] ): List[FSequent] = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply( fs, emptymap, counter )._1
  }

  /**
   * Apply method for a formula when scope needs to passed on in a recursion.
   * @param formula the formula to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced formula and the updated scope
   */
  def apply( formula: HOLFormula, scope: Map[HOLExpression, StringSymbol], id: { def nextId: Int } ): ( FOLFormula, Map[HOLExpression, StringSymbol] ) = {
    val ( scope_, qterm ) = replaceAbstractions( formula, scope, id )
    ( apply_( qterm ).asInstanceOf[FOLFormula], scope_ )
  }

  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param s the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( s: FSequent, scope: Map[HOLExpression, StringSymbol], id: { def nextId: Int } ): ( FSequent, Map[HOLExpression, StringSymbol] ) = {
    val ( scope1, ant ) = s.antecedent.foldLeft( ( scope, List[HOLFormula]() ) )( ( r, formula ) => {
      val ( scope_, f_ ) = replaceAbstractions( formula, r._1, id )
      ( scope_, f_.asInstanceOf[HOLFormula] :: r._2 )
    } )
    val ( scope2, succ ) = s.succedent.foldLeft( ( scope1, List[HOLFormula]() ) )( ( r, formula ) => {
      val ( scope_, f_ ) = replaceAbstractions( formula, r._1, id )
      ( scope_, f_.asInstanceOf[HOLFormula] :: r._2 )
    } )

    ( FSequent( ant.reverse map apply_, succ.reverse map apply_ ), scope ++ scope2 )
  }

  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param fss the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( fss: List[FSequent], scope: Map[HOLExpression, StringSymbol], id: { def nextId: Int } ): ( List[FSequent], Map[HOLExpression, StringSymbol] ) = {
    fss.foldRight( ( List[FSequent](), scope ) )( ( fs, pair ) => {
      val ( list, scope ) = pair
      val ( fs_, scope_ ) = apply( fs, scope, id )
      ( fs_ :: list, scope_ )
    } )

  }

  //assumes we are on the logical level of the hol formula - all types are mapped to i, i>o or i>i>o respectively
  private def apply_( term: HOLExpression ): FOLExpression = {
    term match {
      //      case e: FOLExpression          => e // if it's already FOL - great, we are done.
      case z: indexedFOVar => FOLVar( z.name.toString ++ intTermLength( z.index.asInstanceOf[IntegerTerm] ).toString )
      case fov: foVar      => FOLVar( fov.name )
      case foc: foConst    => FOLConst( foc.name )
      case Neg( n )        => Neg( apply_( n ) )
      case And( n1, n2 )   => And( apply_( n1 ), apply_( n2 ) )
      case Or( n1, n2 )    => Or( apply_( n1 ), apply_( n2 ) )
      case Imp( n1, n2 )   => Imp( apply_( n1 ), apply_( n2 ) )
      case AllVar( v, n )  => AllVar( apply_( v ).asInstanceOf[Var], apply_( n ) )
      case ExVar( v, n )   => ExVar( apply_( v ).asInstanceOf[Var], apply_( n ) )
      case Atom( Const( n, _ ), ls ) =>
        FOLAtom( n, ls.map( x => apply_termlevel( x ) ) )
      case Atom( Var( n, _ ), ls ) =>
        FOLAtom( n, ls.map( x => apply_termlevel( x ) ) )
      case Function( Const( n, _ ), ls, _ ) =>
        FOLFunction( n, ls.map( x => apply_termlevel( x ) ) )
      case Function( Var( n, _ ), ls, _ ) =>
        FOLFunction( n, ls.map( x => apply_termlevel( x ) ) )
      case Var( n, _ )   => FOLVar( n )
      case Const( n, _ ) => FOLConst( n )

      //this case is added for schema
      case App( func, arg ) => {
        func match {
          case Var( sym, _ ) =>
            val new_arg = apply_( arg ).asInstanceOf[FOLTerm]
            return FOLFunction( sym, new_arg :: Nil )

          case _ =>
            println( "WARNING: FO schema term: " + term )
            throw new Exception( "Probably unrecognized object from schema!" )
        }
      }
      case _ => throw new IllegalArgumentException( "Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom" ) // for cases of higher order atoms and functions
    }
  }

  //if we encountered an atom, we need to convert logical formulas to the term level too
  private def apply_termlevel( term: HOLExpression ): FOLTerm = {
    term match {
      case z: indexedFOVar => FOLVar( z.name.toString ++ intTermLength( z.index.asInstanceOf[IntegerTerm] ).toString )
      case fov: foVar      => FOLVar( fov.name.toString )
      case foc: foConst    => FOLConst( foc.name.toString )
      case Var( n, _ )     => FOLVar( n )
      case Const( n, _ )   => FOLConst( n )
      //we cannot use the logical symbols directly because they are treated differently by the Function matcher
      case Neg( n )        => FOLFunction( NegSymbol.toString, List( apply_termlevel( n ) ) )
      case And( n1, n2 )   => FOLFunction( AndSymbol.toString, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case Or( n1, n2 )    => FOLFunction( OrSymbol.toString, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case Imp( n1, n2 )   => FOLFunction( ImpSymbol.toString, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case AllVar( v: Var, n ) =>
        FOLFunction( ForallSymbol.toString, List( apply_termlevel( v ).asInstanceOf[Var], apply_termlevel( n ) ) )
      case ExVar( v: Var, n ) =>
        FOLFunction( ExistsSymbol.toString, List( apply_termlevel( v ).asInstanceOf[Var], apply_termlevel( n ) ) )
      case Atom( Const( n, _ ), ls ) =>
        FOLFunction( n, ls.map( x => apply_termlevel( x ) ) )
      case Atom( Var( n, _ ), ls ) =>
        FOLFunction( n, ls.map( x => apply_termlevel( x ) ) )
      case Function( Const( name, _ ), ls, _ ) =>
        FOLFunction( name, ls.map( x => apply_termlevel( x ) ) )

      //this case is added for schema
      /*
      case App(func,arg) => {
        func match {
          case Var(sym,_) => {
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return at.logic.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
          }
          case _ => println("\nWARNING: FO schema term!\n")
        }
        throw new Exception("\nProbably unrecognized object from schema!\n")
      }
      */

      // This case replaces an abstraction by a function term.
      //
      // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
      //
      // TODO: at the moment, syntactic equality is used here... This means that alpha-equivalent terms may be replaced
      // by different constants, which is undesirable.
      /*
      case a @ Abs(v, exp) => {
        val sym = scope.getOrElseUpdate(a.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName")), ConstantStringSymbol("q_{" + id.nextId + "}"))
        val freeVarList = a.getFreeVariables.toList.sortWith((x,y) => x.toString < y.toString).map(x => apply(x.asInstanceOf[HOLExpression],scope,id))
        if (freeVarList.isEmpty) FOLConst(sym) else Function(sym, freeVarList.asInstanceOf[List[FOLTerm]])
      }
      */
      case _ => throw new IllegalArgumentException( "Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom" ) // for cases of higher order atoms and functions
    }
  }

  //transforms a ground integer term to Int
  private def intTermLength( t: IntegerTerm ): Int = t match {
    case c: IntZero => 0
    case Succ( t1 ) => 1 + intTermLength( t1 )
    case _          => throw new Exception( "\nError in reduceHolToFol.length(...) !\n" )
  }
}

object replaceAbstractions extends replaceAbstractions

/**
 * Replace lambda-abstractions by constants.
 *
 * Each abstraction in an [[at.logic.calculi.lk.base.FSequent]] is replaced by a separate constant symbol; the used
 * constants are returned in a Map.
 */
class replaceAbstractions {
  type ConstantsMap = Map[HOLExpression, StringSymbol]

  def apply( l: List[FSequent] ): ( ConstantsMap, List[FSequent] ) = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    l.foldLeft( ( Map[HOLExpression, StringSymbol](), List[FSequent]() ) )( ( rec, el ) => {
      val ( scope_, f ) = rec
      val ( nscope, rfs ) = replaceAbstractions( el, scope_, counter )
      ( nscope, rfs :: f )

    } )
  }

  def apply( f: FSequent, scope: ConstantsMap, id: { def nextId: Int } ): ( ConstantsMap, FSequent ) = {
    val ( scope1, ant ) = f.antecedent.foldLeft( ( scope, List[HOLFormula]() ) )( ( rec, formula ) => {
      val ( scope_, f ) = rec
      val ( nscope, nformula ) = replaceAbstractions( formula, scope_, id )
      ( nscope, nformula.asInstanceOf[HOLFormula] :: f )
    } )
    val ( scope2, succ ) = f.succedent.foldLeft( ( scope1, List[HOLFormula]() ) )( ( rec, formula ) => {
      val ( scope_, f ) = rec
      val ( nscope, nformula ) = replaceAbstractions( formula, scope_, id )
      ( nscope, nformula.asInstanceOf[HOLFormula] :: f )
    } )

    ( scope2, FSequent( ant.reverse, succ.reverse ) )
  }

  def apply( e: HOLExpression ): HOLExpression = {
    val counter = new {
      private var state = 0;

      def nextId = {
        state = state + 1; state
      }
    }
    apply( e, Map[HOLExpression, StringSymbol](), counter )._2
  }

  // scope and id are used to give the same names for new functions and constants between different calls of this method
  def apply( e: HOLExpression, scope: ConstantsMap, id: { def nextId: Int } ): ( ConstantsMap, HOLExpression ) = e match {
    case Var( _, _ ) =>
      ( scope, e )
    case Const( _, _ ) =>
      ( scope, e )
    //quantifiers should be kept
    case AllVar( x, f ) =>
      val ( scope_, e_ ) = replaceAbstractions( f, scope, id )
      ( scope_, AllVar( x, e_.asInstanceOf[HOLFormula] ) )
    case ExVar( x, f ) =>
      val ( scope_, e_ ) = replaceAbstractions( f, scope, id )
      ( scope_, ExVar( x, e_.asInstanceOf[HOLFormula] ) )
    case App( s, t ) =>
      val ( scope1, s1 ) = replaceAbstractions( s, scope, id )
      val ( scope2, t1 ) = replaceAbstractions( t, scope1, id )
      ( scope2, App( s1, t1 ) )
    // This case replaces an abstraction by a function term.
    // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
    case Abs( v, exp ) =>
      //systematically rename free variables for the index
      //val normalizeda = e.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName"))
      //TODO: check if variable renaming is really what we want
      val ( normalizeda, mapping ) = normalizeFreeVariables( e )
      //println("e: "+e)
      //println("norm: "+normalizeda)
      //update scope with a new constant if neccessary
      //println(scope)
      val scope_ = if ( scope contains normalizeda ) scope else scope + ( ( normalizeda, StringSymbol( "q_{" + id.nextId + "}" ) ) )
      //println(scope_)
      val sym = scope_( normalizeda )
      val freeVarList = freeVariables( e ).toList.sortBy( _.toString ).asInstanceOf[List[HOLExpression]]
      if ( freeVarList.isEmpty )
        ( scope_, Const( sym, e.exptype ) )
      else {
        val c = Const( sym, FunctionType( e.exptype, freeVarList.map( _.exptype ) ) )
        ( scope_, Function( c, freeVarList ) )
      }
    case _ =>
      throw new Exception( "Unhandled case in abstraction replacement!" + e )

  }
}

object undoReplaceAbstractions extends undoReplaceAbstractions
/**
 * Replaces the constants introduced by [[replaceAbstractions]] with the original lambda-abstractions.
 */
class undoReplaceAbstractions {
  import replaceAbstractions.ConstantsMap

  def apply( fs: FSequent, map: ConstantsMap ): FSequent = FSequent(
    fs.antecedent.map( apply( _, map ) ),
    fs.succedent.map( apply( _, map ) ) )
  def apply( e: HOLExpression, map: ConstantsMap ): HOLExpression = {
    val stringsmap = map.map( x => ( x._2.toString(), x._1 ) ) //inverting the map works because the symbols are unique
    getAllPositions2( e ).foldLeft( e )( ( exp, position ) =>
      //we check if the position is a constant with an abstraction symbol
      position._2 match {
        case Const( name, _ ) if stringsmap.contains( name ) =>
          //if yes, we replace it by the original expression
          Replacement( position._1, stringsmap( name ) )( exp )
        case _ => exp
      } )
  }
}

object convertHolToFol extends convertHolToFol
/**
 * In contrast to [[reduceHolToFol]], we recreate the term via the fol constructors but
 * do not try to remove higher-order content.
 */
class convertHolToFol {
  def apply( fs: FSequent ): FSequent =
    FSequent( fs.antecedent.map( apply ), fs.succedent.map( apply ) )

  def apply( e: HOLFormula ): FOLFormula = e match {
    case Atom( Const( sym, exptype ), args ) if ( args.filterNot( _.exptype == Ti ).isEmpty ) =>
      FOLAtom( sym, args map apply )

    case Neg( x )                      => Neg( apply( x ) )
    case And( x, y )                   => And( apply( x ), apply( y ) )
    case Or( x, y )                    => Or( apply( x ), apply( y ) )
    case Imp( x, y )                   => Imp( apply( x ), apply( y ) )
    case AllVar( x @ Var( _, Ti ), t ) => AllVar( apply( x ).asInstanceOf[Var], apply( t ) )
    case ExVar( x @ Var( _, Ti ), t )  => ExVar( apply( x ).asInstanceOf[Var], apply( t ) )

    case Var( x, Ti )                  => FOLVar( x )
    case Const( x, Ti )                => FOLConst( x )
    case Function( Const( f, FunctionType( Ti, _ ) ), args, Ti ) if ( args.filterNot( _.exptype == Ti ).isEmpty ) =>
      FOLFunction( f, args map apply )

    case _ => throw new Exception( "Could not convert term " + e + " to first order!" )
  }

}

/**
 * Introducing abstractions and converting to fol changes more complex types to fol compatible ones. With changeTypeIn
 * you can change them back.
 */
object changeTypeIn {
  type TypeMap = Map[String, TA]

  /* TODO: this broken, since e.g. for (a b) q with type(q)=alpha, type(b)=beta then type(a)=beta > (alpha > gamma)
     we need to actually change the type of a when changing the type of q
    */
  /*
  def oldapply(e:LambdaExpression, tmap : TypeMap) : LambdaExpression = e match {
    case Var(name, ta) =>
      if (tmap.contains(name.toString()))
        e.factory.createVar(name, tmap(name.toString()))
      else
        e
    case App(s,t) => s.factory.createApp(oldapply(s,tmap), oldapply(t,tmap))
    case Abs(x,t) => t.factory.createAbs(oldapply(x,tmap).asInstanceOf[Var], oldapply(t,tmap))
  } */

  //Remark: this only works for changing the type of leaves in the term tree!
  def apply( e: HOLExpression, tmap: TypeMap ): HOLExpression = e match {
    case Var( name, ta ) => if ( tmap contains name.toString() ) Var( name, tmap( name.toString() ) ) else
      Var( name, ta )
    case Const( name, ta ) => if ( tmap contains name.toString() ) Const( name, tmap( name.toString() ) ) else
      Const( name, ta )
    case Function( Const( f, exptype ), args, rv ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val freturntype = exptype match { case FunctionType( r, _ ) => r }
      val f_ = Const( f, FunctionType( freturntype, args.map( _.exptype ) ) )
      Function( f_, args_ )
    case Function( Var( f, exptype ), args, rv ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val freturntype = exptype match { case FunctionType( r, _ ) => r }
      val f_ = Var( f, FunctionType( freturntype, args.map( _.exptype ) ) )
      Function( f_, args_ )
    case Atom( Const( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val f_ = Const( f, FunctionType( To, args.map( _.exptype ) ) )
      Atom( f_, args_ )
    case Atom( Var( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val f_ = Var( f, FunctionType( To, args.map( _.exptype ) ) )
      Atom( f_, args_ )
    case Neg( x )       => Neg( apply( x, tmap ) )
    case And( s, t )    => And( apply( s, tmap ), apply( t, tmap ) )
    case Or( s, t )     => Or( apply( s, tmap ), apply( t, tmap ) )
    case Imp( s, t )    => Imp( apply( s, tmap ), apply( t, tmap ) )
    case AllVar( x, t ) => AllVar( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case ExVar( x, t )  => ExVar( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case Abs( x, t )    => Abs( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case App( s, t )    => App( apply( s, tmap ), apply( t, tmap ) )
    case _              => throw new Exception( "Unhandled case of a HOL Formula! " + e )

  }
  def apply( fs: FSequent, tmap: TypeMap ): FSequent = FSequent( fs.antecedent.map( x => apply( x, tmap ) ),
    fs.succedent.map( x => apply( x, tmap ) ) )

  //different names bc of type erasure
  private def holsub( s: Substitution, tmap: TypeMap ): Substitution = Substitution(
    s.map.map( x =>
      ( apply( x._1, tmap ).asInstanceOf[Var], apply( x._2, tmap ) ) ) )

  private def folsub( s: Substitution, tmap: TypeMap ): Substitution = Substitution( s.map.map( x =>
    ( apply( x._1, tmap ).asInstanceOf[Var], apply( x._2, tmap ) ) ) )
}

