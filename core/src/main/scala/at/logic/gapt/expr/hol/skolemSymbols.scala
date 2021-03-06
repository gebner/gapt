/*
 * SkolemSymbols.scala
 */

package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.utils.{ StreamUtils, NameGenerator }
import StreamUtils._

/* The idea of SkolemSymbolFactory is to provide
     a singleton for access to the (global) Skolem symbols.
     SkolemSymbolFactory provides
     (1) single Skolem symbols, and
     (2) streams of Skolem symbols.

     Every Skolem symbol is only returned once in both
     cases.

     This is realized by keeping a stream s of Skolem
     symbols internally, and upon request returning a stream
     consisting of the even indices of s, while keeping
     the odd indices of s.
   */

class SkolemSymbolFactory( usedConstants: Iterable[Const] ) {
  private var skolem_symbol_stream = new NameGenerator( usedConstants map { _.name } ).freshStream( "s" )

  def getSkolemSymbols = {
    val stream = even( skolem_symbol_stream )
    skolem_symbol_stream = odd( skolem_symbol_stream )
    stream
  }

  def getSkolemSymbol = {
    val sym = skolem_symbol_stream.head
    skolem_symbol_stream = skolem_symbol_stream.tail
    sym
  }
}
