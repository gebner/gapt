package gapt.provers.thinsnail

trait TermOrdering {
  def lt( e1: Term, e2: Term ): Boolean = lt( e1, e2, treatVarsAsConsts = false )
  def lt( e1: Term, e2: Term, treatVarsAsConsts: Boolean ): Boolean
}

case class LPO( precedence: Seq[FnSym] = Seq() ) extends TermOrdering {
  val precIdx: Map[FnSym, Int] = precedence.zipWithIndex.toMap

  def lt( e1: Term, e2: Term, treatVarsAsConsts: Boolean ): Boolean = {
    def majo( s: Term, ts: List[Term] ): Boolean =
      ts.forall( t => lpo( s, t ) )

    def alpha( ss: List[Term], t: Term ): Boolean =
      ss.exists( s => s == t || lpo( s, t ) )

    def precGt( h1: Term, h2: Term ): Boolean =
      ( h1, h2 ) match {
        case ( IsCon( c1 ), IsCon( c2 ) ) =>
          precIdx.getOrElse( c1, -1 ) > precIdx.getOrElse( c2, -1 )
        case ( IsCon( _ ), IsVar( _ ) ) if treatVarsAsConsts => true
        case ( IsVar( v1 ), IsVar( v2 ) ) if treatVarsAsConsts => v1.idx > v2.idx
        case _ => false
      }

    def lexMa( s: Term, t: Term, ss: List[Term], ts: List[Term] ): Boolean =
      ( ss, ts ) match {
        case ( si :: sss, ti :: tss ) =>
          if ( si == ti ) lexMa( s, t, sss, tss )
          else if ( lpo( si, ti ) ) majo( s, tss )
          else alpha( ss, t )
        case _ => false
      }

    object Apps {
      def unapply( t: Term ): Some[( Term, List[Term] )] =
        t match {
          case IsCon( c ) => Some( ( c, Nil ) )
          case IsFn( f )  => Some( ( f.fnSym, f.args.toList ) )
          case IsVar( v ) => Some( ( v, Nil ) )
        }
    }

    def lpo( s: Term, t: Term ): Boolean = {
      //      if ( typeOrderLt( t.ty, s.ty ) ) return true
      val Apps( sf, sas ) = s
      val Apps( tf, tas ) = t
      if ( precGt( sf, tf ) ) majo( s, tas )
      else if ( sf == tf ) lexMa( s, t, sas, tas )
      else alpha( sas, t )
    }

    lpo( e2, e1 )
  }
}

