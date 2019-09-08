package gapt.provers.iescargot

import gapt.expr._
import gapt.utils.verbose
import org.specs2.mutable._

class IEscargotTest extends Specification {

  "lem 1" in {
    verbose( IEscargot.getLKProof(
      hos"""
            !x (p x | ~ p x) :- ~ ~ p c -> p c
         """ ) ) must beSome
  }

}
