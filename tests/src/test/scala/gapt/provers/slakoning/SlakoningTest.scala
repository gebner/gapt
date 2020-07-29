package gapt.provers.slakoning

import gapt.expr._
import gapt.utils.verbose
import org.specs2.mutable._

class SlakoningTest extends Specification {

  "lem 1" in {
    verbose( Slakoning.getLKProof(
      hos"""
            !x (p x | ~ p x) :- ~ ~ p c -> p c
         """ ) ) must beSome
  }

}
