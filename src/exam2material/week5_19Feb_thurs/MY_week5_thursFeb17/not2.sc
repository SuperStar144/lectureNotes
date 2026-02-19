// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not2(p: B, q: B, r: B): Unit = {
  Deduce(
    //what is this? DeMorgan's
    //does this prove equivalence? no, must complete a proof both ways
    ( !p & !q ) |- ( !(p | q)  )
      Proof(
        1 (  !p & !q ) by Premise,
        2 ( !p ) by AndE1(1),
        3 ( !q ) by AndE2(1),
    )
  )
}