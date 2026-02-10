// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( (p | q ) & (p | r) ) |- ( p | (q & r) )
      Proof(
        //PROOF GOES HERE
        1 ((p | q ) & (p | r)) by Premise,
        2 ( p | q ) by AndE1(1),
        3 ( p | r ) by AndE2(1),

        //OrE cases on p | q
        4 SubProof (
          5 Assume ( p ), 
        )

        //another subproof, assume q
    )
  )
}