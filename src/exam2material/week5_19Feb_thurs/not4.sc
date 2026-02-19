// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not4(p: B, q: B, r: B): Unit = {
  Deduce(
    //finish proving contrapositive equivalence
      ( !q __>: !p )|- ( p __>: q )
      Proof(
        1 (  !q __>: !p ) by Premise,

        //use ImplyI pattern to prove p __>: q
        2 SubProof(
          3 Assume( p ),

          //no pattern, try PbC to get to q goal
          4 SubProof(
            5 Assume (!q),
            6 ( !p ) by ImplyE(1, 5),
            7 ( F ) by NegE(3, 6)

            //goal: F
          ),
          8 ( q ) by PbC(4)

          //goal: q
        ),
        9 ( p __>: q ) by ImplyI(2)
    )
  )
}