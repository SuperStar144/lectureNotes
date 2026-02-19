// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//proves the contrapositive
@pure def not3(p: B, q: B, r: B): Unit = {
  Deduce(
    //what is this? contrapositive
    ( p __>: q ) |- ( !q __>: !p  )
      Proof(
      1 (  p __>: q ) by Premise,

      //look at top-level operator of conclusion
      // __>: 
      //ImplyI pattern to introduce the implies
      2 SubProof(
        3 Assume(!q),

        //follow NegI pattern to prove our !p goal
        4 SubProof(
          5 Assume(p),
          6 ( q ) by ImplyE(1, 5),
          7 ( F ) by NegE(6, 3)

          //goal: F
        ),
        8 ( !p ) by NegI(4)

        //goal: !p
      ),
      9 ( !q __>: !p ) by ImplyI(2)
    )
  )
}