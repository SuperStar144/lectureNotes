// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def lem(p: B): Unit = {
  Deduce(
    |- ( p | !p )
      Proof(
        //all theorems start with a subproof
        //only one that makes sense here is PbC
        1 SubProof( //PbC
          2 Assume (!(p | !p)),

          3 SubProof( //NegI
            4 Assume (p),
            5 ( p | !p ) by OrI1(4),
            6 ( F ) by NegE(5,2)
            //goal: F
          ),
          7 (!p) by NegI(3),
          8 ( p | !p ) by OrI2(7),
          9 ( F ) by NegE(8, 2)

          //try to get !p to build OR 
          //need p | !p to contradict with assume
          //goal: F
        ),
        10 (p | !p) by PbC(1)
    )
  )
}