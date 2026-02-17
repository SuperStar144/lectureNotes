// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def ex1(a: B, b: B, c: B, d: B, p: B, q: B, r: B): Unit = {
  Deduce(
    ( a & b & c & d ) |- ( p | b | q | r )
      Proof(
        1 ( a & b & c & d ) by Premise,

        // need b
        2 ( a & b & c ) by AndE1(1),
        3 ( a & b ) by AndE1(2),
        4 ( b ) by AndE2(3),

        //build conclusion
        //first need p | b | q 
        //first build p | b

        5 ( p | b ) by OrI2(4),
        6 ( p | b | q ) by OrI1(5),
        7 ( p | b | q | r ) by OrI1(6)

    )
  )
}