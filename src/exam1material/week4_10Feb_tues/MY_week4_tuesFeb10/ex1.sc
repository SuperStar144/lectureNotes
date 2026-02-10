// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def ex1(a: B, b: B, c: B, d: B, p: B, q: B, r: B): Unit = {
  Deduce(
    ( a & b & c & d ) |- ( p | b | q | r )
      Proof(
        1 ( a & b & c & d ) by Premise,

    )
  )
}