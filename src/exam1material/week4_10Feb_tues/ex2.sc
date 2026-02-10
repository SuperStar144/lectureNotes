// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def ex2(a: B, b: B, c: B, d: B, p: B, q: B): Unit = {
  Deduce(
    ( a & b | c, b __>: a | d __>: p | q, c __>: q ) |- ( p | q )
      Proof(
        1 ( a & b | c ) by Premise,
        2 ( b __>: a | d __>: p | q ) by Premise,
        3 ( c __>: q ) by Premise,


    )
  )
}