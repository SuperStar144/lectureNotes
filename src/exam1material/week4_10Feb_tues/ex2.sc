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

        //try OrE on premise 1
        4 SubProof(
          5 Assume (a & b),
          6 ( a ) by AndE1(5),
          7 ( b ) by AndE2(5),
          8 ( a | d __>: p | q ) by ImplyE(2, 7),
          9 ( a | d ) by OrI1(6),
          10 ( p | q ) by ImplyE(8, 9)
          //goal: p | q
        ),
        11 SubProof(
          12 Assume(c),
          13 ( q ) by ImplyE(3, 12),
          14 ( p | q ) by OrI2(13)
          //goal: p | q
        ),
        15 ( p | q ) by OrE(1, 4, 11)
        //subproof assume c
    )
  )
}