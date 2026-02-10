// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def ex3(a: B, b: B, c: B, p: B, q: B, r: B, s: B, t: B): Unit = {
  Deduce(
    ( b & (s | a), s __>: b __>: p, a & b __>: t, p | t __>: q __>: r, b | c __>: q ) |- ( r )
      Proof(
      1 (  b & (s | a)   ) by Premise,
      2 (  s __>: b __>: p   ) by Premise,
      3 ( a & b __>: t ) by Premise,
      4 ( p | t __>: q __>: r ) by Premise,
      5 ( b | c __>: q ) by Premise,
      
      //what can we get right away from the premises?
      6 ( b ) by AndE1(1),
      7 ( s | a ) by AndE2(1),
      8 ( b | c ) by OrI1(6),
      9 ( q ) by ImplyE(5, 8),

      //use OrE on s | a
      10 SubProof(
    11 Assume(s),
  12 ( b __>: p ) by ImplyE(2, 11),
        13 ( p ) by ImplyE(12, 6),
  14 ( p | t ) by OrI1(13)
        //goal: p | t
      ),
      15 SubProof(
        16 Assume(a),
        17 ( a & b ) by AndI(16, 6),
        18 ( t ) by ImplyE(3, 17),
        19 ( p | t ) by OrI2(18)
        //goal: p | t
      ),
      20 ( p | t ) by OrE(7, 10, 15),
      21 ( q __>: r ) by ImplyE(4, 20),
      22 ( r ) by ImplyE(21, 9)
      //subproof assume a, goal: p | t

      //goal: r
    )
  )
}