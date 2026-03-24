// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,

      //no individual available, can't use AllE on premises yet

      //use AllI subproof to create my conclusion
      4 Let ((random: T) => SubProof(
        //use ImplyI pattern to build my goal
        5 SubProof(
          6 Assume(  P(random) | Q(random) ),

          //use NegI pattern to build my goal
          7 SubProof(
            8 Assume( R(random) ),

            //use AllE with random on all premises
            9 ( P(random) __>: B(random) ) by AllE[T](1),
            10 ( Q(random) __>: C(random) ) by AllE[T](2),
            11 ( R(random) __>: !B(random) & !C(random) ) by AllE[T](3),
            12 ( !B(random) & !C(random) ) by ImplyE(11, 8),
            13 ( !B(random) ) by AndE1(12),
            14 ( !C(random) ) by AndE2(12),

            //try OrE to see if we can get to goal of F in both cases
            15 SubProof(
              16 Assume ( P(random) ),
              17 ( B(random) ) by ImplyE(9, 16),
              18 ( F ) by NegE(17, 13)
              //goal: F
            ),
            19 SubProof(
              20 Assume ( Q(random) ),
              21 ( C(random) ) by ImplyE(10, 20),
              22 ( F ) by NegE(21, 14)

              //goal: F
            ),
            23 ( F ) by OrE(6, 15, 19)

            //goal: F
          ),
          24 ( !R(random) ) by NegI(7)

          //goal: !R(random)
        ),
        25 ( P(random) | Q(random) __>: !R(random) ) by ImplyI(5)

        //goal: P(random) | Q(random) __>: !R(random)
      )),
      26 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x)  )) ) by AllI[T](4)
      //goal: ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
  )
}