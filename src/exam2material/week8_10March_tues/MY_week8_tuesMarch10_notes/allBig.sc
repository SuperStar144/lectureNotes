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
      //AllI
      4 Let ((random: T) => SubProof (
        5 ( P(random) __>: B(random) ) by AllE[T](1),
        6 ( Q(random) __>: C(random) ) by AllE[T](2),
        7 ( R(random) __>: !B(random) & !C(random) ) by AllE[T](3),
        //ImplyI
        8 SubProof (
          9 Assume ( P(random) | Q(random) ),
          //OrE
          10 SubProof (
            11 Assume ( P(random) ),
            12 ( B(random) ) by ImplyE(5, 11),
            //NegI
            13 SubProof (
              14 Assume R(random),
              15 ( !B(random) & !C(random) ) by ImplyE(7, 14),
              16 ( !B(random) ) by AndE1(15),
              17 ( F ) by NegE(12, 16)
              //goal: F
            ),
            18 ( !R(random) ) by NegI(13),
            //goal: !R(random)
          ),
          //OrE pt 2
          19 SubProof (
            20 Assume ( Q(random) ),
            21 ( C(random) ) by ImplyE(6, 20),
            //NegI
            22 SubProof (
              23 Assume R(random),
              24 ( !B(random) & !C(random) ) by ImplyE(7, 23),
              25 ( !C(random) ) by AndE2(24),
              26 ( F ) by NegE(21, 25)
              //goal: F
            ),
            27 ( !R(random) ) by NegI(22),
            //goal: !R(random)
          ),
          28 ( !R(random) ) by OrE(9,10,19)
          //goal: !R(random)
        ),
        29 ( P(random) | Q(random) __>: !R(random) ) by ImplyI(8),
        //goal: P(random) | Q(random) __>: !R(random)
      )),
      30 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x))) ) by AllI[T](4)
    )
  )
}