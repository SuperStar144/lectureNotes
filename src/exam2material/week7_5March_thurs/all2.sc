// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (P(x) ⋀ Q(x))    equivalent to     (∀ x P(x)) ⋀ (∀ x Q(x))

@pure def all2part1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
      |-
    (
       ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
    Proof(
      1 (∀((x: T) => (P(x) & Q(x)))) by Premise,

      //use AllI to get ∀((x: T) => P(x))
      2 Let( (random: T) => SubProof(
        3 ( P(random) & Q(random) ) by AllE[T](1),
        4 ( P(random) ) by AndE1(3)

        //goal: P(random)
      )),
      5 ( ∀((x: T) => P(x)) ) by AllI[T](2),

      //use AllI to get ∀((x: T) => P(x))
      6 Let( (random2: T) => SubProof(
        7 ( P(random2) & Q(random2) ) by AllE[T](1),
        8 ( Q(random2) ) by AndE2(7)

        //goal: P(random)
      )),
      9 ( ∀((x: T) => Q(x)) ) by AllI[T](6),

      10 ( ∀((x: T) => P(x)) & ∀((x: T) => Q(x)) ) by AndI(5, 9)

      //goal: prove ∀((x: T) => P(x))
    )
  )
}


@pure def all2part2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
      |-
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
    Proof(
      1 (  ∀((x: T) => P(x)) & ∀((x: T) => Q(x))  ) by Premise,
      
      //this would be good practice
      //use AndE to get ∀((x: T) => P(x)) and also ∀((x: T) => Q(x))

      2 ( ∀((x: T) => P(x)) ) by AndE1(1),
      3 ( ∀((x: T) => Q(x)) ) by AndE2(1),

      4 Let ((random: T) => SubProof(
        5 ( P(random)  ) by AllE[T](2),
        6 ( Q(random) ) by AllE[T](3),
        7 ( P(random) & Q(random) ) by AndI(5, 6)

        //need: P(random) & Q(random)
      )),
      8 ( ∀((x: T) => (P(x) & Q(x))) ) by AllI[T](4)

      //goal: ∀((x: T) => (P(x) & Q(x)))
    )
  )
}