// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires(adult >= 0, kid >= 0),
    Ensures(Res[Z] == adult*50 + kid*30, Res[Z] >= 0)
  )


  //what to do here?


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here?

  Deduce (
    1 (overall == adult*50 + kid*30) by Premise,
    2 (adult >= 0) by Premise, //first precondition
    3 (kid >= 0) by Premise, //second precondition
    //4 (overall == adult*50 + kid*30) by Algebra*(1), //proves first postcondition
    4 (overall >= 0) by Algebra*(1,2,3), //proves second postcondition
    //need to prove: both postconditions
  )

  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?

Deduce (
  1 (k == 3) by Premise,
  2 (a == 2) by Premise,
  3 (a >= 0) by Algebra*(2), //proves first precondition
  4 (k >= 0) by Algebra*(1) //proves second precondition
)

val cost: Z = getTicketCosts(a, k)

//what to do here?

Deduce (
  1 (cost == a*50 + k*30) by Premise, //by first postcondition
  2 (k == 3) by Premise, //still true
  3 (a == 2) by Premise, //still true
  4 (cost == 190) by Algebra*(1,2,3) //proves assert
)

//what *should* cost be?

assert(cost == 190)