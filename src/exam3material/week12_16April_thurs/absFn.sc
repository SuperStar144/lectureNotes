// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    //no preconditions
    Ensures(
      Res[Z] >= 0,
      Res[Z] == -1*numOrig | Res[Z] == numOrig
    )
  )

  var num: Z = numOrig

  //update num to be the absolute value of the input
  if (num < 0) {
    num = num * -1

    Deduce(
    1 ( Old(num) < 0 ) by Premise, //condition was true for old num val
    2 ( Old(num) == numOrig ) by Premise, //assignment statement, num has changed
    3 ( num == Old(num) * -1 ) by Premise, //assignment statement, num has changed
    4 ( num >= 0 ) by Algebra*(1,3),
    5 ( num == -1* numOrig ) by Algebra*(2,3)
  )
  } else {
    //do nothing -- num is already its own absolute value
    Deduce(
      1 ( !(num < 0 ) ) by Premise, //condition is false
      2 ( num == numOrig) by Premise, //assignment statement
      3 ( num >= 0 ) by Algebra*(1)
    )
  }

  //what can we say here?
  //what do we need to prove by the end of the function?

  Deduce(
    1 ( num >= 0 ) by Premise, //true in both branches
    2 ( num == -1*numOrig | num == numOrig ) by Premise, //LHS true in if, RHS true in else
    //need: num >= 0
    //need: num == -1*numOrig | num == numOrig
  )

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?
val calc: Z = absVal(x)

//THURSDAY: finish from here

// calc >= 0
// calc == -1*x | calc == x

//what should we be able to assert?
assert(calc == 4)