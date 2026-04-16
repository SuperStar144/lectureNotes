// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


if (num < 0) {
  num = num * -1

  Deduce(
    1 ( Old(num) < 0 ) by Premise, //condition was true for old num val
    2 ( numOrig == Old(num) ) by Premise, //assignment statement, num has changed
    3 ( num == Old(num) * -1 ) by Premise, //assignment statement, num has changed
    4 ( num >= 0 ) by Algebra*(1,3),
    5 ( num == -1* numOrig ) by Algebra*(2,3)
  )

  //need: num >= 0
  //need: num == -1*numOrig
} else {
  //no code, just for verification

  Deduce(
    1 ( !(num < 0 ) ) by Premise, //condition is false
    2 ( numOrig == num ) by Premise, //assignment statement
    3 ( num >= 0 ) by Algebra*(1),
    4 ( num == numOrig ) by Algebra*(2)
  )

  //need: num >= 0 
  //need: num == numOrig 
}

Deduce(
  1 ( num >= 0 ) by Premise, //true in both branches
  2 ( num == -1*numOrig | num == numOrig ) by Premise, //LHS true in if, RHS true in else
  //need: num >= 0
  //need: num == -1*numOrig | num == numOrig
)


//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
assert(num == -1*numOrig | num == numOrig)