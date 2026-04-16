// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  Contract (
    Requires (
      y >= 0 //needed to prevent infinite recursion
    ),
    Ensures (
      Res[Z] == x * y
    )
  )
  //what goes here?
  //what should we require?
  //what should we ensure?

  var answer: Z = 0

  if (y == 0) {
    answer = 0
  
    Deduce (
      1 ( y == 0 ) by Premise, //if condition is true
      2 ( y >= 0 ) by Premise, //precondition
      3 ( answer == 0 ) by Premise, //assignment statement
      4 ( x * y == 0 ) by Algebra*(1), //multiplication by 0
      5 ( answer == x * y ) by Algebra*(3,4) //postcondition
    )

    //what do we need to do here?
    //need: answer == x * y
  } else {
    //what do we need to show here?
    //prove precondition for recursive call ( y - 1 )

    Deduce (
      1 ( y >= 0 ) by Premise, //precondition
      2 ( !( y == 0 ) ) by Premise, //for the else branch
      3 ( y != 0 ) by Algebra*(2),
      4 ( y > 0 ) by Algebra*(1,2),
      5 ( y - 1 >= 0) by Algebra*(3,4) //proves precondition for the recursive call
      //need y - 1 >= 0 to prove precondition
    )

    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce (
      1 ( temp == ( x * (y - 1) ) ) by Premise, //from postcondition of recursive call
      2 ( answer == x + temp ) by Premise, //from assignment statement
      3 ( answer == x + (x * (y - 1)) ) by Algebra*(1,2),
      4 ( answer == x + x*y - x ) by Algebra*(3),
      5 ( answer == x * y ) by Algebra*(4),
    )

    //what do we need to show here?
    //need: answer == x * y
  }

  //what do we need to do here?
  //need: answer == x * y
  Deduce (
    1 ( answer == x * y ) by Premise //true in both branches and proves postcondition
  )

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//what do we need here?
//prove precondition: b >= 0

Deduce ( 
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1)
)

var ans: Z = mult(a, b)

Deduce (
  1 ( a == 5 ) by Premise,
  2 ( b == 4 ) by Premise,
  3 ( a * b == 20 ) by Algebra*(1,2),
  4 ( ans == a * b ) by Premise, //postcondition
  5 ( ans == 20 ) by Subst_<(3,4)
)

//what do we want to assert that ans is?

assert (ans == 20)