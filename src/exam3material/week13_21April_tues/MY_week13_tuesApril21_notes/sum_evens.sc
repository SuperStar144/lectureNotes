// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract (
    Requires (
      n > 0
    ),
    Ensures (
      //Res[Z] == n*(n+1)
    )
  )

  var sum: Z = 0
  var cur: Z = 0

  //what can we list as premises?
  //sum == 0
  //cur == 0 
  //n > 0

  //need to prove:
  //ALL loop invariants
  //sum == cur*(cur+1)
  //do NOT need to prove loop condition

  while (cur != n) {
    //what about our loop invariant?
    Invariant (
      Modifies(cur, sum),
      //sum = cur*(cur+1)
    )

    //what can we list as premises?
    //invariant (like the inductive step, assuming the inductive hypothesis)
    //loop condition (cur != n)
    //preconditions

    cur = cur + 1

    //need a Deduce block to process how cur changed
    //learn something about cur change that doesn't use "Old"

    sum = sum + 2*cur

    //NEED TO PROVE:
    //ALL invariants ( sum = cur*(cur+1) )
  }

  //what could we list as premises?
  //negation of the loop condition
  //preconditions
  //invariant(s)

  //need to prove?
  //postconditions

  return sum
}

//////////// test code /////////

val num: Z = 5

//prove precondition
//premise: num == 5
//must prove precondition for whatever expression is being passed in to the function

//var sum5evens: Z = sumEvens(num)

//use postcondition to prove the result
//premises
//sum5evens = num*(num+1)
//num == 5

//sum of first 5 evens: ?
//assert(sum5evens == 30)