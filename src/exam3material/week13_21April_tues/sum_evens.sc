// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires( n > 0),
    Ensures( Res[Z] == n*(n+1) )
  )

  var sum: Z = 0
  var cur: Z = 0

  //what can we list as premises?
  //sum == 0
  //cur == 0
  //n > 0

  //Need to prove:
  //ALL invariants
  //sum == cur*(cur+1)

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur, sum),
      sum == cur*(cur+1)
    )

    //what can we list as premises?
    //sum == cur*(cur+1)
    //cur != n
    //n > 0

    cur = cur + 1

    //need a Deduce block to process how cur changed
    //learn something about cur change that doesn't use "Old"

    sum = sum + 2*cur

    //NEED TO PROVE:
    //sum == cur*(cur+1)
  }

  //what could we list as premises?
  //!(cur != n)
  //sum == cur*(cur+1)
  //n > 0
  //sum == Old(sum) + 2*cur <-- NO. Don't say this.

  //need to prove?
  //sum == n*(n+1)

  return sum
}

//////////// test code /////////

val num: Z = 5

//what can be premises?
//num == 5

//need to prove?
//num > 0

var sum5evens: Z = sumEvens(num)

//what can be premises?
// sum5evens == num*(num+1)
// num == 5

//what do we need to prove?
//sum5evens == 30

//sum of first 5 evens: 2 + 4 + 6 + 8 + 10
assert(sum5evens == 30)
