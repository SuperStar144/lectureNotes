// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a
<<<<<<< HEAD
  
  Deduce (
    1 ( a > b ) by Premise, //condition is true
    2 ( max == a ) by Premise, //from assignment
    3 ( max >= a ) by Algebra*(2),
    4 ( max >= b ) by Algebra*(1,3)
=======

  Deduce(
    1 ( a > b ) by Premise, //condition is true
    2 ( max == a ) by Premise, //from assignment
    3 ( max >= a ) by Algebra*(2),
    4 ( max >= b ) by Algebra*(1, 2)

>>>>>>> 2bb8534ac685dd77a89b44d6366f5ed5aa733f16
    //need: max >= a, max >= b
  )
} else {
  max = b

<<<<<<< HEAD
  Deduce (
=======
  Deduce(
>>>>>>> 2bb8534ac685dd77a89b44d6366f5ed5aa733f16
    1 ( !(a > b) ) by Premise, //condition is not true
    2 ( max == b ) by Premise, //from assignment
    3 ( max >= b ) by Algebra*(2),
    4 ( a <= b ) by Algebra*(1),
<<<<<<< HEAD
    5 ( max >= a ) by Algebra*(4,3)
=======
    5 ( max >= a ) by Algebra*(3, 4)

>>>>>>> 2bb8534ac685dd77a89b44d6366f5ed5aa733f16
    //need: max >= a, max >= b
  )
}

<<<<<<< HEAD
Deduce (
  1 ( max == a | max == b ) by Premise, //LHS is true in if and RHS is true in else
  2 ( max >= a ) by Premise, //true in both branches
  3 ( max >= b ) by Premise //true in both branches
  //need: max >= a
  //need: max >= b
  //need: max == a | max == b
)

//how can we assert that we've found the max?
assert( max >= a)
assert( max >= b )
assert( max == a | max == b )
=======
Deduce(
  1 ( max == a | max == b ) by Premise, //LHS true in if, RHS is true in else
  2 ( max >= a ) by Premise, //true in both branches
  3 ( max >= b ) by Premise //true in both branches

  //need: max >= a
  //need: max >= b
  //need: max == a | max == b
)


//how can we assert that we've found the max?
assert(max >= a)
assert(max >= b)
assert(max == a | max == b)
>>>>>>> 2bb8534ac685dd77a89b44d6366f5ed5aa733f16
