// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? don't need one


x = x + 1

Deduce(
    1 ( Old(x) > 0 ) by Premise, //x WAS > 0 just before the
                                //latest change
    2 ( x == Old(x) + 1 ) by Premise, //I just added one to x
    3 ( orig == Old(x) ) by Premise, //orig equaled the old value of x
    4 ( x == orig + 1 ) by Subst_>(3, 2),
    5 ( x > 1 ) by Algebra*(1,2)

    //want: x > 1
)

//what can we put in a proof block here?
//what should we be able to assert about x and orig?

x = x + 2

Deduce(
    1 ( x == Old(x) + 2 ) by Premise, //process assignment
    2 ( Old(x) == orig + 1 ) by Premise, //this was true in
                        //prior proof block, but x has changed

    3 ( x == orig + 1 + 2 ) by Subst_<(2, 1),
    4 ( x == orig + 3 ) by Algebra*(3),
    //need: x == orig + 3
    //need: x > 3

    5 (  Old(x) > 1 ) by Premise, //showed in previous block
                                //before latest x change
    6 ( x > 3 ) by Algebra*(1, 5),
    7 ( x == orig + 3 & x > 3 ) by AndI(4, 6)
)


//what can we put in a proof block here?



//what do we want to assert? How has x changed?

assert( x == orig + 3 & x > 3 )


//Once it is working - if x was originally positive,
//how could we assert that x was still positive at the end?