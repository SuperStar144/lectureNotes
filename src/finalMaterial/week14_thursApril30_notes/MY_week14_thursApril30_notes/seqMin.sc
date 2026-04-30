// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract (
        Requires(
            list.size > 0
        ),
        //doesn't modifies anything
        Ensures (
            //nothing in the sequence is changing
            //still need to describe the return value

            //whatever it's returning is less than or equal to every number in the sequence
            ∀(0 until list.size)(k => Res[Z] <= list(k)),

            //the return value is contained in the array
            ∃(0 until list.size)(k => Res[Z] == list(k))
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),

            //bound the loop counter
            i >= 1, i <= list.size, //notice that i started at 0 !!

            //size doesn't change (not necessary here bc it's not being modified)

            //small is the smallest I've looked at so far
            ∀(0 until i)(k => small <= list(k)),

            //small is one of the elements I've looked at so far
            ∃(0 until i)(k => small == list(k))

            //notice that these are very similar to the postconditions, just adjusting to only looking
            //at what I've already looked at
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?

assert(testMin == 0)