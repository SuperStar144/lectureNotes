// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(list.size > 0),
        Ensures(
            //nothing in sequence is changing
            //still need to describe the return value
            
            //whatever it is returning is <= every element in the sequence
            ∀ (0 until list.size) (k => Res[Z] <= list(k)),

            //whatever we are returning IS one of our elements
            ∃ (0 until list.size) (k => Res[Z] == list(k))
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),

            //bound the loop counter
            i >= 1, i <= list.size,

            //don't need to say size doesn't change because list isn't changing

            //small is the smallest I've looked at SO FAR
            ∀ (0 until i) (k => small <= list(k)),

            //small IS one of the elements I've looked at so far
            ∃ (0 until i) (k => small == list(k))
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