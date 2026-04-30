// #Sireum #Logika

import org.sireum._

//"Unit" is like a void return type
def makeFirstZero(seq: ZS): Unit = {
  //how would we write the function contract?
  //what do we want to require of seq?
  //how can we describe how seq will change?
  Contract (
    Requires (
      seq.size > 0
    ),
    Modifies(seq),
    Ensures (
      seq(0) == 0,
      //every other position is unchanged (English definition), use for all.
      //sireum slang template insert for all range quantification (or just type "ALL")
      ∀(1 until seq.size)(k => seq(k) == In(seq)(k))
      //∀(0 until seq.size)(k => k != 2 __>: seq(k) == In(seq(k)))
    )
  )
  seq(0) = 0
}

///// Test code ///////////

var nums: ZS = ZS(1,2,3)
makeFirstZero(nums)

//---> what should we assert?
assert (nums == ZS(0,2,3))