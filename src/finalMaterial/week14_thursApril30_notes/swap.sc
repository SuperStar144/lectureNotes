// #Sireum #Logika

import org.sireum._

//∀ ∃

//want to write a swap function
def swap(nums: ZS, pos1: Z, pos2: Z): Unit = {
  //how to write?
  Contract(
    Requires(
      pos1 >= 0,
      pos1 < nums.size,
      pos2 >= 0,
      pos2 < nums.size
    ),
    Modifies(nums),
    Ensures(
      //"nums" means the value of nums at the END of the function
      //"In(nums)" means the value of nums at the BEGINNING of the function
      nums(pos1) == In(nums)(pos2),
      nums(pos2) == In(nums)(pos1),
      //also, every other element is unchanged
      ∀(0 until nums.size) (k => k != pos1 & k != pos2 __>: nums(k) == In(nums)(k))
    )
  )

  var temp: Z = nums(pos1)
  nums(pos1) = nums(pos2)
  nums(pos2) = temp

  //how to write contract?
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

swap(test, 2, 4)

assert(test == ZS(4,1,10,8,3,2))


//what do we want to assert?