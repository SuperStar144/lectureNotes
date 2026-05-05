// #Sireum #Logika

import org.sireum._

//∀ ∃

//set all elements to 10
def all10(nums: ZS): Unit = {
  //function contract?
  Contract(
    //no requirements needed
    Modifies(nums),
    Ensures(
      //all elements have changed to 10
      ∀(0 until nums.size) (k => nums(k) == 10)
    )
  )

  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?
    Invariant(
      Modifies(nums, i),
      //bound the loop counter
      i >= 0, i <= nums.size,

      //size doesn't change
      nums.size == In(nums).size,

      //what part HAS already changed
      ∀(0 until i) (k => nums(k) == 10),

      //what part has NOT changed (not needed in this example)
      ∀(i until nums.size) (k => nums(k) == In(nums)(k)),

      
    )


    nums(i) = 10
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

all10(test)

//what do we want to assert?
assert(test == ZS(10,10,10,10,10,10))