// #Sireum #Logika

//∀ ∃

import org.sireum._

var balance: Z = 0
var elite: B = F
val eliteMin: Z = 1000000 // $1M is the minimum balance for elite members

//these are the global invariants
@spec def inv = Invariant(
  balance >= 0, //balance should not be negative
  elite == (balance >= eliteMin)    //elite flag should correspond to 
                            //whether we are over 1000000
)

def deposit(amount: Z): Unit = {
    Contract(
        Requires(amount >= 0),
        Modifies(balance, elite),
        Ensures(
            //describe how the global variables change
            balance == In(balance) + amount

            //unwritten postconditions (so I don't need them again):
            //balance >= 0
            //elite == (balance >= eliteMin)
        )
    )
    //unwritten precondition about the global invariants?
    //unwritten postcondition about the global invariants?

    balance = balance + amount

    if (balance >= eliteMin) {
        elite = true
    }
}

def withdraw(amount: Z): Unit = {
    Contract(
        //don't allow balance to become negative
        Requires(
            amount <= balance,
            amount >= 0
        ),
        Modifies(balance, elite),
        Ensures(
            balance == In(balance) - amount

            //unwritten postconditions (so I don't need them again):
            //balance >= 0
            //elite == (balance >= eliteMin)
        )
    )

    //unwritten precondition about the global invariants?
    //unwritten postcondition about the global invariants?

    balance = balance - amount

    if (balance < eliteMin) {
        elite = false
    }
}

//////////////// Test code /////////////////////

deposit(500000)
assert(balance == 500000 & !elite)
deposit(600000)
assert(balance == 1100000 & elite)
withdraw(150000)
assert(balance == 950000 & !elite)
deposit(200000)
assert(balance == 1150000 & elite)