// #Sireum #Logika

import org.sireum._

def mult(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var sum: Z = 0
    var count: Z = 0

    //measure of work? (how many more iterations left?)
    //initially? y more iterations
    //after 1 iteration? y-1 more iterations

    //in general? y-count (measure of work)

    while (count < y) {
        Invariant(
            Modifies(sum, count),
            count <= y,
            sum == x*count
        )

        //calculate y-count here

        sum = sum + x
        count = count + 1

        //calculate y-count here


        //measure should decrease with each iteration
            //does it? yes, gets one smaller each time

        //when I have no work left, then my loop should be done
            //is it? 
            //measure of work, y - count == 0.
            //means y == count
            //loop condition would be false
    }

    return sum
}

/*
We claim that multRec terminates for y>= 0 (y is an integer).

Base case. We must show that our function terminates when y == 0
(the smallest value in our domain). When y is 0, we immediately return.

Inductive step. We assume the inductive hypothesis - that 
multRec terminates for some fixed y=k >= 0, k is an integer
(i.e., the second parameter).

We must show that multRec terminates when our second paramter (y)
is k+1. We would go into the else because k+1 must be at least 1.
There, we make a recursive call, passing y-1 (or k+1-1 = k) as the
second parameter. (Really, calling multRec(x, k)). By our inductive 
hypothesis, that recursive call terminates.
At that point we just do addition/return, so we also terminate.
*/

def multRec(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var answer: Z = 0

    if (y == 0) {
        answer = 0
    } else {
        var temp: Z = multRec(x, y-1)
        answer = x + temp
    }

    return answer
}

def collatz(n: Z): Z = {
    Contract(
        Requires(n > 0),
        Ensures(Res[Z] == 1)
    )

    //what if n is 52?
    //cur = 52 -> 26 -> 13 -> 40 -> 20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1

    var cur: Z = n
    while (cur > 1) {
        Invariant(
            Modifies(cur),
            cur >= 1        //what else could we say?
        )

        if (cur % 2 == 0) {
            cur = cur / 2
        } else {
            cur = 3 * cur + 1
        }
    }

    return cur
}