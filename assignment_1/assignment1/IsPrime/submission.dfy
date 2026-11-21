// Please, before you do anything else, add your names here:
// Group:    32
// Member 1: Constantinof Alexia: <Student number 1>
// Member 2: Dediu David: 2096676
include "assignment.dfy"
 
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method IsPrime(n: int) returns (b: bool)
      ensures b <==> prime(n) // repeated for your convenience
    {
       // TODO 
    }

}
