// Please, before you do anything else, add your names here:
// Group:    <Group number>
// Member 1: <Full name 1>: <Student number 1>
// Member 2: <Full name 2>: <Student number 2>

include "assignment.dfy"
 
module Submission refines Assignment {
  lemma EvenDoesNotDevideOdd(n: int, i: int)
        // The preconditions are the facts we knew at the point when we applied the lemma 
        // in the program, such as n is odd, n >= i >= 3 and i % 2 == 1.
        requires n % 2 == 1 
        requires n >= i >= 3
        requires i % 2 == 1
        // The postcondition is to prove that the even number we skip ( i + 1 ) does not 
        // divide n.
        ensures n % (i + 1) != 0
      {
      // Proof by contradiction that the even number we skip does not divide an odd n.
              assert n % (i + 1) != 0 by {
                // Assume an even number does devide an odd n.
                if n % (i + 1) == 0 {
                  // Let q be the quotient of n / (i + 1).
                  var q := n / (i + 1);
                  // Let m be the quotient of (i + 1) / 2.
                  var m := (i + 1) / 2;
                  // Since (i + 1) devides n, there is no remainder. Therefore, multiplying 
                  // (i + 1) with the quotient gives n.
                  // Since 2 devides i + 1, there is no remainder. Therefore, multiplying 
                  // 2 with the quotient gives i + 1.
                  assert n == (i + 1) * q;
                  assert i + 1 == 2 * m;
                  // Then n is a multiple of 2, so it is even. But n is odd, so we have proven 
                  // the contradiction.
                  assert n == 2 * (m * q); 
                }
              }
      }
      @TimeLimit(60)
      lemma NoDivisorFromIToN(n: int, i: int)
        // The preconditions are the facts we knew at the point when we applied the lemma 
        // in the program, such as n < i * i (negation of while statement), and the invariants 
        // of the loop.
        requires n >= i >= 3
        requires n < i * i
        requires forall k :: 1 < k < i ==> n % k != 0
        ensures !(exists k :: i <= k < n && n % k == 0)
      {
          assert !(exists k :: i <= k < n && n % k == 0) by {
            // Assume there exists a divider greater or equal to i for n is true. 
            if exists k :: i <= k < n && n % k == 0 { 
              // Pick k to be this divisor.
              var k :| i <= k < n && n % k == 0;
              // Let d be the quotient, which is also a devisor of n.
              var d := n / k;
              // d is greater than 1, because k < n.
              assert d > 1;
              // k * d = n, where n < i * i. So k * d < i * i 
              assert k * d == n;
              assert k * d < i * i;
              // Then i * i <= k * i, because  i <= k.
              assert i * i <= k * i;
              // Therefore, k * d < k * i. Since 1 < k, we conclude d < i.
              assert k * d < k * i;
              assert d < i;
              // Therefore, d is a divisor of n smaller than i.
              // But the invariant has proven that no number smaller or equal to i is a divisor
              // of n. We have shown a contradiction, so n % k != 0.
              assert n % d == 0; 
            }
          }
      }


    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method IsPrime(n: int) returns (b: bool)
      ensures b <==> prime(n) 
    {
      if (n > 1) {
        if (n == 2) {
          return true;
        } else if (n % 2 == 0) {
          return false;
        } else {
          var i : int := 3;
          while (i * i <= n)
            invariant 3 <= i <= n
            invariant i % 2 == 1
            invariant forall k :: 1 < k < i ==>  n % k != 0
          {

            if (n % i == 0) {
              return false;
            }

            //proves ( i + 1 ) does not devide n, so we can prove the third invariant
            EvenDoesNotDevideOdd(n, i);
            i := i + 2;
          }
          // We now know ( n < i * i) and forall k :: 1 < k < i ==>  n % k != 0.
          // To prove the predicate prime(n), we need to show that all values greater or equal 
          // than i do not divide n either.
          NoDivisorFromIToN(n, i);
          return true;
        }
      } else {
        return false;
      }
    }
}