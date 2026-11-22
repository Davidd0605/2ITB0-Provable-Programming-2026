// Please, before you do anything else, add your names here:
// Group:    32
// Member 1: Constantinof Alexia: 2130793
// Member 2: Dediu David: 2096676
include "assignment.dfy"

 // OPTIMISATIONS IMPLEMENTED: both (1) only odd divisors are checked, and
// (2) divisors are only checked up to sqrt(n) (loop guard i*i <= n).
//
// Proof approach:
//  - EvenDoesNotDevideOdd: skipping even i+1 is safe because an even number
//    can't divide an odd n (if it did, n would be a multiple of 2).
//  - NoDivisorFromIToN: no divisor exists in [i, n). Any divisor d there has a
//    partner p = n/d with p < i (since d*p = n < i*i), which the loop invariant
//    already ruled out. ProductDivisible shows p genuinely divides n.
module Submission refines Assignment {


    //==========================================

    // Prove i + 1   
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
    //==========================================

    // If n == p * d with p > 0, then p divides n.
    lemma ProductDivisible(n: int, d: int, p: int)
      requires p > 0
      requires n == p * d
      ensures n % p == 0
    {
      // Name the quotient and remainder of n divided by p.
      var q := n / p;
      var r := n % p;
      // Definition of division: n == p * q + r with 0 <= r < p.
      assert n == p * q + r;
      assert 0 <= r < p;
      // Since also n == p * d, the remainder is a multiple of p.
      assert p * (d - q) == r;
      // A multiple of p in the range [0, p) must be 0, so k == 0.
      var k := d - q;
      if k >= 1 {
        // then p * k >= p > r, contradiction
        assert p * k == p * (k - 1) + p;
        assert p * (k - 1) >= 0;
      } else if k <= -1 {
        // then p * k <= -p < 0 <= r, contradiction
        assert p * k == p * (k + 1) - p;
        assert p * (k + 1) <= 0;
      }
      assert k == 0;
      // so r == p * 0 == 0
      assert r == 0;
      assert n % p == 0;
    }
    //==========================================
    
    // There are no divisors in the complement.
    lemma NoDivisorFromIToN(n: int, i: int)
      requires 3 <= i <= n //invariant
      requires i % 2 == 1 // construction
      requires forall d :: 1 < d < i ==> n % d != 0 // invariant
      requires n < i * i // negation of guard.
      ensures forall d :: i <= d < n ==> n % d != 0 // rest is not divisor.
    {
      //forall introduction in order to prove it
      forall d | i <= d < n
        ensures n % d != 0
      {
        // d is now fixed arbitrary between i and n, remains to prove n % d != 0

        // assume for contradiction
        if (n % d == 0) {
          var p : int;
          p := n / d;
          ProductDivisible(n, d, p);
          assert n % p == 0;

          //remains to prove p is between 1 and i;
          // holds since d < n, p is at least 2.
          assert 1 < p;

          assert p * d == n;
          assert i <= d;
          assert 0 < i;
          assert p * i <= n;
          assert p * i < i * i;
          assert p < i;

          assert 1 < p < i;
          assert 1 < p < i && n % p == 0; // this contradicts precondition 3.
          assert false;

        }
        // so the negation is true
        assert n % d != 0;
      }
      // we have to prove that forall d between i and n, n % d != 0
      assert forall d :: i <= d < n ==> n % d != 0;
    }
    //==========================================

    @TimeLimit(60)
    method IsPrime(n: int) returns (b: bool)
      ensures b <==> prime(n) // repeated for your convenience
    {
      //base cases
      if ( n == 2) { // 2 is prime
        return true;
      }
      if ( n <= 1 || n % 2 == 0 ) { // 0, 1 and all even numbers that are not 2 are not prime
        return false;
      }
      // case where n > 2
      var i : int;
      i := 3;

      while (i * i <= n) // 3 * 3 <= 9 goes through and returns false
        invariant 3 <= i <= n
        invariant i % 2 == 1
        invariant forall d :: 1 < d < i ==> n % d != 0
      {
        // if i divides n, then n is not prime
        if (n % i == 0) {
          return false;
        }
        // Prove that if n is odd and i is also odd, then n cannot be divided by i+1, so we can skip it
        EvenDoesNotDevideOdd(n, i);
        i := i + 2;
      }
      // We now know ( n < i * i) and forall k :: 1 < k < i ==>  n % k != 0.
      // To prove the predicate prime(n), we need to show that all values greater or equal 
      // than i do not divide n either.
      NoDivisorFromIToN(n, i);
      assert forall d :: 1 < d < n ==> n % d != 0; //isPrime lemma
      return true; 
    }
    //==========================================
}
