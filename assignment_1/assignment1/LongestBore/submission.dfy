// Please, before you do anything else, add your names here:
// Group:    32
// Member 1: Constantinof Alexia: 2130793
// Member 2: Dediu David: 2096676

include "assignment.dfy"
 
/**
    Make sure this file and the file tests.dfy verify.
    Verification of tests.dfy is only dependent on the contract of this method, 
    not on its implementation. 
  */
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method LongestBoringSubsequence(a: seq<int>) returns (start: int, len: int)
      // postcondition repeated for your convenience  
      ensures 0 <= start <= start + len <= |a|
      ensures isBoring(a, start, start+len)
      ensures forall i, j :: 0 <= i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len // Boring subsequence may not be longer than sequence.
    {
      var c_start: int;
      var c_len: int;
      
      // index in sequence
      var i := 0;
      start, c_start := i, i;
      len, c_len := 0, 0; // this is fine, since we start with i = 0, len/c_len will immediately go to 1 if |a| >= 1 which is not guaranteed.
      

      while (i < |a|) 
        invariant 0 <= i <= |a| // defined this way

        invariant 0 <= c_start <= i // current start cannot exceed current analyzed element
        invariant c_start + c_len == i // current subsequence corresponds to that of the last analyzed element a[i]

        invariant 0 <= start <= i // start cannot exceed current analyzed element as well
        invariant start + len <= i // end of largest subsequence (currently) cannot be further that we have analyzed so far.

        invariant isBoring(a, start, start + len) // maintained maximum is boring
        invariant isBoring(a, c_start, c_start + c_len) // sequence corresponding to current element is boring

        invariant c_start > 0 && c_start < |a| ==> a[c_start] != a[c_start - 1] // start of current subsequence cannot be shifted to the right to increase its length, so its maximal for the current i.
        // this also implies that given the subsequence a[0..i], c_start is the optimal and c_len is the largest it can be for the current a[i]
        invariant forall p, q :: 0 <= p <= q <= i && isBoring(a, p, q) ==> q - p <= len // maintained maximum is maximum for the subsequence a[0..i]
        // len is updated via c_len which is ensured to be maximal by the previous invariant
      {
        //update the current subsequence accordingly, 2 cases, either continue or reset
        if (a[i] == a[c_start]) {

          //same sequence, continue it
          c_len := c_len + 1;

        } else {
          //new sequence
          assert a[i] != a[c_start];

          c_start := i;
          c_len := 1;

          assert a[c_start - 1] != a[c_start];

        }

        // update longest sequence based on current sequence, if its longer replace, else ignore
        if (c_len > len) {
          len := c_len;
          start := c_start;
        } // else do nothing.
        i := i + 1;
      }
      //loop ends so guard fails, combine that with invariant 1 and get that:
      assert i == |a|;

      //resulting from invariants + assertion above:

      assert 0 <= start <= |a|;
      assert start + len <= |a|;
      // therefore, postcondition 1 
      assert 0 <= start <=start + len <= |a|;

      //postconditions 2 and 3 follow from invariant termination directly.
      assert isBoring(a, start, start + len); 
      assert forall p, q :: 0 <= p <= q <= |a| && isBoring(a, p, q) ==> q - p <= len; 
    }

}
