/-
  Optional evaluation/demo file for the formalisation in `Main.lean`.

  This file is not needed for the proof; it merely prints the computed facts so
  a reviewer can read them off directly. Run with

      lake env lean Eval.lean
-/

import Main

open Tlmc3485

-- The number of kernels of C₅, found by brute force over the 32 subsets.
#eval kernelMasks5.length            -- expected: 0
#eval kernelMasks5                  -- expected: []

-- The out-degrees of the five vertices of C₅.
#eval V5.map outDeg5                -- expected: [1, 1, 1, 1, 1]

-- Directed girth: no closed walk of length 1..4, and one of length 5.
#eval V5.map (fun i => walk5 4 i i) -- expected: [false, false, false, false, false]
#eval walk5 5 0 0                   -- expected: true

-- The kernel predicate of C₅ on a few sample subsets (all false).
#eval kernel5 (fun _ => false)      -- expected: false (empty set is not absorbing)
#eval kernel5 (fun _ => true)       -- expected: false (full set is not independent)
#eval kernel5 (fun i => decide (i = 0))  -- expected: false
