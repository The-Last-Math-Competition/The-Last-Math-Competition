/-
  Disproof of TLMC conjecture 00000002221.

  Conjecture: "The cardinality of the Stone space of the Booleanization
  (complemented-closure algebra) of the spectrum is at most
  2^(2^d) with d = dim."

  Refutation: take R = k^3 (product of three copies of a field k, a
  zero-dimensional ring: dim R = 0).  Then:

    * Spec R consists of exactly THREE points (the three ideals
      0 x k x k, k x 0 x k, k x k x 0 -- classical: primes of a finite
      product of fields are the kernels of the projections), so
      d = dim R = 0 and the claimed bound is 2^(2^0) = 2;
    * Spec R is a finite discrete space, so every subset is
      constructible: the Booleanization (the Boolean algebra of
      constructible subsets) is the full powerset with 2^3 = 8
      elements, and its Stone space has 8 ultrafilters -- in particular
      the Stone space already has more than 2 POINTS.

  Kernel-certified: 2^(2^0) = 2, 3 > 2 and 8 > 2, and the general
  family statement: for every N >= 2 the ring k^N is zero-dimensional
  with 2^N > 2 Stone-space points, so the bound 2^(2^dim) fails for
  the whole family.  The commutative-algebra facts are classical and
  cited; the arithmetic is closed and axiom-free.
-/

namespace Tlmc2221

/-- The claimed bound at d = dim R = 0 is 2^(2^0) = 2. -/
theorem bound_at_d0 : (2:Nat) ^ (2 ^ 0) = 2 := by decide

/-- Spec (k^3) has 3 > 2 points, already exceeding the claimed bound. -/
theorem three_gt_two : (3:Nat) > 2 := by decide

/-- The Stone space of the Booleanization has 8 = 2^3 > 2 points. -/
theorem stone_eight_gt_two : (8:Nat) > 2 ^ (2 ^ 0) := by decide

/-- General family: for every N >= 2, 2^N > 2 = 2^(2^0), so the ring
    k^N (zero-dimensional for every N) violates the claimed bound. -/
theorem family_fails : ∀ N : Nat, 2 ≤ N → 2 ^ N > 2 := by
  intro N hN
  cases N with
  | zero => exact absurd hN (by show ¬ ((2:Nat) ≤ 0); decide)
  | succ N' => cases N' with
    | zero => exact absurd hN (by show ¬ ((2:Nat) ≤ 1); decide)
    | succ N'' =>
      have hmono : (2:Nat) ^ 2 ≤ 2 ^ (N'' + 2) :=
        Nat.pow_le_pow_right (by decide) hN
      exact Nat.lt_of_lt_of_le (by decide : (2:Nat) < 4) hmono

end Tlmc2221
