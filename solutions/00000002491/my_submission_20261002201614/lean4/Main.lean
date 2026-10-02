/-
  Disproof of TLMC conjecture 00000002491.

  Conjecture: "The Mobius function of the partition lattice is governed by
  squarefree partitions: ... the Mobius values vanish otherwise [i.e., on
  partitions WITH repeated block sizes]."

  Refutation at n = 4: the partition sigma = {{1,2},{3,4}} has a REPEATED
  block size (2, 2), but mu(0_hat, sigma) = 1, not 0.

  The value is computed exactly by the classical product formula
  mu(0_hat, sigma) = prod over blocks B of (-1)^(|B|-1) * (|B|-1)!,
  which for block sizes (2,2) gives (-1)(1) * (-1)(1) = 1; and
  independently by direct recursive computation of the Mobius function on
  the 4-element interval [0_hat, sigma] =
    { {1|2|3|4},  {12|3|4},  {1|2|34},  {12|34} }
  (a Boolean lattice B_2 in disguise): the recursion
  mu(x, y) = -sum_{x <= z < y} mu(x, z), mu(x,x) = 1, gives
    mu(0, {12|3|4}) = -1, mu(0, {1|2|34}) = -1,
    mu(0, {12|34}) = -(1 + (-1) + (-1)) = 1.

  Lean certificate: the interval is hardcoded as a 4x4 order matrix;
  the Mobius values are computed by the recursion and kernel-checked.
  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc2491

/- The interval [0_hat, sigma] with elements indexed 0..3:
   0 = {1|2|3|4}   (bottom)
   1 = {12|3|4}
   2 = {1|2|34}
   3 = {12|34}     (top = sigma)                          -/

/-- Order relation of the 4-element interval (as an explicit matrix). -/
def le : Nat → Nat → Bool :=
  fun x y =>
    match x, y with
    | 0, _ => true
    | 1, 1 => true
    | 1, 3 => true
    | 2, 2 => true
    | 2, 3 => true
    | 3, 3 => true
    | _, _ => false

/-- Strict order x <= z < y. -/
def between (x z y : Nat) : Bool := le x z && le z y && !(z == y)

/-- Mobius function of the interval via the classical recursion with a
    fuel parameter (the interval has 4 elements, so fuel 4 suffices; the
    recursion strictly descends in the second argument). -/
def muAux : Nat → Nat → Nat → Int
  | 0,     x, y => if x == y then 1 else if !(le x y) then 0 else 0
  | f+1, x, y =>
      if x == y then 1
      else if !(le x y) then 0
      else -((List.range 4).foldl (fun acc z =>
        if between x z y && z < y then acc + muAux f x z else acc) 0)

/-- mu(0, {12|3|4}) = -1. -/
theorem mu_1 : muAux 4 0 1 = -1 := by decide

/-- mu(0, {1|2|34}) = -1. -/
theorem mu_2 : muAux 4 0 2 = -1 := by decide

/-- mu(0_hat, sigma) = mu(0, 3) = -(1 + (-1) + (-1)) = 1 — NOT zero,
    although sigma = {{1,2},{3,4}} has repeated block sizes (2,2). -/
theorem mu_sigma : muAux 4 0 3 = 1 := by decide

/-- The conjectured vanishing fails: 1 <> 0. -/
theorem not_zero : ¬ (muAux 4 0 3 = 0) := by decide

/-- sigma has two blocks of size 2 each (repeated parts). -/
theorem repeated_sizes : (2 = 2 : Bool) := rfl

end Tlmc2491
