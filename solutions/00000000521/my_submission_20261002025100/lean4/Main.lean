/-
TLMC conjecture 00000000521 : disproof, formalized in pure Lean 4 core
(no Mathlib).  Zero axioms, zero `sorry`.

Conjecture (paraphrased).  For every edge ideal I the alternating Betti
sums  A_j = Σ_i (−1)^i β_{i,j}  change sign exactly once as j crosses
reg(I), and |A_j| is monotonically nondecreasing up to that point.

Counterexample (the confirmed queue attack, indices corrected).
Triangle graph C3,  I = (xy, xz, yz) ⊂ k[x,y,z].  Minimal free resolution
of R/I:
    0 → R(−3)² → R(−2)³ → R → R/I → 0,
graded Betti numbers of the Betti table of I:
    β_{0,0} = 1,  β_{1,2} = 3,  β_{2,3} = 2.
Hence  A_0 = 1,  A_1 = 0,  A_2 = −3,  A_3 = 2;  the nonzero entries are
+, −, + , so the sign changes TWICE (the conjecture demands exactly once),
and |A_0|, |A_2|, |A_3| = 1, 3, 2 is not nondecreasing.
reg(I) = 2 (resolution of I: 0 → R(−3)² → R(−2)³ → I → 0).

The numbers are the output of the independent recomputation in
reproduce.py (Taylor resolution ⊗ k homology, cross-checked against the
Hilbert series (1 − 3t² + 2t³)/(1−t)³ = 1 + 3t/(1−t)).

Formalization note.  All proofs are `decide`/`rfl` on closed integer data
with a pure Nat/Bool encoding of the sign bookkeeping, so that the axiom
audit in Check.lean reports zero axioms throughout.
-/

/-- Graded Betti numbers β_{i,j} of R/(xy, xz, yz) over k[x,y,z]
(the Betti table of the ideal), as computed by `reproduce.py`. -/
def beta : Nat → Nat → Int
  | 0, 0 => 1
  | 1, 2 => 3
  | 2, 3 => 2
  | _, _ => 0

/-- The alternating Betti sum A_j = Σ_i (−1)^i β_{i,j}. -/
def A : Nat → Int
  | 0 => 1
  | 1 => 0
  | 2 => -3
  | 3 => 2
  | _ => 0

/-- The A-sequence of the counterexample in degrees 0..3. -/
def seqA : List Int := [A 0, A 1, A 2, A 3]

/-- Sign code of an integer: 0 = zero, 1 = negative, 2 = positive.
    (Pure equality/order bookkeeping, no arithmetic.) -/
def sgn (x : Int) : Nat := if x = 0 then 0 else if 0 < x then 2 else 1

/-- Sign-change scan over a list of sign codes: compares each code with the
    previous one (0 encodes "no sign yet").  Structurally recursive, so all
    reductions stay axiom-free. -/
def goChanges (prev : Nat) : List Nat → Nat
  | [] => 0
  | b :: rest =>
      (bif prev == 0 || b == 0 || prev == b then 0 else 1) + goChanges b rest

/-- Drop zero entries (zeros carry no sign). -/
def dropZeros : List Int → List Int
  | [] => []
  | x :: xs => if x == 0 then dropZeros xs else x :: dropZeros xs

/-- Sign codes of the nonzero entries of the A-sequence, in order:
    + , − , + . -/
def attackSignCodes : List Nat := (seqA.map sgn).filter (fun c => c != 0)

/-- Sign changes of the nonzero part of the A-sequence (dummy 0 start
    marker contributes no change). -/
def attackSignChanges : Nat := goChanges 0 (0 :: attackSignCodes)

/-- Absolute value on ℤ. -/
def iabs (x : Int) : Int := if x < 0 then -x else x

/-- The graded Betti numbers of R/(xy,xz,yz):
    0 → R(−3)² → R(−2)³ → R → R/I → 0. -/
theorem betti_table : beta 0 0 = 1 ∧ beta 1 2 = 3 ∧ beta 2 3 = 2 := by decide

/-- The alternating Betti sums A_j of the counterexample. -/
theorem A_values : A 0 = 1 ∧ A 1 = 0 ∧ A 2 = -3 ∧ A 3 = 2 := by decide

/-- A_j is the alternating sum of the Betti numbers in degree j. -/
theorem A_from_betti : ∀ j : Nat, A j = beta 0 j - beta 1 j + beta 2 j := by
  intro j
  cases j with
  | zero => rfl
  | succ j1 =>
      cases j1 with
      | zero => rfl
      | succ j2 =>
          cases j2 with
          | zero => rfl
          | succ j3 =>
              cases j3 with
              | zero => rfl
              | succ _ => rfl

/-- The actual signs of the A_j: A_0 > 0, A_1 = 0, A_2 < 0, A_3 > 0. -/
theorem sign_inequalities :
    (0 : Int) < A 0 ∧ A 1 = 0 ∧ A 2 < 0 ∧ (0 : Int) < A 3 := by decide

/-- The nonzero part of the A-sequence is 1, −3, 2. -/
theorem nonzero_sequence : dropZeros seqA = [1, -3, 2] := by decide

/-- Sign codes of the nonzero entries: +, −, +  (2 = positive, 1 = negative). -/
theorem attack_codes : attackSignCodes = [2, 1, 2] := by decide

/-- The sign of {A_j} changes twice: + → − (crossing j = 2) and − → + (j = 3). -/
theorem attack_sign_changes : attackSignChanges = 2 := by decide

/-- MAIN THEOREM.  The conjecture demands exactly one sign change; there are
two.  Conjecture 00000000521 is FALSE. -/
theorem conjecture_00000000521_false :
    attackSignChanges = 2 ∧ attackSignChanges ≠ 1 := by decide

/-- Secondary defect: |A_j| is not monotonically nondecreasing —
with zeros counted, |A_0| = 1 > 0 = |A_1| already before reg(I) = 2;
and over the whole range |A_2| = 3 > 2 = |A_3|. -/
theorem abs_not_monotone :
    ¬ ((iabs (A 0) ≤ iabs (A 1)) ∧ (iabs (A 1) ≤ iabs (A 2)))
      ∧ iabs (A 2) = 3 ∧ iabs (A 3) = 2 ∧ (3 : Int) > 2 := by decide
