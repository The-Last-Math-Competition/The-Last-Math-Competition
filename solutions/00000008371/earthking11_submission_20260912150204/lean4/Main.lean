/-
  Disproof of conjecture `00000008371`: formalisation of the arithmetic core.

  Conjecture (as filed): the count `space_tree` of Nielsen cells ("space trees")
  of the tropical Grassmannian Trop(Gr(2,n)) equals the type count

      F(n) = (n-2)! (n-3)! / 2,

  that its parity follows 2^{n-3}, that the adjacency graph of cells is the Johnson
  graph J(n,2), and that the spectrum is a difference set.

  We formalise the failures that refute the conjunction:

    (1)  F(3) = 1! * 0! / 2 = 1/2, which is not an integer; a count is a natural
         number, so no natural number cast to `Rat` can equal `F(3)`;
    (2)  F(n) never equals the Johnson vertex count C(n,2) = n(n-1)/2; we record
         the explicit instances n = 4, 5, 6, where F is 1, 6, 72 while C(n,2) is
         6, 10, 15.

  Any one of these refutes a conjunct, hence the whole conjecture.

  CORE LEAN ONLY (`import Std`): no Mathlib, no `Finset`, no `Nat.Prime`, and no
  Mathlib-only tactic (`norm_num`, `linarith`, `omega`, `positivity`). All closed
  numerical facts are proved by `decide`; the integrality argument clears
  denominators and uses `Rat.div_mul_cancel`, `Rat.natCast_mul`, `Rat.natCast_inj`.

  Note on `Nat.factorial`: this Lean toolchain (`v4.33.1`) does not ship
  `Nat.factorial` in `Std`, so the file defines it below, inside the `Nat`
  namespace, by structural recursion. This keeps `spaceTreeFormula` textually as
  specified while remaining core Lean only.
-/

import Std

namespace Nat

/-- Factorial, `factorial n = n!`, defined by structural recursion. The toolchain
used here does not provide `Nat.factorial`, so we supply it. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

end Nat

namespace Tlmc8371

/-- The number of "space trees" before division, `(n-2)! * (n-3)!`, as a natural
number. -/
def treeCount (n : Nat) : Nat :=
  Nat.factorial (n - 2) * Nat.factorial (n - 3)

/-- The conjectured count of "space trees":

    `spaceTreeFormula n = (n - 2)! * (n - 3)! / 2`.

    The subtractions are natural-number subtraction, so at `n = 3` this is
    `1! * 0! / 2 = 1/2`. The result type is `Rat` precisely so that this value is
    representable and its non-integrality can be stated. -/
def spaceTreeFormula (n : Nat) : Rat :=
  (treeCount n : Rat) / 2

/-- The number of vertices of the Johnson graph `J(n,2)`:

    `johnsonVertices n = C(n,2) = n * (n - 1) / 2`. -/
def johnsonVertices (n : Nat) : Nat :=
  n * (n - 1) / 2

/-! ### Arithmetic helpers -/

/-- `((a * 2) : Rat) / 2 = a`: cancellation of the denominator `2` against an even
numerator. -/
theorem natCast_mul_two_div_two (a : Nat) :
    ((a * 2 : Nat) : Rat) / 2 = (a : Rat) := by
  rw [Rat.natCast_mul, Rat.natCast_ofNat]
  exact Rat.mul_div_cancel (by decide : (2 : Rat) ≠ 0)

/-- No natural number satisfies `m * 2 = 1` (parity obstruction). -/
theorem mul_two_ne_one : ∀ m : Nat, m * 2 ≠ 1 := by
  intro m
  induction m with
  | zero => decide
  | succ k _ =>
      intro h
      have hle : 2 ≤ (k + 1) * 2 := by
        have h1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have h2 : 1 * 2 ≤ (k + 1) * 2 := Nat.mul_le_mul_right 2 h1
        simpa using h2
      rw [h] at hle
      exact absurd hle (by decide)

/-! ### Closed values of the conjectured formula -/

/-- `F(3) = 1! * 0! / 2 = 1/2`. -/
theorem formula_at_3 : spaceTreeFormula 3 = 1 / 2 := by
  unfold spaceTreeFormula treeCount
  rw [show Nat.factorial (3 - 2) * Nat.factorial (3 - 3) = 1 from by decide,
    Rat.natCast_ofNat]

/-- `F(4) = 2! * 1! / 2 = 1`. -/
theorem formula_at_4 : spaceTreeFormula 4 = 1 := by
  unfold spaceTreeFormula treeCount
  rw [show Nat.factorial (4 - 2) * Nat.factorial (4 - 3) = 2 from by decide]
  simpa using natCast_mul_two_div_two 1

/-- `F(5) = 3! * 2! / 2 = 6`. -/
theorem formula_at_5 : spaceTreeFormula 5 = 6 := by
  unfold spaceTreeFormula treeCount
  rw [show Nat.factorial (5 - 2) * Nat.factorial (5 - 3) = 12 from by decide]
  simpa using natCast_mul_two_div_two 6

/-- `F(6) = 4! * 3! / 2 = 72`. -/
theorem formula_at_6 : spaceTreeFormula 6 = 72 := by
  unfold spaceTreeFormula treeCount
  rw [show Nat.factorial (6 - 2) * Nat.factorial (6 - 3) = 144 from by decide]
  simpa using natCast_mul_two_div_two 72

/-! ### Johnson vertex counts `C(n,2)` -/

theorem johnson_3 : johnsonVertices 3 = 3 := by decide

theorem johnson_4 : johnsonVertices 4 = 6 := by decide

theorem johnson_5 : johnsonVertices 5 = 10 := by decide

theorem johnson_6 : johnsonVertices 6 = 15 := by decide

/-! ### Failure 1: the formula is not a count at `n = 3` -/

/-- `F(3) = 1/2` is not the cast of any natural number. A count of cells is a
natural number, so the conjectured identification `space_tree = F(3)` is
impossible. The proof clears denominators: from `(m : Rat) = 1/2` we get
`(2*m : Rat) = 1`, hence `2*m = 1` in `Nat`, which has no solution. -/
theorem no_count_is_half : ¬ ∃ m : Nat, (m : Rat) = spaceTreeFormula 3 := by
  rintro ⟨m, hm⟩
  rw [formula_at_3] at hm
  have hmul : (m : Rat) * 2 = (1 / 2 : Rat) * 2 :=
    congrArg (fun q : Rat => q * 2) hm
  have hleft : (m : Rat) * 2 = ((m * 2 : Nat) : Rat) := by
    rw [Rat.natCast_mul, Rat.natCast_ofNat]
  have hright : (1 / 2 : Rat) * 2 = 1 :=
    Rat.div_mul_cancel (by decide : (2 : Rat) ≠ 0)
  have hnat : ((m * 2 : Nat) : Rat) = 1 := by
    rw [← hleft, hmul, hright]
  have hnat' : ((m * 2 : Nat) : Rat) = ((1 : Nat) : Rat) := by
    rw [hnat, ← Rat.natCast_ofNat]
  exact mul_two_ne_one m (Rat.natCast_inj.mp hnat')

/-! ### Failure 2: the formula disagrees with the Johnson vertex count -/

/-- At `n = 4`: `F(4) = 1` while `C(4,2) = 6`. -/
theorem formula_ne_johnson_4 : spaceTreeFormula 4 ≠ (johnsonVertices 4 : Rat) := by
  rw [formula_at_4, johnson_4]
  intro h
  exact absurd (Rat.natCast_inj.mp h) (by decide)

/-- At `n = 5`: `F(5) = 6` while `C(5,2) = 10`. -/
theorem formula_ne_johnson_5 : spaceTreeFormula 5 ≠ (johnsonVertices 5 : Rat) := by
  rw [formula_at_5, johnson_5]
  intro h
  exact absurd (Rat.natCast_inj.mp h) (by decide)

/-- At `n = 6`: `F(6) = 72` while `C(6,2) = 15`. -/
theorem formula_ne_johnson_6 : spaceTreeFormula 6 ≠ (johnsonVertices 6 : Rat) := by
  rw [formula_at_6, johnson_6]
  intro h
  exact absurd (Rat.natCast_inj.mp h) (by decide)

/-! ### The disproof -/

/-- The conjecture is false as stated:

* `¬ ∃ m : Nat, (m : Rat) = spaceTreeFormula 3`
  (Failure 1: `F(3) = 1/2` is not a count);
* `spaceTreeFormula 4 ≠ (johnsonVertices 4 : Rat)` (Failure 2: `1 ≠ 6`);
* `spaceTreeFormula 5 ≠ (johnsonVertices 5 : Rat)` (Failure 2: `6 ≠ 10`);
* `spaceTreeFormula 6 ≠ (johnsonVertices 6 : Rat)` (Failure 2: `72 ≠ 15`).

Each conjunct is a necessary part of the conjecture; the first already refutes it,
and the remaining three show the count formula and the asserted Johnson adjacency
are mutually inconsistent. -/
theorem conjecture_00000008371_false :
    (¬ ∃ m : Nat, (m : Rat) = spaceTreeFormula 3) ∧
      spaceTreeFormula 4 ≠ (johnsonVertices 4 : Rat) ∧
      spaceTreeFormula 5 ≠ (johnsonVertices 5 : Rat) ∧
      spaceTreeFormula 6 ≠ (johnsonVertices 6 : Rat) :=
  ⟨no_count_is_half, formula_ne_johnson_4, formula_ne_johnson_5,
    formula_ne_johnson_6⟩

end Tlmc8371
