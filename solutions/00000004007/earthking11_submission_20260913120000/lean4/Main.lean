/-
  Refutation of conjecture 00000004007 (optimal subadditivity of p-variation).

  Statement under test.  With
      ‖X‖_p = ( sup over partitions of Σ |X(t_i) - X(t_{i-1})|^p )^{1/p}
  the p-th root of the supremum, and q the conjugate exponent of p
  (1/p + 1/q = 1, q = p/(p-1)), the conjecture claims
      ‖X + Y‖ ≤ ( ‖X‖^q + ‖Y‖^q )^{1/q}
  and that this inequality "cannot be enlarged".

  The claim is FALSE, and the failure is elementary.  Because ‖·‖ is the
  p-th root of a supremum it is homogeneous of degree 1:
      ‖a X‖ = |a| ‖X‖ .
  Take any non-zero path X and put Y = X.  Then
      LHS = ‖X + Y‖ = ‖2X‖ = 2 ‖X‖ ,
      RHS = ( ‖X‖^q + ‖X‖^q )^{1/q} = 2^{1/q} ‖X‖ ,
  and since q = p/(p-1) > 1 for every finite p > 1 we have 2 > 2^{1/q}.
  Hence the inequality fails; it "cannot be enlarged" only in the trivial
  sense that it is not even valid.

  Equivalently, at X = Y ≠ 0 the claimed inequality would require
      2 ≤ 2^{1/q}  ⟺  2^q ≤ 2 ,
  which is false for every q > 1.  This file formalises exactly that
  arithmetic core, in core Lean 4 (`import Std`, no Mathlib, no `sorry`,
  no `axiom`, no `native_decide`; core Lean has no ℝ and `decide` cannot
  reduce `Rat` operations, so everything is kept in `Nat`).

  For a two-point unit-step path (‖X‖ = 1) the numbers are:
      p = 3/2 → q = 3,     LHS = 2, RHS = 2^{1/3}  ≈ 1.2599
      p = 2   → q = 2,     LHS = 2, RHS = 2^{1/2}  ≈ 1.4142
      p = 3   → q = 3/2,   LHS = 2, RHS = 2^{2/3}  ≈ 1.5874
      p = 4   → q = 4/3,   LHS = 2, RHS = 2^{3/4}  ≈ 1.6818
      p = 10  → q = 10/9,  LHS = 2, RHS = 2^{9/10} ≈ 1.8661 .
  See `../reproduce.py` and `../main.tex`.  `lean4/README.md` records the
  precise scope of what is and is not formalised here.
-/
import Std

namespace Tlmc4007

/-- Instance for `p = 2`, i.e. `q = 2`: the requirement `2^q ≤ 2` is `4 ≤ 2`,
which is false. -/
theorem q_eq_two_fails : ¬ ((2 : Nat) ^ 2 ≤ 2) := by decide

/-- The value of `2^2`, recorded so that the failure `¬ (4 ≤ 2)` is transparent. -/
theorem q_eq_two : (2 : Nat) ^ 2 = 4 := by decide

/-- Instance for `p = 3`, i.e. `q = 3/2`.  The requirement `2^q ≤ 2` is
`2^{3/2} ≤ 2`, equivalently `2^3 ≤ 2^2`, i.e. `8 ≤ 4`, which is false. -/
theorem q_eq_three_halves_fails : ¬ ((2 : Nat) ^ 3 ≤ (2 : Nat) ^ 2) := by decide

/-- General arithmetic fact: for every `q > 1`, `2 < 2^q`, hence `2^q ≤ 2` is
false.  Proved by induction, core Lean only. -/
theorem pow_two_gt_two : ∀ q : Nat, 1 < q → 2 < 2 ^ q := by
  intro q
  induction q with
  | zero => omega
  | succ q ih =>
    intro hq
    rw [Nat.pow_succ]
    by_cases hq0 : q = 0
    · subst hq0
      exact absurd hq (by decide)
    · by_cases hq1 : q = 1
      · subst hq1
        decide
      · have h2 : 2 < 2 ^ q := ih (by omega)
        omega

/-- Conjecture 00000004007 is false.

The homogeneity `‖aX‖ = |a| ‖X‖` of the p-variation (it is the p-th root of a
supremum, hence homogeneous of degree 1) reduces the conjectured inequality
at `X = Y ≠ 0` to
    `2 ‖X‖ ≤ 2^{1/q} ‖X‖`,  i.e.  `2 ≤ 2^{1/q}`,  i.e.  `2^q ≤ 2`,
which is exactly the false inequality collected below: the two explicit
instances (`q = 2`, `q = 3/2`) and the general fact `2 < 2^q` for all `q > 1`.
There is no real-valued p-variation formalised here; only this arithmetic
core is, since it is the entire content of the obstruction. -/
theorem conjecture_00000004007_false :
    (¬ ((2 : Nat) ^ 2 ≤ 2)) ∧
    ((2 : Nat) ^ 2 = 4) ∧
    (¬ ((2 : Nat) ^ 3 ≤ (2 : Nat) ^ 2)) ∧
    (∀ q : Nat, 1 < q → 2 < 2 ^ q) :=
  ⟨q_eq_two_fails, q_eq_two, q_eq_three_halves_fails, pow_two_gt_two⟩

end Tlmc4007
