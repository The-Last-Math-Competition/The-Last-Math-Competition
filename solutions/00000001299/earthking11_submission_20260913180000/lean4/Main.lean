import Std

/-!
# Refutation of conjecture 00000001299 (Ducci cycles)

The conjecture states that for `n` a power of two the Ducci sequence reaches
zero, that for non-powers of two nontrivial cycles exist, **and that the minimal
cycle length is an odd factor of `n`**.

This file formalises a counterexample to the last clause, in core Lean 4
(`import Std` only), with no Mathlib, no `sorry`, no `axiom`, and no
`native_decide` / `Lean.ofReduceBool`.

## The model

The Ducci map on `n`-tuples is `T(x)_i = |x_i - x_{i+1}|` with cyclic indexing.
For `n = 5` we work with `Fin 5 → Nat` and encode the absolute difference
`|a - b|` as the purely natural expression `(a - b) + (b - a)` (truncated
subtraction), which is kernel-reducible.

The seed `s = (0,0,0,1,1)` lies on a cycle of length `15`: fifteen applications
of `T` return to `s`, and no positive iterate below `15` does.  The value `15`
is odd but `15 ∤ 5`, so the minimal cycle length is not an odd factor of `n`.

## Note on decidability

Core Lean (`import Std`) does not provide a `DecidableEq` instance for function
types, and in particular not for `Fin 5 → Nat`.  Equality of two states is
therefore phrased *pointwise* (`∀ i : Fin 5, x i = y i`), which is decidable
because `Fin 5` is finite and `Nat` has decidable equality.  The function-level
statement `iter 15 = s` is then obtained from the pointwise one by `funext`.
-/

set_option maxRecDepth 100000

namespace Tlmc1299

/-- The Ducci map on `Fin 5 → Nat`, i.e. `|x_i - x_{i+1}|` with cyclic
indexing.  For naturals `(a - b) + (b - a) = |a - b|`, since one of the two
truncated subtractions vanishes. -/
def T (x : Fin 5 → Nat) : Fin 5 → Nat :=
  fun i => (x i - x (i + 1)) + (x (i + 1) - x i)

/-- The seed `(0,0,0,1,1)`. -/
def s : Fin 5 → Nat :=
  fun i => match i.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 1
    | _ => 1

/-- The `k`-fold iterate of `T` starting from the seed `s`. -/
def iter : Nat → Fin 5 → Nat
  | 0 => s
  | k + 1 => T (iter k)

/-- Fifteen iterations of the Ducci map return the seed to itself.  Proved
pointwise over the five coordinates, then packaged with `funext`. -/
theorem returns_at_15 : iter 15 = s := by
  funext i
  revert i
  decide

/-- No positive iterate strictly below `15` returns the seed, expressed
pointwise so that it is a finite decidable check. -/
theorem no_return_below_15 :
    ∀ k : Fin 15, k.val ≠ 0 → ¬ (∀ i : Fin 5, iter k.val i = s i) := by
  decide

/-- Every positive `k < 15` yields a state different from the seed. -/
theorem distinct_first_15 : ∀ k, 1 ≤ k → k < 15 → iter k ≠ s := by
  intro k hk1 hk15 h
  exact no_return_below_15 ⟨k, hk15⟩ (Nat.pos_iff_ne_zero.mp hk1)
    (fun i => congrFun h i)

/-- `15` does not divide `5`. -/
theorem fifteen_not_divides_five : ¬ (15 ∣ 5) := by
  intro h
  have hle : 15 ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  exact absurd hle (by decide)

/-- `15` is the minimal non-trivial period of the seed `(0,0,0,1,1)` for
`n = 5`: it returns at `15`, and no positive smaller iterate does. -/
theorem min_period_five :
    (∃ k, 1 ≤ k ∧ iter k = s) ∧
      ¬ (∃ k, 1 ≤ k ∧ k < 15 ∧ iter k = s) := by
  refine ⟨⟨15, by decide, returns_at_15⟩, ?_⟩
  rintro ⟨k, hk1, hk15, hks⟩
  exact distinct_first_15 k hk1 hk15 hks

/-- **Refutation of conjecture 00000001299.**

For `n = 5` the seed `(0,0,0,1,1)` lies on a cycle of minimal non-trivial
length `15`.  The number `15` is odd, but `15 ∤ 5`.  Therefore the minimal
cycle length is not an odd factor of `n`, and the conjecture (in the exact
wording of the conjecture file) is false.

The first clause of the conjecture — nontrivial cycles exist for non-powers of
two — is not in dispute; only the "odd factor of `n`" clause is refuted. -/
theorem conjecture_00000001299_false :
    iter 15 = s ∧
      (∃ k, 1 ≤ k ∧ iter k = s) ∧
      ¬ (∃ k, 1 ≤ k ∧ k < 15 ∧ iter k = s) ∧
      ¬ (15 ∣ 5) :=
  ⟨returns_at_15, min_period_five.1, min_period_five.2, fifteen_not_divides_five⟩

end Tlmc1299
