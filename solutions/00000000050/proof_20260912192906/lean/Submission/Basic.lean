import Mathlib

/-!
# A proof of conjecture 00000000050

Conjecture 00000000050 asserts that every prime `p` is the permanent of some
square matrix with entries in `{0, 1}`. This is true, and more: **every**
natural number is such a permanent, by an explicit construction.

For `n : ℕ` let `W n` be the `(n+1) × (n+1)` matrix whose first row is all ones
and whose row `r ≠ 0` has ones exactly in column `0` and column `r`:

```
1 1 1 1 1
1 1 0 0 0
1 0 1 0 0
1 0 0 1 0
1 0 0 0 1
```

A permutation contributes to the permanent exactly when every nonzero index is
either fixed or sent to `0`, and those permutations are precisely the
transpositions `swap 0 k` for `k` ranging over all indices — `swap 0 0` being
the identity. There are `n+1` of them, so `permanent (W n) = n + 1`.

Primality plays no role: taking `n = p - 1` settles the conjecture.

Throughout, `permanent` is Mathlib's `Matrix.permanent`, not a local
redefinition.
-/

namespace Submission00000000050

open Finset Equiv Matrix

variable {n : ℕ}

/-- The witness matrix: first row all ones, row `r ≠ 0` with ones exactly in
columns `0` and `r`. -/
def W (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ :=
  Matrix.of fun r c => if r = 0 ∨ c = 0 ∨ c = r then 1 else 0

theorem W_apply (r c : Fin (n + 1)) :
    W n r c = if r = 0 ∨ c = 0 ∨ c = r then 1 else 0 := rfl

/-- `W n` has entries in `{0, 1}`. -/
theorem W_zero_or_one (r c : Fin (n + 1)) : W n r c = 0 ∨ W n r c = 1 := by
  rw [W_apply]; split <;> simp

/-- The permutations that contribute to the permanent. -/
def Contributes (σ : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∀ i : Fin (n + 1), i ≠ 0 → σ i = 0 ∨ σ i = i

instance (σ : Equiv.Perm (Fin (n + 1))) : Decidable (Contributes σ) := by
  unfold Contributes; infer_instance

theorem prod_W (σ : Equiv.Perm (Fin (n + 1))) :
    ∏ i, W n (σ i) i = if Contributes σ then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one (fun i _ => ?_)
    rw [W_apply]
    by_cases hi : i = 0
    · simp [hi]
    · rcases h i hi with h1 | h1
      · simp [h1]
      · simp [h1]
  · unfold Contributes at h
    push_neg at h
    obtain ⟨i, hi0, hi1, hi2⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [W_apply, if_neg]
    rintro (h | h | h)
    · exact hi1 h
    · exact hi0 h
    · exact hi2 h.symm

/-- Each `swap 0 k` contributes. -/
theorem contributes_swap (k : Fin (n + 1)) : Contributes (Equiv.swap 0 k) := by
  intro i hi
  by_cases hik : i = k
  · left; rw [hik, Equiv.swap_apply_right]
  · right; exact Equiv.swap_apply_of_ne_of_ne hi hik

/-- A contributing permutation is the transposition exchanging `0` with its
own image. -/
theorem eq_swap_of_contributes {σ : Equiv.Perm (Fin (n + 1))} (h : Contributes σ) :
    σ = Equiv.swap 0 (σ 0) := by
  ext i
  by_cases hi : i = 0
  · rw [hi, Equiv.swap_apply_left]
  · rcases h i hi with h1 | h1
    · have hk0 : σ 0 ≠ 0 := by
        intro hEq
        exact hi (σ.injective (h1.trans hEq.symm))
      have hσk : σ (σ 0) = 0 := by
        rcases h (σ 0) hk0 with h2 | h2
        · exact h2
        · exact absurd (σ.injective h2) hk0
      have : σ 0 = i := σ.injective (hσk.trans h1.symm)
      rw [h1, ← this, Equiv.swap_apply_right]
    · have hne : i ≠ σ 0 := by
        intro hEq
        exact hi (σ.injective (h1.trans hEq))
      rw [h1, Equiv.swap_apply_of_ne_of_ne hi hne]

theorem swap_injective :
    Function.Injective (fun k : Fin (n + 1) => Equiv.swap (0 : Fin (n + 1)) k) := by
  intro a b hab
  have := congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e 0) hab
  simpa [Equiv.swap_apply_left] using this

theorem filter_contributes :
    (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => Contributes σ))
      = univ.image (fun k : Fin (n + 1) => Equiv.swap 0 k) := by
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro h
    exact ⟨σ 0, (eq_swap_of_contributes h).symm⟩
  · rintro ⟨k, rfl⟩
    exact contributes_swap k

/-- The permanent of the witness matrix is its size. -/
theorem permanent_W (n : ℕ) : (W n).permanent = n + 1 := by
  rw [Matrix.permanent, Finset.sum_congr rfl (fun σ _ => prod_W σ), Finset.sum_boole,
    filter_contributes, Finset.card_image_of_injective _ swap_injective]
  simp

/-! ## The conjecture -/

/-- Conjecture 00000000050. -/
def ConjectureHolds : Prop :=
  ∀ p : ℕ, p.Prime → ∃ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℕ),
    (∀ i j, A i j = 0 ∨ A i j = 1) ∧ A.permanent = p

/-- Every natural number is the permanent of a `{0,1}` matrix. -/
theorem exists_zeroOne_permanent (m : ℕ) :
    ∃ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℕ),
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧ A.permanent = m := by
  cases m with
  | zero =>
      refine ⟨1, 0, fun i j => Or.inl rfl, ?_⟩
      simp
  | succ k => exact ⟨k + 1, W k, fun i j => W_zero_or_one i j, permanent_W k⟩

/-- Conjecture 00000000050 is true. -/
theorem conjecture_00000000050_true : ConjectureHolds := fun p _ =>
  exists_zeroOne_permanent p

end Submission00000000050
