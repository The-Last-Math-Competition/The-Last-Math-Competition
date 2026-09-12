import Mathlib

/-!
# Conjecture 00000000034

Every finite colouring of `ℕ` contains a monochromatic geometric progression
`x, x r, x r ^ 2` with integer ratio `r > 1`.

The proof is the standard reduction to van der Waerden's theorem: colour the
exponents by `n ↦ c (2 ^ n)`, extract a monochromatic three-term arithmetic
progression `a, a + d, a + 2d` with `d > 0`, and read it back through powers of
two as `2 ^ a, 2 ^ a · 2 ^ d, 2 ^ a · (2 ^ d) ^ 2`.

Van der Waerden is not assumed here: `vanDerWaerden3` derives it from Mathlib's
`Combinatorics.exists_mono_homothetic_copy`, itself a corollary of the
Hales–Jewett theorem. The main results `exists_mono_geometric_progression` and
`exists_mono_geometric_progression_fin` are therefore unconditional.
-/

namespace GeometricProgression34

/-- Van der Waerden's theorem for three-term arithmetic progressions, obtained
from Mathlib's monochromatic homothetic copy theorem applied to `{0, 1, 2}`. -/
theorem vanDerWaerden3 {κ : Type*} [Finite κ] (color : ℕ → κ) :
    ∃ a d : ℕ, 0 < d ∧ color a = color (a + d) ∧ color (a + d) = color (a + 2 * d) := by
  obtain ⟨d, hd, b, k, hk⟩ :=
    Combinatorics.exists_mono_homothetic_copy ({0, 1, 2} : Finset ℕ) color
  have h0 := hk 0 (by decide)
  have h1 := hk 1 (by decide)
  have h2 := hk 2 (by decide)
  simp only [smul_eq_mul, Nat.mul_zero, Nat.mul_one, Nat.zero_add] at h0 h1 h2
  refine ⟨b, d, hd, ?_, ?_⟩
  · rw [h0, Nat.add_comm b d, h1]
  · rw [Nat.add_comm b d, h1, Nat.add_comm b (2 * d), Nat.mul_comm 2 d, h2]

/-- The conjecture, for an arbitrary finite palette. -/
theorem exists_mono_geometric_progression {κ : Type*} [Finite κ] (c : ℕ → κ) :
    ∃ x r : ℕ, 0 < x ∧ 1 < r ∧ c x = c (x * r) ∧ c (x * r) = c (x * r ^ 2) := by
  obtain ⟨a, d, hd, h₁, h₂⟩ := vanDerWaerden3 (fun n => c (2 ^ n))
  refine ⟨2 ^ a, 2 ^ d, Nat.two_pow_pos a,
    Nat.one_lt_pow (by omega) (by norm_num), ?_, ?_⟩
  · rw [← pow_add]; exact h₁
  · rw [← pow_add, ← pow_mul, ← pow_add, Nat.mul_comm d 2]; exact h₂

/-- A finite colouring of `ℕ` with `q` colours, as in the conjecture. -/
def Coloring (q : ℕ) := ℕ → Fin q

/-- The conjecture as literally stated: for any colouring by `q` colours there
are a positive `x` and an integer ratio `r > 1` with `x`, `x r` and `x r ^ 2`
all of the same colour. -/
theorem exists_mono_geometric_progression_fin {q : ℕ} (c : Coloring q) :
    ∃ x r : ℕ, 0 < x ∧ 1 < r ∧ c x = c (x * r) ∧ c (x * r) = c (x * r ^ 2) :=
  exists_mono_geometric_progression c

end GeometricProgression34
