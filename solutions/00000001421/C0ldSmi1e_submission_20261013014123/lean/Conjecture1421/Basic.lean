import Mathlib.Data.Matrix.DoublyStochastic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The exactly-half-lazy uniform Cayley walk used throughout the counterexample. -/
noncomputable section
open scoped BigOperators
namespace Conjecture1421

instance second_neZero (n : ℕ) : NeZero (n + 4) := ⟨by omega⟩

abbrev Second (n : ℕ) := ZMod (n + 4)
abbrev State (n : ℕ) := ZMod 2 × Second n

def size (n : ℕ) : ℝ := (n + 4 : ℕ)
def q (n : ℕ) : ℝ := 1 - 1 / size n
def r : ℝ := 1 / 2
def s (n : ℕ) : ℝ := 1 / 2 - 1 / size n

def support (n : ℕ) : Finset (State n) :=
  Finset.univ.filter fun g => (g.1 = 0 ∧ g.2 ≠ 0) ∨ (g.1 = 1 ∧ g.2 = 0)

def jumpLaw (n : ℕ) (g : State n) : ℝ :=
  if g.1 = 0 then (if g.2 = 0 then 1 / 2 else 1 / (2 * size n))
  else if g.2 = 0 then 1 / (2 * size n) else 0

def transition (n : ℕ) : Matrix (State n) (State n) ℝ :=
  fun x y => jumpLaw n (y - x)

def tvFrom (n t : ℕ) (x : State n) : ℝ :=
  (1 / 2) * ∑ y, |(transition n ^ t) x y - 1 / (2 * size n)|

def worstTV (n t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (tvFrom n t)

lemma size_ge_four (n : ℕ) : 4 ≤ size n := by
  simp only [size, Nat.cast_add, Nat.cast_ofNat]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma size_pos (n : ℕ) : 0 < size n := lt_of_lt_of_le (by norm_num) (size_ge_four n)
lemma size_ne_zero (n : ℕ) : size n ≠ 0 := ne_of_gt (size_pos n)

lemma transition_apply (n : ℕ) (x y : State n) :
    transition n x y =
      if x.1 = y.1 then (if x.2 = y.2 then 1 / 2 else 1 / (2 * size n))
      else if x.2 = y.2 then 1 / (2 * size n) else 0 := by
  simp only [transition, jumpLaw, Prod.fst_sub, Prod.snd_sub, sub_eq_zero]
  simp only [eq_comm]

lemma q_pos (n : ℕ) : 0 < q n := by
  have hn := size_ge_four n
  rw [q, sub_pos, div_lt_one (size_pos n)]
  linarith

lemma q_lt_one (n : ℕ) : q n < 1 := by
  have : 0 < 1 / size n := one_div_pos.mpr (size_pos n)
  dsimp [q]
  linarith

lemma s_nonneg (n : ℕ) : 0 ≤ s n := by
  have h : 1 / size n ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (size_pos n)).2
    have := size_ge_four n
    linarith
  exact sub_nonneg.mpr h

lemma q_eq_r_add_s (n : ℕ) : q n = r + s n := by unfold q r s; ring

lemma state_card (n : ℕ) : Fintype.card (State n) = 2 * (n + 4) := by
  simp

end Conjecture1421
