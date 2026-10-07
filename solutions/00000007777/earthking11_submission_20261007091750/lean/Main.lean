import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace TLMC7777

abbrev K := AlgebraicClosure ℚ

def g (x : ℚ) : ℚ := x ^ 2 + 6 * x

theorem g_zero : g 0 = 0 := by norm_num [g]
theorem g_neg_three : g (-3) = -9 := by norm_num [g]
theorem g_neg_nine : g (-9) = 27 := by norm_num [g]

theorem g_gt_self {x : ℚ} (hx : 27 ≤ x) : x < g x := by
  unfold g
  nlinarith [sq_nonneg (x - 1)]

theorem tail_lower (n : ℕ) : 27 ≤ (g^[n]) 27 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_of_lt (g_gt_self ih))

theorem tail_strict : StrictMono (fun n : ℕ => (g^[n]) 27) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Function.iterate_succ_apply']
  exact g_gt_self (tail_lower n)

theorem orbit_tail (n : ℕ) : (g^[n+2]) (-3) = (g^[n]) 27 := by
  rw [Function.iterate_add_apply]
  norm_num [g, Function.iterate_succ_apply, Function.iterate_zero]

theorem orbit_ne_repeat : ¬ ∃ m n : ℕ, m < n ∧ (g^[m]) (-3) = (g^[n]) (-3) := by
  rintro ⟨m, n, hmn, heq⟩
  have hbig (k : ℕ) (hk : 2 ≤ k) : 27 ≤ (g^[k]) (-3) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    simpa [Nat.add_comm, Function.iterate_add_apply, g_neg_three, g_neg_nine]
      using tail_lower j
  rcases m with _ | m
  · rcases n with _ | n
    · exact (Nat.lt_irrefl _ hmn)
    · rcases n with _ | n
      · norm_num [g, Function.iterate_succ_apply] at heq
      · have : (g^[0]) (-3) < (g^[n+2]) (-3) := by
          simpa using (lt_of_lt_of_le (show (-3 : ℚ) < 27 by norm_num) (hbig (n+2) (by omega)))
        exact (ne_of_lt this) (by simpa [Nat.add_assoc] using heq)
  · rcases m with _ | m
    · rcases n with _ | n
      · omega
      · rcases n with _ | n
        · omega
        · have : (g^[1]) (-3) < (g^[n+2]) (-3) := by
            simpa [g_neg_three, Function.iterate_succ_apply] using
              (lt_of_lt_of_le (show (-9 : ℚ) < 27 by norm_num)
                (hbig (n+2) (by omega)))
          exact (ne_of_lt this) (by simpa [Nat.add_assoc] using heq)
    · have hn : 2 ≤ n := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hlt : m < j := by omega
      have : (g^[m+2]) (-3) < (g^[j+2]) (-3) := by
        rw [orbit_tail, orbit_tail]
        exact tail_strict hlt
      exact (ne_of_lt this) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)

noncomputable def P : Polynomial K := Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X

theorem degree_P : P.degree = 2 := by
  have hlt : (Polynomial.C (6 : K) * Polynomial.X).degree <
      ((Polynomial.X : Polynomial K) ^ 2).degree := by
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  unfold P
  rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  norm_num

theorem eval_P_cast (x : ℚ) : P.eval (x : K) = (g x : K) := by
  simp [P, g]

theorem P_zero : P.eval 0 = 0 := by
  simpa [g_zero] using eval_P_cast 0

theorem orbit_cast (n : ℕ) (x : ℚ) :
    ((P.eval)^[n]) (x : K) = ((g^[n]) x : K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact eval_P_cast _

theorem critical_neg_three : P.derivative.eval (-3 : K) = 0 := by
  simp [P, pow_two, Polynomial.derivative_mul]
  ring

def Preperiodic (p : Polynomial K) (x : K) : Prop :=
  ∃ m n : ℕ, m < n ∧ (p.eval^[m]) x = (p.eval^[n]) x

def PCF (p : Polynomial K) : Prop :=
  ∀ x : K, p.derivative.eval x = 0 → Preperiodic p x

theorem not_PCF : ¬ PCF P := by
  intro h
  obtain ⟨m, n, hmn, heq⟩ := h (-3) critical_neg_three
  have heqK : (((g^[m]) (-3) : ℚ) : K) = (((g^[n]) (-3) : ℚ) : K) := by
    rw [← orbit_cast, ← orbit_cast]
    simpa using heq
  have heqQ : (g^[m]) (-3) = (g^[n]) (-3) := Rat.cast_injective heqK
  exact orbit_ne_repeat ⟨m, n, hmn, heqQ⟩

noncomputable def naiveHeight (x : ℚ) : ℝ :=
  Real.log (max x.num.natAbs x.den : ℕ)

noncomputable def canonicalHeight (x : ℚ) : ℝ :=
  Filter.limUnder Filter.atTop
    (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)) * naiveHeight ((g^[n]) x))

theorem canonicalHeight_zero : canonicalHeight 0 = 0 := by
  have hs (n : ℕ) : (g^[n]) 0 = 0 := Function.iterate_fixed g_zero n
  have ht : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  simpa [canonicalHeight, naiveHeight, hs] using ht.limUnder_eq

theorem no_positive_bound_at_period_one :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℚ, g x = x → 2 * c ≤ canonicalHeight x := by
  rintro ⟨c, hc, h⟩
  have h0 := h 0 g_zero
  rw [canonicalHeight_zero] at h0
  linarith

theorem counterexample :
    P.degree = 2 ∧ ¬ PCF P ∧ P.eval 0 = 0 ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℚ, g x = x → 2 * c ≤ canonicalHeight x :=
  ⟨degree_P, not_PCF, P_zero, no_positive_bound_at_period_one⟩

#print axioms counterexample

end TLMC7777
