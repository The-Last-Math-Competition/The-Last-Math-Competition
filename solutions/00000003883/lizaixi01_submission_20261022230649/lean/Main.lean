import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Actual Frobenius powers of the homogeneous maximal ideal of F₂[x,y]. -/
namespace TLMC3883
open MvPolynomial Filter Topology

abbrev R := MvPolynomial (Fin 2) (ZMod 2)
noncomputable def maximalIdeal : Ideal R := idealOfVars (Fin 2) (ZMod 2)
noncomputable def frobeniusPower (e : ℕ) : Ideal R :=
  Ideal.map (iterateFrobenius R 2 e) maximalIdeal

theorem frobeniusPower_span (e : ℕ) :
    frobeniusPower e = Ideal.span
      ((fun d : Fin 2 →₀ ℕ => monomial d (1 : ZMod 2)) ''
        Set.range (fun i : Fin 2 => Finsupp.single i (2 ^ e))) := by
  unfold frobeniusPower maximalIdeal idealOfVars
  rw [Ideal.map_span]
  congr 1
  ext f
  simp [Set.mem_image, iterateFrobenius_def, X_pow_eq_monomial]

theorem mem_frobeniusPower (e : ℕ) (f : R) :
    f ∈ frobeniusPower e ↔
      ∀ d ∈ f.support, 2 ^ e ≤ d 0 ∨ 2 ^ e ≤ d 1 := by
  rw [frobeniusPower_span, mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff]
  simp [Fin.exists_fin_two]

theorem degree_two (d : Fin 2 →₀ ℕ) : Finsupp.degree d = d 0 + d 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem power_containment (e r : ℕ) :
    maximalIdeal ^ r ≤ frobeniusPower e ↔ 2 * (2 ^ e - 1) < r := by
  have hq : 0 < 2 ^ e := by positivity
  constructor
  · intro h
    by_contra hr
    let d : Fin 2 →₀ ℕ := Finsupp.single 0 (2 ^ e - 1) + Finsupp.single 1 (2 ^ e - 1)
    have hd : Finsupp.degree d = 2 * (2 ^ e - 1) := by
      simp [d, degree_two, two_mul]
    have hin : monomial d (1 : ZMod 2) ∈ maximalIdeal ^ r := by
      rw [maximalIdeal, monomial_mem_pow_idealOfVars_iff r d one_ne_zero, hd]
      omega
    have hout := (mem_frobeniusPower e _).mp (h hin)
    have hs : d ∈ (monomial d (1 : ZMod 2) : R).support := by simp
    have := hout d hs
    simp [d] at this
    omega
  · intro hr f hf
    apply (mem_frobeniusPower e f).mpr
    intro d hd
    have hdeg := (mem_pow_idealOfVars_iff r f).mp hf d hd
    rw [degree_two] at hdeg
    omega

theorem power_noncontainment (e r : ℕ) :
    ¬ maximalIdeal ^ r ≤ frobeniusPower e ↔ r ≤ 2 * (2 ^ e - 1) := by
  rw [power_containment]
  omega

/-- The largest exponent with noncontainment, defined from actual ideals. -/
noncomputable def nu (I : Ideal R) (e : ℕ) : ℕ :=
  sSup {r : ℕ | ¬ I ^ r ≤ frobeniusPower e}

theorem noncontainment_greatest (e : ℕ) :
    IsGreatest {r : ℕ | ¬ maximalIdeal ^ r ≤ frobeniusPower e}
      (2 * (2 ^ e - 1)) := by
  constructor
  · exact (power_noncontainment e _).mpr le_rfl
  · intro r hr
    exact (power_noncontainment e r).mp hr

theorem nu_formula (e : ℕ) : nu maximalIdeal e = 2 * (2 ^ e - 1) :=
  (noncontainment_greatest e).csSup_eq

noncomputable def normalizedNu (I : Ideal R) (e : ℕ) : ℝ :=
  nu I e / (2 : ℝ) ^ e

theorem normalizedNu_formula (e : ℕ) :
    normalizedNu maximalIdeal e = 2 - 2 * ((2 : ℝ) ^ e)⁻¹ := by
  have hq : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by decide)
  rw [normalizedNu, nu_formula, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_pow]
  push_cast
  field_simp

theorem threshold_limit :
    Tendsto (normalizedNu maximalIdeal) atTop (nhds 2) := by
  have hp : Tendsto (fun e : ℕ => (2 : ℝ) ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi := tendsto_inv_atTop_zero.comp hp
  have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
    (hi.const_mul 2)
  have hf : normalizedNu maximalIdeal = fun e => 2 - 2 * ((2 : ℝ) ^ e)⁻¹ :=
    funext normalizedNu_formula
  rw [hf]
  simpa using h

/-- Standard Frobenius-limit definition at the homogeneous maximal ideal.
Every use below is accompanied by a proved existence and value of the limit. -/
noncomputable def fPureThreshold (I : Ideal R) : ℝ :=
  limUnder atTop (normalizedNu I)

theorem maximalIdeal_fpt : fPureThreshold maximalIdeal = 2 :=
  threshold_limit.limUnder_eq

noncomputable def monomialIdeal (a b : ℕ) : Ideal R :=
  Ideal.span {X (0 : Fin 2) ^ a, X (1 : Fin 2) ^ b}

theorem monomialIdeal_one_one : monomialIdeal 1 1 = maximalIdeal := by
  unfold monomialIdeal maximalIdeal idealOfVars
  congr 1
  ext f
  simp [Fin.exists_fin_two, eq_comm]

theorem counterexample :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ ¬ 2 ∣ min a b ∧
      Tendsto (normalizedNu (monomialIdeal a b)) atTop
        (nhds (fPureThreshold (monomialIdeal a b))) ∧
      fPureThreshold (monomialIdeal a b) ≠ (min a b : ℕ) := by
  refine ⟨1, 1, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rw [monomialIdeal_one_one, maximalIdeal_fpt]
    exact threshold_limit
  · rw [monomialIdeal_one_one, maximalIdeal_fpt]
    norm_num

end TLMC3883
