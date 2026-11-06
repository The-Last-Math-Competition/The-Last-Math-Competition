import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace TLMC3890
open Polynomial
abbrev R := Polynomial (ZMod 2)

noncomputable def frobeniusPower (J : Ideal R) (e : ℕ) : Ideal R :=
  Ideal.map (iterateFrobenius R 2 (e + 1)) J

/-- The infimum of the ideals whose Frobenius power contains I.
We prove that for every ideal used below this infimum is itself the least such ideal. -/
noncomputable def frobeniusRoot (I : Ideal R) (e : ℕ) : Ideal R :=
  sInf {J | I ≤ frobeniusPower J e}

noncomputable def principalTestIdeal (f : R) (t : ℝ) : Ideal R :=
  ⨆ e : ℕ, frobeniusRoot (Ideal.span {f} ^ ⌈t * (2 : ℝ) ^ (e + 1)⌉₊) e

theorem frobeniusPower_principal (f : R) (e : ℕ) :
    frobeniusPower (Ideal.span {f}) e = Ideal.span {f ^ (2 ^ (e + 1))} := by
  simp [frobeniusPower, Ideal.map_span, iterateFrobenius_def]

theorem X_pow_dvd_X_pow (n m : ℕ) : (X ^ n : R) ∣ X ^ m ↔ n ≤ m := by
  constructor
  · intro h
    have hd := Polynomial.natDegree_le_of_dvd h (by simp)
    simpa using hd
  · exact pow_dvd_pow X

theorem X_ideal_nonzero_proper :
    (Ideal.span {(X : R)} : Ideal R) ≠ ⊥ ∧ Ideal.span {(X : R)} ≠ ⊤ := by
  constructor
  · simp
  · intro h
    have h1 : (1 : R) ∈ Ideal.span {(X : R)} := by rw [h]; trivial
    rw [Ideal.mem_span_singleton] at h1
    have hd : (X ^ 1 : R) ∣ X ^ 0 := by simpa using h1
    have := (X_pow_dvd_X_pow 1 0).mp hd
    omega

theorem frobeniusRoot_X_pow_least (e n : ℕ) :
    IsLeast {J : Ideal R | Ideal.span {(X : R) ^ n} ≤ frobeniusPower J e}
      (Ideal.span {X ^ (n / 2 ^ (e + 1))}) := by
  have hq : 0 < 2 ^ (e + 1) := by positivity
  constructor
  · change Ideal.span {(X : R) ^ n} ≤ _
    rw [frobeniusPower_principal, ← pow_mul]
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_X_pow]
    exact Nat.div_mul_le_self n _
  · intro J hJ
    change Ideal.span {(X : R) ^ n} ≤ frobeniusPower J e at hJ
    let g : R := Submodule.IsPrincipal.generator J
    have hgen : Ideal.span {g} = J := Ideal.span_singleton_generator J
    have hgq : g ^ (2 ^ (e + 1)) ∣ (X : R) ^ n := by
      rw [← hgen, frobeniusPower_principal, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton] at hJ
      exact hJ
    have hg : g ∣ (X : R) ^ n := (dvd_pow_self g (by omega : 2 ^ (e + 1) ≠ 0)).trans hgq
    obtain ⟨j, _, hassoc⟩ := (dvd_prime_pow (Polynomial.prime_X (R := ZMod 2)) n).mp hg
    have hjq : j * 2 ^ (e + 1) ≤ n := by
      apply (X_pow_dvd_X_pow _ _).mp
      rw [pow_mul]
      exact (hassoc.pow_pow).dvd_iff_dvd_left.mp hgq
    have hj : j ≤ n / 2 ^ (e + 1) := (Nat.le_div_iff_mul_le hq).mpr hjq
    rw [Ideal.span_singleton_le_iff_mem, ← hgen, Ideal.mem_span_singleton]
    exact hassoc.dvd.trans (pow_dvd_pow X hj)

theorem frobeniusRoot_X_pow (e n : ℕ) :
    frobeniusRoot (Ideal.span {(X : R) ^ n}) e = Ideal.span {X ^ (n / 2 ^ (e + 1))} :=
  (frobeniusRoot_X_pow_least e n).csInf_eq

theorem testIdeal_integer (k : ℕ) :
    principalTestIdeal (X : R) k = Ideal.span {X ^ k} := by
  unfold principalTestIdeal
  have h (e : ℕ) : frobeniusRoot (Ideal.span {(X : R)} ^ ⌈(k : ℝ) * 2 ^ (e + 1)⌉₊) e =
      Ideal.span {X ^ k} := by
    rw [show (k : ℝ) * 2 ^ (e + 1) = ((k * 2 ^ (e + 1) : ℕ) : ℝ) by push_cast; rfl]
    rw [Nat.ceil_natCast, Ideal.span_singleton_pow, frobeniusRoot_X_pow,
      Nat.mul_div_left _ (by positivity)]
  simp_rw [h]
  simp

theorem testIdeal_antitone : Antitone (principalTestIdeal (X : R)) := by
  intro s t hst
  unfold principalTestIdeal
  apply iSup_le
  intro e
  apply le_trans _ (le_iSup _ e)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    frobeniusRoot_X_pow, frobeniusRoot_X_pow,
    Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_X_pow]
  apply Nat.div_le_div_right
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_right hst (by positivity)

/-- The defining roots form an increasing chain, so the ideal supremum
below is the literal union in the standard test-ideal definition. -/
theorem testStages_monotone (t : ℝ) : Monotone (fun e : ℕ =>
    frobeniusRoot (Ideal.span {(X : R)} ^ ⌈t * (2 : ℝ) ^ (e + 1)⌉₊) e) := by
  apply monotone_nat_of_le_succ
  intro e
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    frobeniusRoot_X_pow, frobeniusRoot_X_pow,
    Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_X_pow]
  let q : ℕ := 2 ^ (e + 1)
  have hn : ⌈t * ((2 * q : ℕ) : ℝ)⌉₊ ≤ 2 * ⌈t * (q : ℝ)⌉₊ := by
    apply Nat.ceil_le.mpr
    push_cast
    have h := Nat.le_ceil (t * (q : ℝ))
    nlinarith
  have hd : ⌈t * ((2 * q : ℕ) : ℝ)⌉₊ / (2 * q) ≤
      (2 * ⌈t * (q : ℝ)⌉₊) / (2 * q) := Nat.div_le_div_right hn
  rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 2)] at hd
  convert hd using 1 <;>
    simp [q, Nat.cast_pow, pow_succ, Nat.add_assoc, mul_comm]

theorem mem_testIdeal_iff (t : ℝ) (f : R) :
    f ∈ principalTestIdeal X t ↔ ∃ e : ℕ,
      f ∈ frobeniusRoot (Ideal.span {(X : R)} ^ ⌈t * (2 : ℝ) ^ (e + 1)⌉₊) e := by
  exact Submodule.mem_iSup_of_directed _ (testStages_monotone t).directed_le

noncomputable def leftPoint (k e : ℕ) : ℝ :=
  ((k * 2 ^ (e + 1) + (2 ^ (e + 1) - 1) : ℕ) : ℝ) / (2 : ℝ) ^ (e + 1)

theorem leftPoint_formula (k e : ℕ) :
    leftPoint k e = (k + 1 : ℕ) - ((2 : ℝ) ^ (e + 1))⁻¹ := by
  have hq : 1 ≤ 2 ^ (e + 1) := Nat.one_le_pow (e + 1) 2 (by decide)
  simp only [leftPoint, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub hq, Nat.cast_one]
  field_simp
  ring

theorem leftPoint_witness (k e : ℕ) :
    (X ^ k : R) ∈ principalTestIdeal X (leftPoint k e) := by
  have hq : 0 < 2 ^ (e + 1) := by positivity
  apply (le_iSup (fun n : ℕ => frobeniusRoot
    (Ideal.span {(X : R)} ^ ⌈leftPoint k e * (2 : ℝ) ^ (n + 1)⌉₊) n) e)
  have hceil : ⌈leftPoint k e * (2 : ℝ) ^ (e + 1)⌉₊ =
      k * 2 ^ (e + 1) + (2 ^ (e + 1) - 1) := by
    rw [leftPoint, div_mul_cancel₀ _ (by positivity), Nat.ceil_natCast]
  rw [hceil, Ideal.span_singleton_pow, frobeniusRoot_X_pow]
  have hdiv : (k * 2 ^ (e + 1) + (2 ^ (e + 1) - 1)) / 2 ^ (e + 1) = k := by
    rw [Nat.mul_comm k _, Nat.mul_add_div hq, Nat.div_eq_of_lt (by omega)]
    omega
  rw [hdiv]
  exact Ideal.subset_span (by simp)

theorem leftPoint_not_equal (k e : ℕ) :
    principalTestIdeal (X : R) (leftPoint k e) ≠ principalTestIdeal X (k + 1 : ℕ) := by
  intro h
  have hm := leftPoint_witness k e
  rw [h, testIdeal_integer, Ideal.mem_span_singleton, X_pow_dvd_X_pow] at hm
  omega

/-- The actual test ideal changes at parameters arbitrarily close from below. -/
def IsLeftJump (f : R) (c : ℝ) : Prop :=
  0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ t : ℝ,
    0 ≤ t ∧ c - ε < t ∧ t < c ∧ principalTestIdeal f t ≠ principalTestIdeal f c

theorem positive_integer_left_jump (k : ℕ) : IsLeftJump (X : R) (k + 1 : ℕ) := by
  refine ⟨by positivity, ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hp : (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    have hnat : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
    exact_mod_cast hnat.le
  have hsmall : ((2 : ℝ) ^ (n + 1))⁻¹ < ε := by
    have hi := one_div_le_one_div_of_le (by positivity : 0 < (n + 1 : ℝ)) hp
    exact lt_of_le_of_lt (by simpa [one_div] using hi) hn
  refine ⟨leftPoint k n, by unfold leftPoint; positivity, ?_, ?_, leftPoint_not_equal k n⟩
  · rw [leftPoint_formula]
    linarith
  · rw [leftPoint_formula]
    have hi : 0 < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
    linarith

/-- The usual F-jump criterion for the decreasing test-ideal family. -/
def IsFJump (f : R) (c : ℝ) : Prop :=
  0 < c ∧ ∀ t : ℝ, 0 ≤ t → t < c → principalTestIdeal f t ≠ principalTestIdeal f c

theorem positive_integer_jump (k : ℕ) : IsFJump (X : R) (k + 1 : ℕ) := by
  obtain ⟨hpos, hjump⟩ := positive_integer_left_jump k
  refine ⟨hpos, ?_⟩
  intro t ht htc heq
  obtain ⟨u, _, hlu, huc, hne⟩ := hjump ((k + 1 : ℕ) - t) (sub_pos.mpr htc)
  have htu : t < u := by linarith
  have hle := testIdeal_antitone htu.le
  rw [heq] at hle
  exact hne (le_antisymm hle (testIdeal_antitone huc.le))

theorem infinitely_many_jumps : Set.Infinite {c : ℝ | IsFJump (X : R) c} := by
  apply Set.Infinite.mono (Set.range_subset_iff.mpr positive_integer_jump)
  apply Set.infinite_range_of_injective (f := fun k : ℕ => ((k + 1 : ℕ) : ℝ))
  intro i j hij
  exact Nat.add_right_cancel (Nat.cast_injective hij)

end TLMC3890
