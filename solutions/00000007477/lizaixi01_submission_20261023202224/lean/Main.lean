import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

open Filter Topology
open scoped ENNReal NNReal
noncomputable section
set_option maxHeartbeats 800000

namespace TLMC7477

abbrev C0 := ZeroAtInftyContinuousMap ℕ ℝ

def sequence (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : C0 where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using hf

theorem tends_zero (f : C0) : Tendsto f atTop (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    using ZeroAtInftyContinuousMapClass.zero_at_infty f

theorem value_le_norm (f : C0) (n : ℕ) : |f n| ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF n

theorem norm_le_iff (f : C0) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ n, |f n| ≤ C :=
  BoundedContinuousFunction.norm_le hC

instance pointwiseOrder : PartialOrder C0 where
  le f g := ∀ n, f n ≤ g n
  le_refl f n := le_refl _
  le_trans f g h hfg hgh n := le_trans (hfg n) (hgh n)
  le_antisymm f g hfg hgf := ZeroAtInftyContinuousMap.ext (fun n => le_antisymm (hfg n) (hgf n))

def pointwiseSup (f g : C0) : C0 :=
  sequence (fun n => max (f n) (g n)) (by simpa using (tends_zero f).max (tends_zero g))

def pointwiseInf (f g : C0) : C0 :=
  sequence (fun n => min (f n) (g n)) (by simpa using (tends_zero f).min (tends_zero g))

instance pointwiseLattice : Lattice C0 where
  sup := pointwiseSup
  le_sup_left _f _g _n := le_max_left _ _
  le_sup_right _f _g _n := le_max_right _ _
  sup_le _f _g _h hfh hgh n := max_le (hfh n) (hgh n)
  inf := pointwiseInf
  inf_le_left _f _g _n := min_le_left _ _
  inf_le_right _f _g _n := min_le_right _ _
  le_inf _f _g _h hfg hfh n := le_min (hfg n) (hfh n)

theorem abs_apply (f : C0) (n : ℕ) : (|f| : C0) n = |f n| := by
  change max (f n) (-f n) = |f n|
  exact abs_eq_max_neg.symm

instance orderedAddition : IsOrderedAddMonoid C0 where
  add_le_add_left _f _g h k n := add_le_add_left (h n) (k n)

instance solidNorm : HasSolidNorm C0 where
  solid {f g} h := by
    apply (norm_le_iff f (norm_nonneg g)).mpr
    intro n
    exact le_trans (by simpa only [abs_apply] using h n) (value_le_norm g n)

theorem positive_smul {c : ℝ} (hc : 0 ≤ c) {f : C0} (hf : 0 ≤ f) : 0 ≤ c • f := by
  intro n
  exact mul_nonneg hc (hf n)

def rightShift (f : C0) : C0 := sequence (fun n => match n with
  | 0 => 0
  | n + 1 => f n) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tends_zero f) ε hε
    refine ⟨N + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hN n (by omega))

def leftShift (f : C0) : C0 := sequence (fun n => f (n + 1)) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tends_zero f) ε hε
    exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩)

theorem rightShift_norm_le (f : C0) : ‖rightShift f‖ ≤ ‖f‖ := by
  apply (norm_le_iff _ (norm_nonneg f)).mpr
  intro n
  cases n with
  | zero => change |(0 : ℝ)| ≤ ‖f‖; simp
  | succ n => exact value_le_norm f n

theorem leftShift_norm_le (f : C0) : ‖leftShift f‖ ≤ ‖f‖ := by
  apply (norm_le_iff _ (norm_nonneg f)).mpr
  intro n
  exact value_le_norm f (n + 1)

def adjacency : C0 →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := fun f => rightShift f + leftShift f
      map_add' := by
        intro f g
        ext n
        cases n <;> simp [rightShift, leftShift, sequence, add_add_add_comm]
      map_smul' := by
        intro c f
        ext n
        cases n <;> simp [rightShift, leftShift, sequence] }
    2 (by
      intro f
      change ‖rightShift f + leftShift f‖ ≤ 2 * ‖f‖
      have h := norm_add_le (rightShift f) (leftShift f)
      linarith [rightShift_norm_le f, leftShift_norm_le f])

theorem adjacency_zero (f : C0) : adjacency f 0 = f 1 := by
  simp [adjacency, rightShift, leftShift, sequence]

theorem adjacency_succ (f : C0) (n : ℕ) : adjacency f (n + 1) = f n + f (n + 2) := rfl

theorem adjacency_positive {f : C0} (hf : 0 ≤ f) : 0 ≤ adjacency f := by
  intro n
  cases n with
  | zero => change (0 : ℝ) ≤ adjacency f 0; rw [adjacency_zero]; exact hf 1
  | succ n => exact add_nonneg (hf n) (hf (n + 2))

theorem adjacency_norm_le : ‖adjacency‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound adjacency (by norm_num)
  intro f
  change ‖rightShift f + leftShift f‖ ≤ _
  linarith [norm_add_le (rightShift f) (leftShift f), rightShift_norm_le f, leftShift_norm_le f]

def delta (k : ℕ) : C0 := sequence (fun n => if n = k then 1 else 0) (by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  refine ⟨k + 1, ?_⟩
  intro n hn
  have hne : n ≠ k := by omega
  simpa [hne] using hε)

theorem delta_self (k : ℕ) : delta k k = 1 := by simp [delta, sequence]
theorem delta_other (k n : ℕ) (h : n ≠ k) : delta k n = 0 := by simp [delta, sequence, h]

theorem delta_nonzero (k : ℕ) : delta k ≠ 0 := by
  intro h
  have hh := congrArg (fun f : C0 => f k) h
  simp [delta_self] at hh

instance nontrivialC0 : Nontrivial C0 := ⟨⟨delta 0, 0, delta_nonzero 0⟩⟩

theorem adjacency_no_eigenvector_two (f : C0) (hf : adjacency f = (2 : ℝ) • f) : f = 0 := by
  have hrec (n : ℕ) : f n = (n + 1 : ℕ) * f 0 := by
    induction n using Nat.twoStepInduction with
    | zero => simp
    | one =>
      have h := congrArg (fun g : C0 => g 0) hf
      simpa [adjacency_zero] using h
    | more n hn hn1 =>
      have h := congrArg (fun g : C0 => g (n + 1)) hf
      rw [adjacency_succ] at h
      change f n + f (n + 2) = 2 * f (n + 1) at h
      rw [hn, hn1] at h
      push_cast at *
      linarith
  have hdiff : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => f (n + 1)) atTop (𝓝 0) := tends_zero (leftShift f)
    simpa using hs.sub (tends_zero f)
  have hconstant : (fun n => f (n + 1) - f n) = (fun _ => f 0) := by
    funext n
    rw [hrec (n + 1), hrec n]
    push_cast
    ring
  rw [hconstant] at hdiff
  have hz : f 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  ext n
  change f n = 0
  rw [hrec, hz]
  simp

theorem delta_mem_of_coordinate (I : Submodule ℝ C0)
    (hs : LatticeOrderedAddCommGroup.IsSolid (I : Set C0))
    {f : C0} (hf : f ∈ I) {n : ℕ} (hn : f n ≠ 0) : delta n ∈ I := by
  have hd : f n • delta n ∈ I := by
    apply hs hf
    intro j
    simp only [abs_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    by_cases hj : j = n
    · subst j
      rw [delta_self, mul_one]
    · rw [delta_other n j hj, mul_zero, abs_zero]
      exact abs_nonneg _
  have h := I.smul_mem (f n)⁻¹ hd
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using h

theorem delta_next_mem (I : Submodule ℝ C0)
    (hs : LatticeOrderedAddCommGroup.IsSolid (I : Set C0))
    (hi : ∀ f ∈ I, adjacency f ∈ I) {n : ℕ} (hn : delta n ∈ I) :
    delta (n + 1) ∈ I := by
  apply delta_mem_of_coordinate I hs (hi _ hn)
  rw [adjacency_succ, delta_self, delta_other n (n + 2) (by omega)]
  norm_num

theorem delta_prev_mem (I : Submodule ℝ C0)
    (hs : LatticeOrderedAddCommGroup.IsSolid (I : Set C0))
    (hi : ∀ f ∈ I, adjacency f ∈ I) {n : ℕ} (hn : delta (n + 1) ∈ I) :
    delta n ∈ I := by
  apply delta_mem_of_coordinate I hs (hi _ hn)
  cases n with
  | zero => rw [adjacency_zero, delta_self]; norm_num
  | succ n =>
    rw [adjacency_succ, delta_other (n + 1 + 1) n (by omega)]
    have h : n + 2 = n + 1 + 1 := by omega
    rw [h, delta_self]
    norm_num

theorem delta_zero_mem (I : Submodule ℝ C0)
    (hs : LatticeOrderedAddCommGroup.IsSolid (I : Set C0))
    (hi : ∀ f ∈ I, adjacency f ∈ I) (n : ℕ) : delta n ∈ I → delta 0 ∈ I := by
  induction n with
  | zero => exact id
  | succ n hn => exact fun h => hn (delta_prev_mem I hs hi h)

def truncation (N : ℕ) (f : C0) : C0 :=
  sequence (fun n => if n < N then f n else 0) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    refine ⟨N, ?_⟩
    intro n hn
    simpa [not_lt.mpr hn] using hε)

theorem truncation_sum (N : ℕ) (f : C0) :
    truncation N f = ∑ j ∈ Finset.range N, f j • delta j := by
  induction N with
  | zero => ext n; simp [truncation, sequence]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← hN]
    ext n
    simp only [ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
      smul_eq_mul]
    by_cases hn : n = N
    · subst n
      simp [truncation, sequence, delta_self]
    · rw [delta_other N n hn, mul_zero, add_zero]
      have hiff : n < N + 1 ↔ n < N := by omega
      change (if n < N + 1 then f n else 0) = (if n < N then f n else 0)
      simp only [hiff]

theorem truncation_tends (f : C0) : Tendsto (fun N => truncation N f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tends_zero f) (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro M hM
  rw [dist_eq_norm]
  have hbound : ‖truncation M f - f‖ ≤ ε / 2 := by
    apply (norm_le_iff _ (by linarith)).mpr
    intro n
    change |(if n < M then f n else 0) - f n| ≤ ε / 2
    split_ifs with hn
    · simp; linarith
    · have ht := hN n (by omega)
      simpa [Real.dist_eq, abs_sub_comm] using le_of_lt ht
  linarith

theorem adjacency_ideal_irreducible (I : Submodule ℝ C0)
    (hc : IsClosed (I : Set C0))
    (hs : LatticeOrderedAddCommGroup.IsSolid (I : Set C0))
    (hi : ∀ f ∈ I, adjacency f ∈ I) : I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ f ∈ I, f ≠ 0 := by
    by_contra! h
    apply hI
    apply le_antisymm
    · intro f hf
      exact (Submodule.mem_bot ℝ).mpr (h f hf)
    · exact bot_le
  obtain ⟨f, hf, hf0⟩ := hex
  have hn : ∃ n, f n ≠ 0 := by
    by_contra! hn
    apply hf0
    ext n
    exact hn n
  obtain ⟨n, hn⟩ := hn
  have hz := delta_zero_mem I hs hi n (delta_mem_of_coordinate I hs hf hn)
  have hall : ∀ j, delta j ∈ I := by
    intro j
    induction j with
    | zero => exact hz
    | succ j hj => exact delta_next_mem I hs hi hj
  apply top_unique
  intro g _
  apply hc.mem_of_tendsto (truncation_tends g)
  apply Filter.Eventually.of_forall
  intro N
  rw [truncation_sum]
  exact I.sum_mem (fun j _ => I.smul_mem (g j) (hall j))

theorem shifted_no_preimage (f : C0) : (2 : ℝ) • f - adjacency f ≠ delta 0 := by
  intro hf
  have hrec (n : ℕ) : f n = (n + 1 : ℕ) * f 0 - n := by
    induction n using Nat.twoStepInduction with
    | zero => simp
    | one =>
      have h := congrArg (fun g : C0 => g 0) hf
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
        smul_eq_mul, adjacency_zero, delta_self] at h
      push_cast
      linarith
    | more n hn hn1 =>
      have h := congrArg (fun g : C0 => g (n + 1)) hf
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
        smul_eq_mul, adjacency_succ, delta_other 0 (n + 1) (by omega)] at h
      rw [hn, hn1] at h
      push_cast at *
      linarith
  have hd : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => f (n + 1)) atTop (𝓝 0) := tends_zero (leftShift f)
    simpa using hs.sub (tends_zero f)
  have he : (fun n => f (n + 1) - f n) = (fun _ => f 0 - 1) := by
    funext n
    rw [hrec (n + 1), hrec n]
    push_cast
    ring
  rw [he] at hd
  have hh : f 0 - 1 = 0 := tendsto_nhds_unique tendsto_const_nhds hd
  have hz : f 0 = 1 := by linarith
  have heq : (f : ℕ → ℝ) = (fun _ => 1) := by
    funext n
    rw [hrec n, hz]
    push_cast
    ring
  have ht := tends_zero f
  rw [heq] at ht
  have hfalse : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at hfalse

theorem two_mem_spectrum : (2 : ℝ) ∈ spectrum ℝ adjacency := by
  rw [spectrum.mem_iff]
  simp only [Algebra.algebraMap_eq_smul_one]
  rintro ⟨u, hu⟩
  let v : C0 := (↑(u⁻¹) : C0 →L[ℝ] C0) (delta 0)
  have h : (((2 : ℝ) • (1 : C0 →L[ℝ] C0) - adjacency) v) = delta 0 := by
    rw [← hu]
    change (((u : C0 →L[ℝ] C0) * ↑(u⁻¹)) (delta 0)) = delta 0
    simp
  apply shifted_no_preimage v
  simpa only [sub_apply, smul_apply, one_apply_eq_self] using h

theorem adjacency_spectral_radius : spectralRadius ℝ adjacency = 2 := by
  apply le_antisymm
  · apply le_trans (spectrum.spectralRadius_le_nnnorm (𝕜 := ℝ) adjacency)
    exact_mod_cast adjacency_norm_le
  · have h : (‖(2 : ℝ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ adjacency :=
      le_iSup₂ (α := ℝ≥0∞) (2 : ℝ) two_mem_spectrum
    norm_num at h ⊢
    exact h

abbrev ComplexC0 := ZeroAtInftyContinuousMap ℕ ℂ

def complexSequence (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ComplexC0 where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using hf

theorem complex_tends_zero (f : ComplexC0) : Tendsto f atTop (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    using ZeroAtInftyContinuousMapClass.zero_at_infty f

def complexRightShift (f : ComplexC0) : ComplexC0 :=
  complexSequence (fun n => match n with | 0 => 0 | n + 1 => f n) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (complex_tends_zero f) ε hε
    refine ⟨N + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hN n (by omega))

def complexLeftShift (f : ComplexC0) : ComplexC0 :=
  complexSequence (fun n => f (n + 1)) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (complex_tends_zero f) ε hε
    exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩)

theorem complexRightShift_norm_le (f : ComplexC0) : ‖complexRightShift f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro n
  cases n with
  | zero => change ‖(0 : ℂ)‖ ≤ ‖f‖; simp
  | succ n => exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF n

theorem complexLeftShift_norm_le (f : ComplexC0) : ‖complexLeftShift f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro n
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF (n + 1)

def complexAdjacency : ComplexC0 →L[ℂ] ComplexC0 :=
  LinearMap.mkContinuous
    { toFun := fun f => complexRightShift f + complexLeftShift f
      map_add' := by
        intro f g
        ext n
        cases n <;> simp [complexRightShift, complexLeftShift, complexSequence,
          add_add_add_comm]
      map_smul' := by
        intro c f
        ext n
        cases n <;> simp [complexRightShift, complexLeftShift, complexSequence] }
    2 (by
      intro f
      change ‖complexRightShift f + complexLeftShift f‖ ≤ 2 * ‖f‖
      linarith [norm_add_le (complexRightShift f) (complexLeftShift f),
        complexRightShift_norm_le f, complexLeftShift_norm_le f])

theorem complexAdjacency_norm_le : ‖complexAdjacency‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound complexAdjacency (by norm_num)
  intro f
  change ‖complexRightShift f + complexLeftShift f‖ ≤ _
  linarith [norm_add_le (complexRightShift f) (complexLeftShift f),
    complexRightShift_norm_le f, complexLeftShift_norm_le f]

def realPart (f : ComplexC0) : C0 :=
  sequence (fun n => (f n).re) (by
    exact (Complex.continuous_re.tendsto (0 : ℂ)).comp (complex_tends_zero f))

def complexDelta (k : ℕ) : ComplexC0 :=
  complexSequence (fun n => if n = k then 1 else 0) (by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    refine ⟨k + 1, ?_⟩
    intro n hn
    have hne : n ≠ k := by omega
    simpa [hne] using hε)

theorem realPart_complexDelta (k : ℕ) : realPart (complexDelta k) = delta k := by
  ext n
  by_cases hn : n = k <;> simp [realPart, complexDelta, complexSequence, sequence, delta, hn]

theorem complexDelta_nonzero (k : ℕ) : complexDelta k ≠ 0 := by
  intro h
  have hh := congrArg (fun f : ComplexC0 => f k) h
  simp [complexDelta, complexSequence] at hh

instance nontrivialComplexC0 : Nontrivial ComplexC0 :=
  ⟨⟨complexDelta 0, 0, complexDelta_nonzero 0⟩⟩

theorem realPart_shifted (f : ComplexC0) :
    realPart ((2 : ℂ) • f - complexAdjacency f) =
      (2 : ℝ) • realPart f - adjacency (realPart f) := by
  ext n
  cases n <;>
    simp [realPart, complexAdjacency, complexRightShift, complexLeftShift,
      complexSequence, sequence, adjacency, rightShift, leftShift]

theorem complex_two_mem_spectrum : (2 : ℂ) ∈ spectrum ℂ complexAdjacency := by
  rw [spectrum.mem_iff]
  simp only [Algebra.algebraMap_eq_smul_one]
  rintro ⟨u, hu⟩
  let v : ComplexC0 := (↑(u⁻¹) : ComplexC0 →L[ℂ] ComplexC0) (complexDelta 0)
  have h : (((2 : ℂ) • (1 : ComplexC0 →L[ℂ] ComplexC0) - complexAdjacency) v) =
      complexDelta 0 := by
    rw [← hu]
    change (((u : ComplexC0 →L[ℂ] ComplexC0) * ↑(u⁻¹)) (complexDelta 0)) = complexDelta 0
    simp
  have hh : (2 : ℂ) • v - complexAdjacency v = complexDelta 0 := by
    simpa only [sub_apply, smul_apply, one_apply_eq_self] using h
  have hr := congrArg realPart hh
  rw [realPart_shifted, realPart_complexDelta] at hr
  exact shifted_no_preimage (realPart v) hr

theorem complexAdjacency_spectral_radius : spectralRadius ℂ complexAdjacency = 2 := by
  apply le_antisymm
  · apply le_trans (spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) complexAdjacency)
    exact_mod_cast complexAdjacency_norm_le
  · have h : (‖(2 : ℂ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ complexAdjacency :=
      le_iSup₂ (α := ℝ≥0∞) (2 : ℂ) complex_two_mem_spectrum
    norm_num at h ⊢
    exact h

def complexification (f : C0) : ComplexC0 :=
  complexSequence (fun n => (f n : ℂ)) (by
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tends_zero f))

theorem complexification_injective : Function.Injective complexification := by
  intro f g h
  ext n
  have hn := congrArg (fun u : ComplexC0 => (u n).re) h
  change (f n : ℂ).re = (g n : ℂ).re at hn
  exact hn

theorem complexification_intertwines (f : C0) :
    complexAdjacency (complexification f) = complexification (adjacency f) := by
  ext n
  cases n <;>
    simp [complexification, complexAdjacency, complexRightShift, complexLeftShift,
      complexSequence, sequence, adjacency, rightShift, leftShift]

theorem complexification_add (f g : C0) :
    complexification (f + g) = complexification f + complexification g := by
  ext n
  change ((f n + g n : ℝ) : ℂ) = (f n : ℂ) + (g n : ℂ)
  exact Complex.ofReal_add _ _

theorem complexification_smul (c : ℝ) (f : C0) :
    complexification (c • f) = (c : ℂ) • complexification f := by
  ext n
  change ((c * f n : ℝ) : ℂ) = (c : ℂ) * (f n : ℂ)
  exact Complex.ofReal_mul _ _

theorem complexification_norm (f : C0) : ‖complexification f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro n
    change ‖(f n : ℂ)‖ ≤ ‖f‖
    simpa only [Complex.norm_real, Real.norm_eq_abs] using value_le_norm f n
  · apply (norm_le_iff f (norm_nonneg (complexification f))).mpr
    intro n
    have h := BoundedContinuousFunction.norm_coe_le_norm (complexification f).toBCF n
    change ‖(f n : ℂ)‖ ≤ ‖complexification f‖ at h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h

def imagPart (f : ComplexC0) : C0 :=
  sequence (fun n => (f n).im) (by
    exact (Complex.continuous_im.tendsto (0 : ℂ)).comp (complex_tends_zero f))

theorem complexification_decomposition (f : ComplexC0) :
    f = complexification (realPart f) + Complex.I • complexification (imagPart f) := by
  ext n
  change f n = ((f n).re : ℂ) + Complex.I * ((f n).im : ℂ)
  apply Complex.ext <;> simp

theorem no_spectral_radius_eigenvector :
    ¬ ∃ f : C0, f ≠ 0 ∧
      adjacency f = (spectralRadius ℂ complexAdjacency).toReal • f := by
  rw [complexAdjacency_spectral_radius]
  norm_num only [ENNReal.toReal_ofNat]
  rintro ⟨f, hne, hf⟩
  exact hne (adjacency_no_eigenvector_two f hf)

theorem perron_frobenius_counterexample :
    (∀ f : C0, 0 ≤ f → 0 ≤ adjacency f) ∧
    (∀ I : Submodule ℝ C0, IsClosed (I : Set C0) →
      LatticeOrderedAddCommGroup.IsSolid (I : Set C0) →
      (∀ f ∈ I, adjacency f ∈ I) → I = ⊥ ∨ I = ⊤) ∧
    spectralRadius ℂ complexAdjacency = 2 ∧
    (∀ f : C0, adjacency f = (2 : ℝ) • f → f = 0) :=
  ⟨fun _ hf => adjacency_positive hf, adjacency_ideal_irreducible,
    complexAdjacency_spectral_radius, adjacency_no_eigenvector_two⟩

end TLMC7477
