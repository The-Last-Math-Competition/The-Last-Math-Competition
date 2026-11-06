import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace Conjecture2819

abbrev Sample := ℕ → ℝ

noncomputable def gaussianProduct : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gaussianProduct := by
  unfold gaussianProduct
  infer_instance

def coordinate (i : ℕ) (ω : Sample) : ℝ := ω i

theorem coordinate_law (i : ℕ) :
    gaussianProduct.map (coordinate i) = gaussianReal 0 1 := by
  ext s hs
  rw [Measure.map_apply (show Measurable (coordinate i) from measurable_pi_apply i) hs]
  have hset : coordinate i ⁻¹' s = Set.pi ({i} : Finset ℕ) (fun _ => s) := by
    ext ω
    simp [coordinate]
  rw [hset, gaussianProduct, Measure.infinitePi_pi (fun _ : ℕ => gaussianReal 0 1)]
  · simp
  · intro j hj
    exact hs

theorem coordinates_independent : iIndepFun coordinate gaussianProduct := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hset : (⋂ i ∈ S, coordinate i ⁻¹' sets i) = Set.pi (S : Set ℕ) sets := by
    ext ω
    simp [coordinate, Set.mem_pi]
  rw [hset, gaussianProduct, Measure.infinitePi_pi (fun _ : ℕ => gaussianReal 0 1) hsets]
  apply Finset.prod_congr rfl
  intro i hi
  have h := congrArg (fun μ : Measure ℝ => μ (sets i)) (coordinate_law i)
  dsimp only at h
  rw [Measure.map_apply (show Measurable (coordinate i) from measurable_pi_apply i) (hsets i hi)] at h
  exact h.symm

def blockSum (m n : ℕ) (ω : Sample) : ℝ := ∑ j ∈ Finset.range n, ω (m + j)

theorem blockSum_add (m n k : ℕ) (ω : Sample) :
    blockSum m (n + k) ω = blockSum m n ω + blockSum (m + n) k ω := by
  simp only [blockSum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_assoc]

theorem blockSum_subadditive (m n k : ℕ) (ω : Sample) :
    blockSum m (n + k) ω ≤ blockSum m n ω + blockSum (m + n) k ω :=
  (blockSum_add m n k ω).le

def partialSum (n : ℕ) : Sample → ℝ := blockSum 0 n

theorem partialSum_measurable (n : ℕ) : Measurable (partialSum n) := by
  unfold partialSum blockSum
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply _)

theorem partialSum_mgf (n : ℕ) (t : ℝ) :
    mgf (partialSum n) gaussianProduct t = Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  have hsum : partialSum n = ∑ i ∈ Finset.range n, coordinate i := by
    funext ω
    simp [partialSum, blockSum, coordinate]
  rw [hsum, coordinates_independent.mgf_sum (fun i => measurable_pi_apply i)]
  simp_rw [mgf_gaussianReal (coordinate_law _) t]
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add,
    Finset.prod_const, Finset.card_range]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

noncomputable def sampleMean (n : ℕ) (ω : Sample) : ℝ := partialSum (n + 1) ω / (n + 1)

theorem sampleMean_measurable (n : ℕ) : Measurable (sampleMean n) :=
  (partialSum_measurable (n + 1)).div_const _

noncomputable def meanLaw (n : ℕ) : Measure ℝ := gaussianProduct.map (sampleMean n)

instance (n : ℕ) : IsProbabilityMeasure (meanLaw n) :=
  isProbabilityMeasure_map (sampleMean_measurable n).aemeasurable

theorem partialSum_exp_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * partialSum n ω)) gaussianProduct := by
  by_contra h
  have hz := integral_undef h
  change mgf (partialSum n) gaussianProduct t = 0 at hz
  rw [partialSum_mgf] at hz
  exact Real.exp_ne_zero _ hz

theorem mean_right_tail (n : ℕ) :
    (meanLaw n).real (Set.Ioi 1) ≤ Real.exp (-((n + 1 : ℕ) : ℝ) / 2) := by
  have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := gaussianProduct)
    (X := partialSum (n + 1)) ((n + 1 : ℕ) : ℝ) (t := 1) (by norm_num)
    (partialSum_exp_integrable (n + 1) 1)
  rw [partialSum_mgf, ← Real.exp_add] at hchernoff
  have hsub : sampleMean n ⁻¹' Set.Ioi 1 ⊆
      {ω | ((n + 1 : ℕ) : ℝ) ≤ partialSum (n + 1) ω} := by
    intro ω hω
    have hω' : 1 < partialSum (n + 1) ω / ((n + 1 : ℕ) : ℝ) := by
      simpa [sampleMean, Nat.cast_add, Nat.cast_one] using hω
    simpa only [one_mul, Set.mem_setOf_eq] using le_of_lt ((lt_div_iff₀ hp).mp hω')
  have hmono := measureReal_mono (μ := gaussianProduct) hsub
  have heq : (meanLaw n).real (Set.Ioi 1) =
      gaussianProduct.real (sampleMean n ⁻¹' Set.Ioi 1) := by
    rw [Measure.real, meanLaw, Measure.map_apply (sampleMean_measurable n) measurableSet_Ioi]
    rfl
  rw [heq]
  calc
    _ ≤ gaussianProduct.real {ω | ((n + 1 : ℕ) : ℝ) ≤ partialSum (n + 1) ω} := hmono
    _ ≤ Real.exp (-1 * ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * 1 ^ 2 / 2) := hchernoff
    _ = Real.exp (-((n + 1 : ℕ) : ℝ) / 2) := by congr 1; ring

/-- Every genuine open interval has positive probability under every mean law. -/
theorem mean_interval_positive (n : ℕ) (a b : ℝ) (hab : a < b) :
    0 < meanLaw n (Set.Ioo a b) := by
  have hg : 0 < gaussianReal 0 1 (Set.Ioo a b) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hv := (gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num)) hz
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hv
    linarith
  have hbox : 0 < gaussianProduct (Set.pi (Finset.range (n + 1)) (fun _ => Set.Ioo a b)) := by
    rw [gaussianProduct, Measure.infinitePi_pi (fun _ : ℕ => gaussianReal 0 1)
      (fun _ _ => measurableSet_Ioo)]
    exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => ne_of_gt hg))
  have hsub : Set.pi (Finset.range (n + 1)) (fun _ => Set.Ioo a b) ⊆
      sampleMean n ⁻¹' Set.Ioo a b := by
    intro ω hω
    have hnon : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
    have hlo := Finset.sum_lt_sum_of_nonempty hnon
      (fun i hi => (hω i hi).1)
    have hhi := Finset.sum_lt_sum_of_nonempty hnon
      (fun i hi => (hω i hi).2)
    have hs : partialSum (n + 1) ω = ∑ i ∈ Finset.range (n + 1), ω i := by
      simp [partialSum, blockSum]
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    change a < sampleMean n ω ∧ sampleMean n ω < b
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlo hhi
    constructor
    · simp only [sampleMean, Nat.cast_add, Nat.cast_one]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      simpa [hs, mul_comm] using hlo
    · simp only [sampleMean, Nat.cast_add, Nat.cast_one]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      simpa [hs, mul_comm] using hhi
  rw [meanLaw, Measure.map_apply (sampleMean_measurable n) measurableSet_Ioo]
  exact lt_of_lt_of_le hbox (measure_mono hsub)

theorem coordinate_cgf (i : ℕ) (t : ℝ) :
    cgf (coordinate i) gaussianProduct t = t ^ 2 / 2 := by
  simpa using cgf_gaussianReal (coordinate_law i) t

/-- A supplementary exact computation of the Cramer transform of the true increment law. -/
noncomputable def cramerTransform (x : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => t * x - cgf (coordinate 0) gaussianProduct t))

theorem cramerTransform_eq (x : ℝ) : cramerTransform x = x ^ 2 / 2 := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨x, ?_⟩
    dsimp only
    rw [coordinate_cgf]
    ring
  · rintro y ⟨t, rfl⟩
    dsimp only
    rw [coordinate_cgf]
    nlinarith [sq_nonneg (t - x)]

theorem cramerTransform_not_affine :
    ¬ ∃ a b : ℝ, ∀ x : ℝ, cramerTransform x = a * x + b := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have hn := h (-1)
  simp only [cramerTransform_eq] at h0 h1 hn
  norm_num at h0 h1 hn
  linarith

/-- The usual full LDP for a finite real-valued rate at speed n+1,
expressed through epsilon exponential bounds on all open and closed sets. -/
structure HasLDP (I : ℝ → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ I x
  lowerSemicontinuous : LowerSemicontinuous I
  lower : ∀ G : Set ℝ, IsOpen G → ∀ x ∈ G, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, Real.exp (-((n + 1 : ℕ) : ℝ) * (I x + ε)) ≤ (meanLaw n).real G
  upper : ∀ F : Set ℝ, IsClosed F → ∀ a : ℝ, (∀ x ∈ F, a ≤ I x) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (meanLaw n).real F ≤ Real.exp (-((n + 1 : ℕ) : ℝ) * (a - ε))

theorem nonnegative_affine_slope_zero {a b : ℝ} (h : ∀ x : ℝ, 0 ≤ a * x + b) :
    a = 0 := by
  by_contra ha
  have heq : a * ((-b - 1) / a) + b = -1 := by
    field_simp
    ring
  have hx' := h ((-b - 1) / a)
  rw [heq] at hx'
  norm_num at hx'

theorem no_affine_ldp (a b : ℝ) : ¬ HasLDP (fun x => a * x + b) := by
  intro h
  have ha : a = 0 := nonnegative_affine_slope_zero h.nonnegative
  subst a
  have hb0 : 0 ≤ b := by simpa using h.nonnegative 0
  have hb : b = 0 := by
    by_contra hb
    have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hu := h.upper Set.univ isClosed_univ b (by intro x hx; simp)
      (b / 2) (by linarith)
    obtain ⟨n, hn⟩ := hu.exists
    have hone : (meanLaw n).real Set.univ = 1 := by simp
    rw [hone] at hn
    have hneg : -((n + 1 : ℕ) : ℝ) * (b - b / 2) < 0 := by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    have hlt : Real.exp (-((n + 1 : ℕ) : ℝ) * (b - b / 2)) < 1 :=
      Real.exp_lt_one_iff.mpr hneg
    linarith
  subst b
  have hl := h.lower (Set.Ioo 1 2) isOpen_Ioo (3 / 2)
    (by constructor <;> norm_num) (1 / 4) (by norm_num)
  obtain ⟨n, hn⟩ := hl.exists
  have ht := mean_right_tail n
  have hm : (meanLaw n).real (Set.Ioo 1 2) ≤ (meanLaw n).real (Set.Ioi 1) :=
    measureReal_mono (by intro x hx; exact hx.1)
  have hcontra : Real.exp (-((n + 1 : ℕ) : ℝ) * (1 / 4)) ≤
      Real.exp (-((n + 1 : ℕ) : ℝ) / 2) := by
    simpa using hn.trans (hm.trans ht)
  have hle := Real.exp_le_exp.mp hcontra
  have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

def LinearRateAssertion : Prop := ∃ a b : ℝ, HasLDP (fun x => a * x + b)

theorem disprove_linear_rate_assertion : ¬ LinearRateAssertion := by
  rintro ⟨a, b, hab⟩
  exact no_affine_ldp a b hab

theorem independent_subadditive_counterexample :
    iIndepFun coordinate gaussianProduct ∧
    (∀ i, gaussianProduct.map (coordinate i) = gaussianReal 0 1) ∧
    (∀ m n k ω, blockSum m (n + k) ω ≤ blockSum m n ω + blockSum (m + n) k ω) ∧
    ¬ LinearRateAssertion :=
  ⟨coordinates_independent, coordinate_law, blockSum_subadditive,
    disprove_linear_rate_assertion⟩

end Conjecture2819

#print axioms Conjecture2819.coordinates_independent
#print axioms Conjecture2819.blockSum_subadditive
#print axioms Conjecture2819.partialSum_mgf
#print axioms Conjecture2819.mean_right_tail
#print axioms Conjecture2819.mean_interval_positive
#print axioms Conjecture2819.cramerTransform_eq
#print axioms Conjecture2819.disprove_linear_rate_assertion
#print axioms Conjecture2819.independent_subadditive_counterexample
