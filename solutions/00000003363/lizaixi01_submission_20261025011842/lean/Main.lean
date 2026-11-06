import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped Uniformity SetRel ENNReal NNReal

namespace TLMC3363

/-- The full usual real logistic parameter interval, including its endpoints. -/
abbrev Parameter := Set.Icc (0 : ℝ) 4

/-- The whole invariant phase interval, rather than an attracting sub-basin. -/
abbrev Phase := Set.Icc (0 : ℝ) 1

def quadratic (a x : ℝ) : ℝ := a * x * (1 - x)

def quadraticPolynomial (a : ℝ) : Polynomial ℝ :=
  Polynomial.C (-a) * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C 0

theorem polynomial_eval (a x : ℝ) :
    (quadraticPolynomial a).eval x = quadratic a x := by
  simp [quadraticPolynomial, quadratic]
  ring

theorem polynomial_degree_two {a : ℝ} (ha : 0 < a) :
    (quadraticPolynomial a).natDegree = 2 := by
  exact Polynomial.natDegree_quadratic (neg_ne_zero.mpr (ne_of_gt ha))

theorem quadratic_hasDerivAt (a x : ℝ) :
    HasDerivAt (quadratic a) (a * (1 - 2 * x)) x := by
  have h := (quadraticPolynomial a).hasDerivAt x
  have hf : (fun y : ℝ => (quadraticPolynomial a).eval y) = quadratic a :=
    funext (polynomial_eval a)
  rw [hf] at h
  apply h.congr_deriv
  simp [quadraticPolynomial]
  ring

theorem quadratic_deriv (a x : ℝ) :
    deriv (quadratic a) x = a * (1 - 2 * x) :=
  (quadratic_hasDerivAt a x).deriv

theorem quadratic_second_deriv (a x : ℝ) :
    deriv (deriv (quadratic a)) x = -2 * a := by
  have hfun : deriv (quadratic a) = fun y => a * (1 - 2 * y) :=
    funext (quadratic_deriv a)
  rw [hfun]
  let p : Polynomial ℝ := Polynomial.C (-2 * a) * Polynomial.X + Polynomial.C a
  have h := p.hasDerivAt x
  have hf : (fun y : ℝ => p.eval y) = fun y => a * (1 - 2 * y) := by
    funext y
    simp [p]
    ring
  rw [hf] at h
  simpa [p] using h.deriv

theorem unique_nondegenerate_critical {a : ℝ} (ha : 0 < a) :
    (∀ x : ℝ, deriv (quadratic a) x = 0 ↔ x = 1 / 2) ∧
      deriv (deriv (quadratic a)) (1 / 2) ≠ 0 := by
  constructor
  · intro x
    rw [quadratic_deriv]
    constructor
    · intro h
      have : 1 - 2 * x = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt ha)
      linarith
    · rintro rfl
      ring
  · rw [quadratic_second_deriv]
    exact mul_ne_zero (by norm_num) (ne_of_gt ha)

theorem maps_phase (a : Parameter) (x : Phase) : quadratic a x ∈ Set.Icc (0 : ℝ) 1 := by
  have hx := x.property
  have ha := a.property
  have h0 : 0 ≤ (x : ℝ) * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have h1 : (x : ℝ) * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg ((x : ℝ) - 1 / 2)]
  constructor
  · simpa only [quadratic, mul_assoc] using mul_nonneg ha.1 h0
  · have h := mul_le_mul_of_nonneg_right ha.2 h0
    dsimp only [quadratic]
    nlinarith

def logistic (a : Parameter) : Phase → Phase :=
  fun x => ⟨quadratic a x, maps_phase a x⟩

theorem logistic_val (a : Parameter) (x : Phase) :
    (logistic a x : ℝ) = (a : ℝ) * x * (1 - x) := rfl

theorem logistic_continuous (a : Parameter) : Continuous (logistic a) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : Phase => (a : ℝ) * x * (1 - x))
  fun_prop

theorem phase_compact : IsCompact (Set.univ : Set Phase) := isCompact_univ

def midpoint : Phase := ⟨1 / 2, by constructor <;> norm_num⟩

theorem value_at_midpoint (a : Parameter) :
    (logistic a midpoint : ℝ) = (a : ℝ) / 4 := by
  simp [logistic_val, midpoint]
  ring

theorem family_injective : Function.Injective logistic := by
  intro a b hab
  have h := congrArg (fun f : Phase → Phase => (f midpoint : ℝ)) hab
  rw [value_at_midpoint, value_at_midpoint] at h
  apply Subtype.ext
  linarith

theorem local_contraction (a : Parameter) (ha : (a : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    LipschitzWith (1 / 2) (logistic a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |(a : ℝ) * x * (1 - x) - (a : ℝ) * y * (1 - y)| ≤
    (1 / 2 : ℝ) * |(x : ℝ) - y|
  have hd : (a : ℝ) * x * (1 - x) - (a : ℝ) * y * (1 - y) =
      (a : ℝ) * ((x : ℝ) - y) * (1 - x - y) := by ring
  have hf : |1 - (x : ℝ) - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]
  rw [hd, abs_mul, abs_mul, abs_of_nonneg a.property.1]
  calc
    (a : ℝ) * |(x : ℝ) - y| * |1 - (x : ℝ) - y| ≤
        (a : ℝ) * |(x : ℝ) - y| * 1 :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg a.property.1 (abs_nonneg _))
    _ ≤ (1 / 2 : ℝ) * |(x : ℝ) - y| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right ha.2
        (abs_nonneg ((x : ℝ) - y))

/-- The all-time orbit distance bound used for every dynamical cover. -/
theorem iterate_nonexpanding {X : Type*} [PseudoMetricSpace X] (T : X → X)
    (hT : ∀ x y, dist (T x) (T y) ≤ dist x y) (n : ℕ) (x y : X) :
    dist (T^[n] x) (T^[n] y) ≤ dist x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using (hT (T^[n] x) (T^[n] y)).trans ih

theorem ennreal_log_nat (k : ℕ) (hk : 0 < k) :
    ENNReal.log (k : ℝ≥0∞) = (Real.log (k : ℝ) : EReal) := by
  have hc : ENNReal.ofReal (k : ℝ) = (k : ℝ≥0∞) := by simp
  rw [← hc, ENNReal.log_ofReal_of_pos (by exact_mod_cast hk)]

/-- A finite cover at a given scale works for every orbit length, so the
native limsup growth at every entourage is zero. -/
theorem native_entropy_zero_of_nonexpanding {X : Type*} [PseudoMetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X → X)
    (hT : ∀ x y, dist (T x) (T y) ≤ dist x y) :
    Dynamics.coverEntropy T Set.univ = 0 := by
  classical
  apply le_antisymm
  · change (⨆ U ∈ 𝓤 X, Dynamics.coverEntropyEntourage T Set.univ U) ≤ 0
    refine iSup₂_le fun U hU => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    let V : SetRel X X := {p | dist p.1 p.2 < ε / 2}
    let : V.IsSymm := ⟨fun x y h => by
      change dist y x < ε / 2
      change dist x y < ε / 2 at h
      simpa only [dist_comm] using h⟩
    have hVU : V ○ V ⊆ U := by
      intro p hp
      apply hεU
      change ∃ z, dist p.1 z < ε / 2 ∧ dist z p.2 < ε / 2 at hp
      obtain ⟨z, hz1, hz2⟩ := hp
      linarith [dist_triangle p.1 z p.2]
    obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_univ : IsCompact (Set.univ : Set X)).totallyBounded (ε / 2) (half_pos hε)
    let centers : Finset X := hs.toFinset
    have hc (x : X) : ∃ y ∈ centers, dist x y < ε / 2 := by
      have hx := hcover (Set.mem_univ x)
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨y, hs.mem_toFinset.mpr hy, hxy⟩
    have hn : 0 < centers.card := by
      obtain ⟨y, hy, _⟩ := hc (Classical.choice (inferInstance : Nonempty X))
      exact Finset.card_pos.mpr ⟨y, hy⟩
    have hdc (n : ℕ) : Dynamics.IsDynCoverOf T Set.univ V n centers := by
      intro x _
      obtain ⟨y, hy, hxy⟩ := hc x
      refine ⟨y, hy, ?_⟩
      rw [Dynamics.mem_dynEntourage]
      intro k _
      exact (iterate_nonexpanding T hT k x y).trans_lt hxy
    have hb (n : ℕ) : Dynamics.coverEntropyEntourage T Set.univ U ≤
        ((Real.log (centers.card : ℝ) / ((n : ℝ) + 1) : ℝ) : EReal) := by
      have h := (hdc (n + 1)).coverEntropyEntourage_le_log_card_div
        (Set.mapsTo_univ _ _) (by omega : n + 1 ≠ 0)
      apply (Dynamics.coverEntropyEntourage_antitone T Set.univ hVU).trans
      convert h using 1
      rw [ennreal_log_nat centers.card hn, ← EReal.coe_coe_eq_natCast (n + 1), ← EReal.coe_div]
      push_cast
      rfl
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
    exact ge_of_tendsto (EReal.tendsto_coe.mpr (tendsto_const_nhds.div_atTop ht))
      (Filter.Eventually.of_forall hb)
  · exact Dynamics.coverEntropy_nonneg T Set.univ_nonempty

/-- This is the library-native full topological entropy of the actual selfmap. -/
def entropy (a : Parameter) : EReal := Dynamics.coverEntropy (logistic a) Set.univ

theorem local_entropy_zero (a : Parameter)
    (ha : (a : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) : entropy a = 0 := by
  apply native_entropy_zero_of_nonexpanding
  intro x y
  have h := (local_contraction a ha).dist_le_mul x y
  have hd : 0 ≤ dist x y := dist_nonneg
  norm_num at h
  linarith

def leftParameter : Parameter := ⟨1 / 4, by constructor <;> norm_num⟩
def rightParameter : Parameter := ⟨1 / 2, by constructor <;> norm_num⟩

theorem endpoints_strict : leftParameter < rightParameter := by
  change (1 / 4 : ℝ) < 1 / 2
  norm_num

theorem parameter_interval_open : IsOpen (Set.Ioo leftParameter rightParameter) := isOpen_Ioo

theorem parameter_interval_nonempty : (Set.Ioo leftParameter rightParameter).Nonempty := by
  refine ⟨⟨3 / 8, by constructor <;> norm_num⟩, ?_, ?_⟩
  · change (1 / 4 : ℝ) < 3 / 8
    norm_num
  · change (3 / 8 : ℝ) < 1 / 2
    norm_num

theorem entropy_zero_on_interval {a : Parameter}
    (ha : a ∈ Set.Ioo leftParameter rightParameter) : entropy a = 0 := by
  apply local_entropy_zero
  exact ⟨le_of_lt ha.1, le_of_lt ha.2⟩

theorem entropy_monotone_interval : MonotoneOn entropy (Set.Ioo leftParameter rightParameter) := by
  intro a ha b hb _
  rw [entropy_zero_on_interval ha, entropy_zero_on_interval hb]

theorem entropy_antitone_interval : AntitoneOn entropy (Set.Ioo leftParameter rightParameter) := by
  intro a ha b hb _
  rw [entropy_zero_on_interval ha, entropy_zero_on_interval hb]

/-- The standard weak meaning of nowhere monotone: no nonempty open interval
admits either a nondecreasing or a nonincreasing restriction. -/
def NowhereMonotone (h : Parameter → EReal) : Prop :=
  ∀ a b : Parameter, a < b → (Set.Ioo a b).Nonempty →
    ¬ MonotoneOn h (Set.Ioo a b) ∧ ¬ AntitoneOn h (Set.Ioo a b)

theorem printed_nowhere_monotone_false : ¬ NowhereMonotone entropy := by
  intro h
  exact (h leftParameter rightParameter endpoints_strict parameter_interval_nonempty).1
    entropy_monotone_interval

end TLMC3363
