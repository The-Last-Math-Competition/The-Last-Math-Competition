import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Definability
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Set Metric FirstOrder FirstOrder.Language
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace TLMC8031

abbrev Snow := Metric.Snowflaking ℝ (1 / 2) (by norm_num) (by norm_num)

def point (x : ℝ) : Snow := Metric.Snowflaking.toSnowflaking x

theorem point_injective : Function.Injective point := by
  intro x y h
  exact congrArg Metric.Snowflaking.val h

theorem point_surjective : Function.Surjective point := by
  intro x
  exact ⟨x.val, rfl⟩

theorem dist_point (x y : ℝ) : dist (point x) (point y) = Real.sqrt |x - y| := by
  simp [point, Real.dist_eq, Real.sqrt_eq_rpow]

theorem dist_sq (x y : Snow) : (dist x y) ^ 2 = |x.val - y.val| := by
  change (dist (point x.val) (point y.val)) ^ 2 = _
  rw [dist_point, Real.sq_sqrt (abs_nonneg _)]

theorem dist_le_iff_sq (x y : Snow) {r : ℝ} (hr : 0 ≤ r) :
    dist x y ≤ r ↔ |x.val - y.val| ≤ r ^ 2 := by
  rw [← dist_sq]
  exact (sq_le_sq₀ dist_nonneg hr).symm

theorem le_dist_iff_sq (x y : Snow) {r : ℝ} (hr : 0 ≤ r) :
    r ≤ dist x y ↔ r ^ 2 ≤ |x.val - y.val| := by
  rw [← dist_sq]
  exact (sq_le_sq₀ hr dist_nonneg).symm

/-- The standard uniform finite separated-set formulation of an Assouad exponent.
The diameter bound and separation are genuine distances; 0 < r ≤ D. -/
def UpperExponent (s : ℝ) : Prop :=
  0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D r : ℝ), 0 < r → r ≤ D →
    ∀ S : Finset Snow,
      (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) →
      (S : Set Snow).Pairwise (fun x y => r ≤ dist x y) →
      (S.card : ℝ) ≤ C * (D / r) ^ s

def assouadDimension : ℝ := sInf {s : ℝ | UpperExponent s}

theorem separated_card_bound (D r : ℝ) (hr : 0 < r) (hrD : r ≤ D)
    (S : Finset Snow) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hsep : (S : Set Snow).Pairwise (fun x y => r ≤ dist x y)) :
    (S.card : ℝ) ≤ 3 * (D / r) ^ 2 := by
  classical
  have hD : 0 < D := lt_of_lt_of_le hr hrD
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  by_cases hS : S = ∅
  · simp only [hS, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  let a : ℝ := x0.val - D ^ 2
  let L : ℝ := 2 * D ^ 2 / r ^ 2
  let code : Snow → ℕ := fun x => ⌊(x.val - a) / r ^ 2⌋₊
  have hcoord (x : Snow) (hx : x ∈ S) : 0 ≤ (x.val - a) / r ^ 2 ∧
      (x.val - a) / r ^ 2 ≤ L := by
    have hh := (dist_le_iff_sq x x0 hD.le).mp (hdiam x hx x0 hx0)
    have hb := abs_le.mp hh
    constructor
    · apply div_nonneg _ hr2.le
      dsimp [a]
      linarith
    · apply (div_le_div_iff_of_pos_right hr2).mpr
      dsimp [a, L]
      linarith
  have hmaps : Set.MapsTo code (S : Set Snow) (Finset.range (⌊L⌋₊ + 1)) := by
    intro x hx
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (hcoord x hx).2)
  have hinj : Set.InjOn code (S : Set Snow) := by
    intro x hx y hy hxy
    by_contra hne
    have hxlo := Nat.floor_le (hcoord x hx).1
    have hylo := Nat.floor_le (hcoord y hy).1
    have hxhi := Nat.lt_floor_add_one ((x.val - a) / r ^ 2)
    have hyhi := Nat.lt_floor_add_one ((y.val - a) / r ^ 2)
    change ⌊(x.val - a) / r ^ 2⌋₊ = ⌊(y.val - a) / r ^ 2⌋₊ at hxy
    have h1 : (x.val - y.val) / r ^ 2 < 1 := by
      rw [← sub_sub_sub_cancel_right x.val y.val a, sub_div]
      rw [hxy] at hxlo hxhi
      linarith
    have h2 : (y.val - x.val) / r ^ 2 < 1 := by
      rw [← sub_sub_sub_cancel_right y.val x.val a, sub_div]
      rw [hxy] at hxlo hxhi
      linarith
    have h1' := (div_lt_iff₀ hr2).mp h1
    have h2' := (div_lt_iff₀ hr2).mp h2
    have habs : |x.val - y.val| < r ^ 2 := by
      apply abs_lt.mpr
      constructor <;> linarith
    exact (not_lt_of_ge ((le_dist_iff_sq x y hr.le).mp (hsep hx hy hne))) habs
  have hc : S.card ≤ ⌊L⌋₊ + 1 := by
    simpa using Finset.card_le_card_of_injOn code hmaps hinj
  have hL : 0 ≤ L := by positivity
  have hcR : (S.card : ℝ) ≤ (⌊L⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  have hf := Nat.floor_le hL
  have hCL : (S.card : ℝ) ≤ L + 1 := by linarith
  have hratio : 1 ≤ D / r := (le_div_iff₀ hr).mpr (by simpa using hrD)
  have hformula : L = 2 * (D / r) ^ 2 := by
    dsimp [L]
    ring
  rw [hformula] at hCL
  nlinarith [sq_nonneg (D / r - 1)]

theorem upper_two : UpperExponent 2 := by
  refine ⟨by norm_num, 3, by norm_num, ?_⟩
  intro D r hr hrD S hdiam hsep
  simpa only [Real.rpow_two] using separated_card_bound D r hr hrD S hdiam hsep

theorem exponent_set_nonempty : {s : ℝ | UpperExponent s}.Nonempty := ⟨2, upper_two⟩

theorem exponent_set_bddBelow : BddBelow {s : ℝ | UpperExponent s} :=
  ⟨0, fun _ hs => hs.1⟩

theorem upper_mono {s t : ℝ} (hs : UpperExponent s) (hst : s ≤ t) : UpperExponent t := by
  obtain ⟨hs0, C, hC, hbound⟩ := hs
  refine ⟨le_trans hs0 hst, C, hC, ?_⟩
  intro D r hr hrD S hdiam hsep
  apply le_trans (hbound D r hr hrD S hdiam hsep)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le ((le_div_iff₀ hr).mpr (by simpa using hrD)) hst

def grid (N : ℕ) : Finset Snow := by
  classical
  exact (Finset.range (N ^ 4)).image (fun j : ℕ => point ((j : ℝ) / (N : ℝ) ^ 4))

theorem grid_card (N : ℕ) (hN : 0 < N) : (grid N).card = N ^ 4 := by
  classical
  rw [grid, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j hij
    have h := point_injective hij
    have hz : (N : ℝ) ^ 4 ≠ 0 := by positivity
    have h' : (i : ℝ) = j := (div_left_inj' hz).mp h
    exact_mod_cast h'

theorem grid_coordinate (N : ℕ) (hN : 0 < N) (x : Snow) (hx : x ∈ grid N) :
    0 ≤ x.val ∧ x.val ≤ 1 := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hj' := Finset.mem_range.mp hj
  change 0 ≤ (j : ℝ) / (N : ℝ) ^ 4 ∧ (j : ℝ) / (N : ℝ) ^ 4 ≤ 1
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.le_of_lt hj'

theorem grid_diameter (N : ℕ) (hN : 0 < N) :
    ∀ x ∈ grid N, ∀ y ∈ grid N, dist x y ≤ 1 := by
  intro x hx y hy
  apply (dist_le_iff_sq x y (by norm_num)).mpr
  have hxx := grid_coordinate N hN x hx
  have hyy := grid_coordinate N hN y hy
  apply abs_le.mpr
  constructor <;> norm_num <;> linarith

theorem grid_separated (N : ℕ) (hN : 0 < N) :
    (grid N : Set Snow).Pairwise (fun x y => 1 / (N : ℝ) ^ 2 ≤ dist x y) := by
  classical
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hij : i ≠ j := by intro h; subst j; exact hxy rfl
  apply (le_dist_iff_sq _ _ (by positivity)).mpr
  change (1 / (N : ℝ) ^ 2) ^ 2 ≤ |(i : ℝ) / (N : ℝ) ^ 4 - (j : ℝ) / (N : ℝ) ^ 4|
  have habs : 1 ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast h))]
      have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
    · rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast h))]
      have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
  have hp : 0 < (N : ℝ) ^ 4 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hp]
  have hpow : (1 / (N : ℝ) ^ 2) ^ 2 = 1 / (N : ℝ) ^ 4 := by ring
  rw [hpow]
  exact (div_le_div_iff_of_pos_right hp).mpr habs

theorem not_upper_three_halves : ¬ UpperExponent (3 / 2) := by
  rintro ⟨_, C, hC, hbound⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 1)
  have hCN : C < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : 0 < N := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hN1)
  have hnR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hr : 0 < 1 / (N : ℝ) ^ 2 := by positivity
  have hrD : 1 / (N : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hh := hbound 1 (1 / (N : ℝ) ^ 2) hr hrD (grid N)
    (grid_diameter N hNpos) (grid_separated N hNpos)
  rw [grid_card N hNpos] at hh
  have hratio : 1 / (1 / (N : ℝ) ^ 2) = (N : ℝ) ^ 2 := by field_simp
  have hpow : ((N : ℝ) ^ 2) ^ (3 / 2 : ℝ) = (N : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  rw [hratio, hpow] at hh
  have hh' : (N : ℝ) ^ 4 ≤ C * (N : ℝ) ^ 3 := by exact_mod_cast hh
  have hstrict := mul_lt_mul_of_pos_right hCN (pow_pos hnR 3)
  nlinarith [show (N : ℝ) ^ 4 = (N : ℝ) * (N : ℝ) ^ 3 by ring]

theorem exponent_lower {s : ℝ} (hs : UpperExponent s) : (3 / 2 : ℝ) < s := by
  by_contra h
  exact not_upper_three_halves (upper_mono hs (le_of_not_gt h))

theorem dimension_lower : (3 / 2 : ℝ) ≤ assouadDimension := by
  apply le_csInf exponent_set_nonempty
  intro s hs
  exact (exponent_lower hs).le

theorem dimension_upper : assouadDimension ≤ 2 :=
  csInf_le exponent_set_bddBelow upper_two

theorem dimension_exceeds_one : 1 < assouadDimension := by
  linarith [dimension_lower]

theorem dimension_not_in_claimed_range : assouadDimension ∉ Icc (0 : ℝ) 1 := by
  intro h
  exact (not_le_of_gt dimension_exceeds_one) h.2

instance realRingLanguage : FirstOrder.Ring.CompatibleRing ℝ :=
  FirstOrder.Ring.compatibleRingOfRing ℝ

/-- A formula over the ordinary ring language, with three free coordinates and
one existential square witness. No square-root or order symbol is assumed. -/
def metricGraphBody : Language.ring.BoundedFormula (Fin 3) 1 :=
  let x : Language.ring.Term (Fin 3 ⊕ Fin 1) := .var (.inl 0)
  let y : Language.ring.Term (Fin 3 ⊕ Fin 1) := .var (.inl 1)
  let z : Language.ring.Term (Fin 3 ⊕ Fin 1) := .var (.inl 2)
  let t : Language.ring.Term (Fin 3 ⊕ Fin 1) := .var (.inr 0)
  z.bdEqual (t * t) ⊓
    ((z * z).bdEqual (x + -y) ⊔ (z * z).bdEqual (y + -x))

def metricGraphFormula : Language.ring.Formula (Fin 3) := metricGraphBody.ex

theorem sqrt_abs_characterization (x y z : ℝ) :
    Real.sqrt |x - y| = z ↔
      ∃ t : ℝ, z = t * t ∧ (z * z = x - y ∨ z * z = y - x) := by
  constructor
  · intro h
    have hz : 0 ≤ z := h ▸ Real.sqrt_nonneg _
    refine ⟨Real.sqrt z, ?_, ?_⟩
    · simpa [pow_two] using (Real.sq_sqrt hz).symm
    · have he : z * z = |x - y| := by
        rw [← pow_two, ← h, Real.sq_sqrt (abs_nonneg _)]
      rcases le_total 0 (x - y) with hp | hn
      · exact Or.inl (by simpa [abs_of_nonneg hp] using he)
      · apply Or.inr
        rw [abs_of_nonpos hn] at he
        linarith
  · rintro ⟨t, ht, he⟩
    have hz : 0 ≤ z := by rw [ht]; exact mul_self_nonneg t
    have habs : |x - y| = z * z := by
      rcases he with h | h
      · have hp : 0 ≤ x - y := by nlinarith [sq_nonneg z]
        rw [abs_of_nonneg hp]
        exact h.symm
      · have hn : x - y ≤ 0 := by nlinarith [sq_nonneg z]
        rw [abs_of_nonpos hn]
        linarith
    rw [habs]
    simpa [pow_two, abs_of_nonneg hz] using Real.sqrt_sq_eq_abs z

theorem metricGraphFormula_realize (v : Fin 3 → ℝ) :
    metricGraphFormula.Realize v ↔ dist (point (v 0)) (point (v 1)) = v 2 := by
  have h : metricGraphFormula.Realize v ↔
      ∃ t : ℝ, v 2 = t * t ∧ (v 2 * v 2 = v 0 - v 1 ∨ v 2 * v 2 = v 1 - v 0) := by
    simp [metricGraphFormula, metricGraphBody, Formula.Realize, Fin.snoc, sub_eq_add_neg]
  rw [h, dist_point]
  exact (sqrt_abs_characterization (v 0) (v 1) (v 2)).symm

def distanceGraph : Set (Fin 3 → ℝ) :=
  {v | dist (point (v 0)) (point (v 1)) = v 2}

theorem distanceGraph_definable : (∅ : Set ℝ).Definable Language.ring distanceGraph := by
  apply Set.empty_definable_iff.mpr
  refine ⟨metricGraphFormula, ?_⟩
  ext v
  exact (metricGraphFormula_realize v).symm

theorem real_line_definable : (∅ : Set ℝ).Definable Language.ring (univ : Set (Fin 1 → ℝ)) :=
  Set.definable_univ

theorem concrete_counterexample :
    (∅ : Set ℝ).Definable Language.ring (univ : Set (Fin 1 → ℝ)) ∧
    (∅ : Set ℝ).Definable Language.ring distanceGraph ∧
    {s : ℝ | UpperExponent s}.Nonempty ∧ BddBelow {s : ℝ | UpperExponent s} ∧
    (3 / 2 : ℝ) ≤ assouadDimension ∧ assouadDimension ≤ 2 ∧
    assouadDimension ∉ Icc (0 : ℝ) 1 :=
  ⟨real_line_definable, distanceGraph_definable, exponent_set_nonempty,
    exponent_set_bddBelow, dimension_lower, dimension_upper, dimension_not_in_claimed_range⟩

end TLMC8031
