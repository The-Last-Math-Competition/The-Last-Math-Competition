import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace TLMC358
noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 24)
abbrev BinaryCode := Set (Fin 24 → ZMod 2)

/-- Wilson's complete three-condition integer-coordinate recipe, with code as input.
It is not asserted that an arbitrary input code is the extended Golay code. -/
def coordinateRecipe (C : BinaryCode) (z : Fin 24 → ℤ) : Prop :=
  ∃ m : ℤ, (∀ i, z i % 2 = m % 2) ∧
    (fun i => (((z i-m)/2 : ℤ) : ZMod 2)) ∈ C ∧
    (∑ i, z i) % 8 = (4*m) % 8

def coordinatePoint (a : ℝ) (z : Fin 24 → ℤ) : E :=
  WithLp.toLp 2 (fun i => a * (z i : ℝ))

def coordinateSet (a : ℝ) (C : BinaryCode) : Set E :=
  coordinatePoint a '' {z | coordinateRecipe C z}

def countedPoints (a : ℝ) (C : BinaryCode) (B : Set E) (t : ℝ) : Set E :=
  coordinateSet a C ∩ (t • B)

def pointCount (a : ℝ) (C : BinaryCode) (B : Set E) (t : ℝ) : ℕ :=
  (countedPoints a C B t).ncard

def integerBox (N : ℕ) : Finset (Fin 24 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(N:ℤ)) N)

theorem integerBox_card (N : ℕ) : (integerBox N).card = (2*N+1)^24 := by
  simp only [integerBox,Fintype.card_piFinset,Finset.prod_const]
  congr 1
  rw [Int.card_Icc]
  omega

theorem coordinatePoint_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (coordinatePoint a) := by
  intro z w h
  funext i
  have hh := congrArg (fun v : E => v i) h
  change a*(z i:ℝ)=a*(w i:ℝ) at hh
  exact_mod_cast (mul_left_cancel₀ ha.ne' hh)

theorem coordinate_bound {a R : ℝ} (ha : 0 < a) (z : Fin 24 → ℤ)
    (hz : ‖coordinatePoint a z‖ ≤ R) : z ∈ integerBox (Nat.ceil (R/a)) := by
  rw [integerBox,Fintype.mem_piFinset]
  intro i
  have hnorm := (PiLp.norm_apply_le (coordinatePoint a z) i).trans hz
  change ‖a*(z i:ℝ)‖ ≤ R at hnorm
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos ha,Real.norm_eq_abs] at hnorm
  have h := (le_div_iff₀ ha).2 (by nlinarith : |(z i:ℝ)| *a ≤ R)
  have h' := h.trans (Nat.le_ceil (R/a))
  have hl := (abs_le.mp h').1
  have hu := (abs_le.mp h').2
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩

theorem countedPoints_subset_box {a R : ℝ} (ha : 0 < a) (_hR : 0 < R)
    (C : BinaryCode) (B : Set E) (hB : ∀x∈B, ‖x‖ ≤ R) (t : ℝ) :
    countedPoints a C B t ⊆ coordinatePoint a ''
      (integerBox (Nat.ceil (|t| *R/a)) : Set (Fin 24 → ℤ)) := by
  rintro x ⟨⟨z,hz,rfl⟩,hx⟩
  obtain ⟨b,hb,hx⟩ := hx
  refine ⟨z,coordinate_bound ha z ?_,rfl⟩
  rw [←hx,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB b hb) (abs_nonneg t)

theorem countedPoints_finite {a : ℝ} (ha : 0 < a) (C : BinaryCode)
    (B : Set E) (hB : Bornology.IsBounded B) (t : ℝ) :
    (countedPoints a C B t).Finite := by
  obtain ⟨R,hR,hBound⟩ := hB.exists_pos_norm_le
  exact ((integerBox (Nat.ceil (|t| *R/a))).finite_toSet.image _).subset
    (countedPoints_subset_box ha hR C B hBound t)

theorem pointCount_box_bound {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (C : BinaryCode) (B : Set E) (hB : ∀x∈B, ‖x‖ ≤ R) (t : ℝ) :
    pointCount a C B t ≤ (2*Nat.ceil (|t| *R/a)+1)^24 := by
  have hsub := countedPoints_subset_box ha hR C B hB t
  calc
    pointCount a C B t ≤ (coordinatePoint a ''
        (integerBox (Nat.ceil (|t| *R/a)) : Set (Fin 24 → ℤ))).ncard :=
      Set.ncard_le_ncard hsub ((integerBox _).finite_toSet.image _)
    _ ≤ ((integerBox (Nat.ceil (|t| *R/a))) : Set (Fin 24 → ℤ)).ncard :=
      Set.ncard_image_le (integerBox _).finite_toSet
    _ = (2*Nat.ceil (|t| *R/a)+1)^24 := by simp [integerBox_card]

theorem pointCount_polynomial_bound {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (C : BinaryCode) (B : Set E) (hB : ∀x∈B, ‖x‖ ≤ R)
    {t : ℝ} (ht : 1 ≤ t) :
    (pointCount a C B t : ℝ) ≤ (2*R/a+3)^24 * t^24 := by
  have hc := pointCount_box_bound ha hR C B hB t
  have ht0 : 0 ≤ t := by linarith
  have he : (Nat.ceil (t*R/a):ℝ) < t*R/a+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hb : ((2*Nat.ceil (|t| *R/a)+1:ℕ):ℝ) ≤ (2*R/a+3)*t := by
    rw [abs_of_nonneg ht0]
    push_cast
    calc
      2*(Nat.ceil (t*R/a):ℝ)+1 ≤ 2*(t*R/a+1)+1 := by linarith only [he]
      _ = (2*R/a)*t+3 := by ring
      _ ≤ (2*R/a)*t+3*t := by linarith only [ht]
      _ = (2*R/a+3)*t := by ring
  calc
    (pointCount a C B t:ℝ) ≤ ((2*Nat.ceil (|t| *R/a)+1:ℕ):ℝ)^24 := by exact_mod_cast hc
    _ ≤ ((2*R/a+3)*t)^24 := by gcongr
    _ = (2*R/a+3)^24*t^24 := mul_pow _ _ _

def normalizedCount (a : ℝ) (C : BinaryCode) (B : Set E) (t : ℝ) : ℝ :=
  (pointCount a C B t:ℝ) / (volume (t • B)).toReal

theorem scaled_volume (B : Set E) {t : ℝ} (ht : 0 ≤ t) :
    (volume (t • B)).toReal = t^24 * (volume B).toReal := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume ht]
  simp [E,ENNReal.toReal_mul,ENNReal.toReal_ofReal,ht,finrank_euclideanSpace]

/-- Cofinal lower amplitude: every cutoff admits a later deviation of the stated size. -/
def CofinalAmplitude (f : ℝ → ℝ) (center c : ℝ) : Prop :=
  ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c*t^11 ≤ |f t-center|


theorem normalizedCount_bounded {a : ℝ} (ha : 0 < a) (C : BinaryCode)
    (B : Set E) (hB : Bornology.IsBounded B)
    (hv0 : 0 < volume B) (hvfin : volume B ≠ ∞) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ normalizedCount a C B t ∧ normalizedCount a C B t ≤ M := by
  obtain ⟨R,hR,hBound⟩ := hB.exists_pos_norm_le
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos (ne_of_gt hv0) hvfin
  let A : ℝ := (2*R/a+3)^24
  refine ⟨A/(volume B).toReal,by dsimp [A]; positivity,?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hden : 0 < t^24*(volume B).toReal := mul_pos (pow_pos ht0 _) hv
  unfold normalizedCount
  rw [scaled_volume B ht0.le]
  refine ⟨div_nonneg (Nat.cast_nonneg _) hden.le,?_⟩
  apply (div_le_iff₀ hden).2
  calc
    (pointCount a C B t:ℝ) ≤ A*t^24 := pointCount_polynomial_bound ha hR C B hBound ht
    _ = A/(volume B).toReal * (t^24*(volume B).toReal) := by field_simp

theorem no_normalized_power_amplitude {a : ℝ} (ha : 0 < a) (C : BinaryCode)
    (B : Set E) (hB : Bornology.IsBounded B)
    (hv0 : 0 < volume B) (hvfin : volume B ≠ ∞)
    (center c : ℝ) (hc : 0 < c) :
    ¬ CofinalAmplitude (normalizedCount a C B) center c := by
  obtain ⟨M,hM,hbound⟩ := normalizedCount_bounded ha C B hB hv0 hvfin
  intro h
  obtain ⟨t,ht,hamp⟩ := h (max 1 ((M+|center|)/c+1))
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hb := hbound t ht1
  have habs : |normalizedCount a C B t-center| ≤ M+|center| := by
    calc
      |normalizedCount a C B t-center| ≤ |normalizedCount a C B t|+|center| := abs_sub _ _
      _ ≤ M+|center| := by rw [abs_of_nonneg hb.1]; exact add_le_add hb.2 le_rfl
  have hlt : (M+|center|)/c < t :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans ht)
  have hgap : M+|center| < c*t := by
    have hh := (div_lt_iff₀ hc).1 hlt
    nlinarith
  have hp : t ≤ t^11 := by
    calc
      t = t*1 := by ring
      _ ≤ t*t^10 := mul_le_mul_of_nonneg_left (one_le_pow₀ ht1) (by linarith)
      _ = t^11 := by ring
  have hcp := mul_le_mul_of_nonneg_left hp hc.le
  linarith


/-- Wilson's integer coordinates with the standard norm divided by 8. -/
def standardScale : ℝ := 1 / Real.sqrt 8

def unitBody : Set E := Metric.closedBall 0 1

theorem standardScale_pos : 0 < standardScale := by unfold standardScale; positivity

theorem unitBody_measurable : MeasurableSet unitBody := Metric.isClosed_closedBall.measurableSet

theorem unitBody_bounded : Bornology.IsBounded unitBody := Metric.isBounded_closedBall

theorem unitBody_volume_pos : 0 < volume unitBody := by
  exact Metric.measure_closedBall_pos volume (0:E) zero_lt_one

theorem unitBody_volume_finite : volume unitBody ≠ ∞ := measure_closedBall_lt_top.ne

theorem standard_coordinates_no_amplitude (C : BinaryCode) (center c : ℝ) (hc : 0 < c) :
    ¬ CofinalAmplitude (normalizedCount standardScale C unitBody) center c :=
  no_normalized_power_amplitude standardScale_pos C unitBody unitBody_bounded
    unitBody_volume_pos unitBody_volume_finite center c hc

end
end TLMC358
