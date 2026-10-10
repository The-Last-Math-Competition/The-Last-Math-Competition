import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

noncomputable section

namespace CFRealization

open scoped BoundedContinuousFunction

abbrev Word := ℕ → Fin 2

def digit (w : Word) (n : ℕ) : ℤ := (w n).val + 1

abbrev TailInterval := Set.Icc (1 / 3 : ℝ) (3 / 4)
abbrev TailSpace := ℕ →ᵇ TailInterval

instance : Nonempty TailInterval := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
instance : Nonempty TailSpace := ⟨BoundedContinuousFunction.const ℕ (Classical.ofNonempty)⟩

lemma digit_bounds (w : Word) (n : ℕ) : 1 ≤ (digit w n : ℝ) ∧ (digit w n : ℝ) ≤ 2 := by
  have h := (w n).isLt
  simp only [digit, Int.cast_add, Int.cast_natCast, Int.cast_one]
  constructor
  · exact_mod_cast (show 1 ≤ (w n).val + 1 by omega)
  · exact_mod_cast (show (w n).val + 1 ≤ 2 by omega)

lemma reciprocal_mem (a : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (x : TailInterval) :
    1 / (a + x.val) ∈ Set.Icc (1 / 3 : ℝ) (3 / 4) := by
  have hx := x.property
  have hp : 0 < a + x.val := by linarith [hx.1]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [hx.2]
  · apply (div_le_iff₀ hp).2
    linarith [hx.1]

lemma interval_dist_le_one (x y : TailInterval) : dist x y ≤ 1 := by
  change |x.val - y.val| ≤ 1
  rw [abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

/-- Simultaneous inverse branches on every suffix of the digit word. -/
def transform (w : Word) (f : TailSpace) : TailSpace :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun n => ⟨1 / ((digit w n : ℝ) + (f (n + 1)).val),
      reciprocal_mem _ (digit_bounds w n) _⟩)
    1 (fun _ _ => interval_dist_le_one _ _)

lemma reciprocal_lipschitz (a : ℝ) (ha : 1 ≤ a) (x y : TailInterval) :
    |1 / (a + x.val) - 1 / (a + y.val)| ≤ (9 / 16 : ℝ) * |x.val - y.val| := by
  have hx : 4 / 3 ≤ a + x.val := by linarith [x.property.1]
  have hy : 4 / 3 ≤ a + y.val := by linarith [y.property.1]
  have hxpos : 0 < a + x.val := by linarith
  have hypos : 0 < a + y.val := by linarith
  have hp : 16 / 9 ≤ (a + x.val) * (a + y.val) := by nlinarith
  have heq : 1 / (a + x.val) - 1 / (a + y.val) =
      (y.val - x.val) / ((a + x.val) * (a + y.val)) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hxpos hypos), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hxpos hypos)).2
  nlinarith [abs_nonneg (x.val - y.val)]

/-- The lower tail bound gives the uniform contraction factor `9/16`. -/
lemma transform_contracting (w : Word) : ContractingWith (9 / 16) (transform w) := by
  constructor
  · change (9 / 16 : ℝ) < 1
    norm_num
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    apply BoundedContinuousFunction.dist_le (by positivity) |>.2
    intro n
    calc
      dist (transform w f n) (transform w g n) ≤
          (9 / 16 : ℝ) * dist (f (n + 1)) (g (n + 1)) :=
        reciprocal_lipschitz _ (digit_bounds w n).1 _ _
      _ ≤ (9 / 16 : ℝ) * dist f g :=
        mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _) (by norm_num)
      _ = _ := by norm_num

/-- Banach's theorem constructs all infinite continued-fraction tails at once. -/
noncomputable def tails (w : Word) : TailSpace :=
  (transform_contracting w).fixedPoint (transform w)

lemma tails_eq (w : Word) (n : ℕ) :
    (tails w n).val = 1 / ((digit w n : ℝ) + (tails w (n + 1)).val) := by
  have h := congrArg (fun f : TailSpace => (f n).val)
    (transform_contracting w).fixedPoint_isFixedPt
  exact h.symm

/-- The ordinary real represented by the infinite regular continued fraction
`[0; digit w 0, digit w 1, ...]`. Its tails are constructed analytically. -/
def realOfWord (w : Word) : ℝ := (tails w 0).val

/-- The complete quotients of the usual floor-and-invert algorithm. -/
def completeQuotient (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => (Int.fract (completeQuotient x n))⁻¹

/-- The ordinary partial quotients, including the integer part at index zero. -/
def partialQuotient (x : ℝ) (n : ℕ) : ℤ := ⌊completeQuotient x n⌋

lemma realOfWord_bounds (w : Word) :
    (1 / 3 : ℝ) ≤ realOfWord w ∧ realOfWord w ≤ 3 / 4 :=
  (tails w 0).property

lemma floor_realOfWord (w : Word) : ⌊realOfWord w⌋ = 0 := by
  apply Int.floor_eq_iff.mpr
  have h := realOfWord_bounds w
  constructor <;> norm_num <;> linarith

lemma floor_digit_add_tail (w : Word) (n : ℕ) :
    ⌊(digit w n : ℝ) + (tails w (n + 1)).val⌋ = digit w n := by
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith [(tails w (n + 1)).property.1,
    (tails w (n + 1)).property.2]

lemma tails_inv (w : Word) (n : ℕ) :
    (tails w n).val⁻¹ = (digit w n : ℝ) + (tails w (n + 1)).val := by
  rw [tails_eq w n, one_div, inv_inv]

lemma completeQuotient_succ (w : Word) (n : ℕ) :
    completeQuotient (realOfWord w) (n + 1) = (tails w n).val⁻¹ := by
  induction n with
  | zero =>
      simp only [completeQuotient, Int.fract, floor_realOfWord, Int.cast_zero, sub_zero]
      rfl
  | succ n ih =>
      rw [completeQuotient, ih, tails_inv, Int.fract, floor_digit_add_tail]
      congr 1
      ring

@[simp] lemma partialQuotient_zero (w : Word) : partialQuotient (realOfWord w) 0 = 0 :=
  floor_realOfWord w

lemma partialQuotient_succ (w : Word) (n : ℕ) :
    partialQuotient (realOfWord w) (n + 1) = digit w n := by
  unfold partialQuotient
  rw [completeQuotient_succ, tails_inv, floor_digit_add_tail]

/-- Positive remainders at every index ensure that this is an infinite regular
continued fraction, with no artificial continuation after termination. -/
lemma completeQuotient_fract_pos (w : Word) (n : ℕ) :
    0 < Int.fract (completeQuotient (realOfWord w) n) := by
  cases n with
  | zero =>
      simp only [completeQuotient, Int.fract, floor_realOfWord, Int.cast_zero, sub_zero]
      linarith [(realOfWord_bounds w).1]
  | succ n =>
      rw [completeQuotient_succ, tails_inv, Int.fract, floor_digit_add_tail]
      linarith [(tails w (n + 1)).property.1]

lemma realOfWord_injective : Function.Injective realOfWord := by
  intro w v h
  funext n
  apply Fin.ext
  have hd : digit w n = digit v n := by
    rw [← partialQuotient_succ w n, ← partialQuotient_succ v n, h]
  unfold digit at hd
  exact_mod_cast (add_right_cancel hd)

/-- Inverting a realization removes its zero integer part and shifts the actual
ordinary algorithm by one position. -/
lemma inverse_completeQuotient_shift (w : Word) (n : ℕ) :
    completeQuotient (realOfWord w)⁻¹ n = completeQuotient (realOfWord w) (n+1) := by
  induction n with
  | zero =>
    change (realOfWord w)⁻¹ = (Int.fract (realOfWord w))⁻¹
    rw [Int.fract, floor_realOfWord, Int.cast_zero, sub_zero]
  | succ n ih =>
    change (Int.fract (completeQuotient (realOfWord w)⁻¹ n))⁻¹ =
      (Int.fract (completeQuotient (realOfWord w) (n+1)))⁻¹
    rw [ih]

lemma inverse_partialQuotient (w : Word) (n : ℕ) :
    partialQuotient (realOfWord w)⁻¹ n = digit w n := by
  unfold partialQuotient
  rw [inverse_completeQuotient_shift]
  exact partialQuotient_succ w n

lemma inverse_completeQuotient_fract_pos (w : Word) (n : ℕ) :
    0 < Int.fract (completeQuotient (realOfWord w)⁻¹ n) := by
  rw [inverse_completeQuotient_shift]
  exact completeQuotient_fract_pos w (n+1)

end CFRealization
