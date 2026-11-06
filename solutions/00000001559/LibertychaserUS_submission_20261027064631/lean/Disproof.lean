import Mathlib

/-!
# Conjecture 00000001559: the 6-disk covering radius of the unit disk

Correspondence to the conjecture text (`r_6` is the minimal radius of six equal disks
covering the closed unit disk):

* `inDisk p` : `p` lies in the closed unit disk `{p | p.1^2 + p.2^2 ≤ 1}`.
* `Covers r C` : the six closed disks of radius `r` centred at `C 0, …, C 5` cover the
  unit disk, i.e. every point of the disk is at Euclidean distance `≤ r` from some centre.
  Distances are written out in coordinates, because the product metric on `ℝ × ℝ` is the
  sup-norm and must not be used here.
* `coverRadius` : the radii `r ≥ 0` for which some six-tuple of centres covers the disk
  (centres unrestricted, repetitions allowed).
* `coverRadiusInj` : the same, but the six centres must be pairwise distinct.
* `r6 = sInf coverRadius`, `r6Inj = sInf coverRadiusInj` : the covering radius `r_6`.

The conjecture asserts that `r_6` equals `(1+√3)/2·(√3−1)`. This expression is exactly `1`.
The file shows that `r_6 ≤ 3/4 < 1` (and the same for the distinct-centre variant), so the
asserted value is wrong under either reading of the definition.
-/

namespace TLMC1559

/-- The closed unit disk. -/
def inDisk (p : ℝ × ℝ) : Prop := p.1 ^ 2 + p.2 ^ 2 ≤ 1

/-- Six closed disks of radius `r`, centred at `C 0, …, C 5`, cover the closed unit disk. -/
def Covers (r : ℝ) (C : Fin 6 → ℝ × ℝ) : Prop :=
  ∀ p : ℝ × ℝ, inDisk p → ∃ i, (p.1 - (C i).1) ^ 2 + (p.2 - (C i).2) ^ 2 ≤ r ^ 2

/-- Radii `r ≥ 0` allowing a covering of the unit disk by six closed disks of radius `r`. -/
def coverRadius : Set ℝ :=
  {r | 0 ≤ r ∧ ∃ C : Fin 6 → ℝ × ℝ, Covers r C}

/-- Same as `coverRadius`, but the six centres are required to be pairwise distinct. -/
def coverRadiusInj : Set ℝ :=
  {r | 0 ≤ r ∧ ∃ C : Fin 6 → ℝ × ℝ, Function.Injective C ∧ Covers r C}

/-- The 6-disk covering radius `r_6` (infimum of the admissible radii). -/
noncomputable def r6 : ℝ := sInf coverRadius

/-- The 6-disk covering radius `r_6` with pairwise distinct centres. -/
noncomputable def r6Inj : ℝ := sInf coverRadiusInj

/-- Certificate: four corners `(±1/2, ±1/2)`, with two of them repeated. -/
noncomputable def C6 : Fin 6 → ℝ × ℝ :=
  ![(1/2, 1/2), (-1/2, 1/2), (-1/2, -1/2), (1/2, -1/2), (1/2, 1/2), (-1/2, -1/2)]

/-- Certificate with pairwise distinct centres: the four corners and two further points. -/
noncomputable def C6d : Fin 6 → ℝ × ℝ :=
  ![(1/2, 1/2), (-1/2, 1/2), (-1/2, -1/2), (1/2, -1/2), (0, 0), (3, 3)]

/-- Corner lemma: if `C 0, …, C 3` are the four corners, every point of the closed unit disk is
within squared distance `1/2` of one of the centres. The key facts are `x^2 ≤ |x|` and
`y^2 ≤ |y|`, which hold because `|x|, |y| ≤ 1`. -/
lemma cover_of_corners (C : Fin 6 → ℝ × ℝ)
    (h0 : C 0 = (1/2, 1/2)) (h1 : C 1 = (-1/2, 1/2))
    (h2 : C 2 = (-1/2, -1/2)) (h3 : C 3 = (1/2, -1/2))
    (x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1) :
    ∃ i, (x - (C i).1) ^ 2 + (y - (C i).2) ^ 2 ≤ 1 / 2 := by
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hx2 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have hy2 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · refine ⟨0, ?_⟩
    simp only [h0]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1), mul_nonneg hy (sub_nonneg.mpr hy1)]
  · refine ⟨3, ?_⟩
    simp only [h3]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1),
      mul_nonneg (neg_nonneg.mpr hy) (by linarith : (0:ℝ) ≤ 1 + y)]
  · refine ⟨1, ?_⟩
    simp only [h1]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (by linarith : (0:ℝ) ≤ 1 + x),
      mul_nonneg hy (sub_nonneg.mpr hy1)]
  · refine ⟨2, ?_⟩
    simp only [h2]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (by linarith : (0:ℝ) ≤ 1 + x),
      mul_nonneg (neg_nonneg.mpr hy) (by linarith : (0:ℝ) ≤ 1 + y)]

/-- `C6` covers the unit disk with radius `3/4`. -/
lemma covers_C6 : Covers (3/4) C6 := by
  intro p hp
  obtain ⟨i, hi⟩ := cover_of_corners C6 rfl rfl rfl rfl p.1 p.2 hp
  exact ⟨i, le_trans hi (by norm_num)⟩

/-- `C6d` covers the unit disk with radius `3/4`. -/
lemma covers_C6d : Covers (3/4) C6d := by
  intro p hp
  obtain ⟨i, hi⟩ := cover_of_corners C6d rfl rfl rfl rfl p.1 p.2 hp
  exact ⟨i, le_trans hi (by norm_num)⟩

/-- `C6d` consists of pairwise distinct points. -/
lemma C6d_injective : Function.Injective C6d := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | (norm_num [C6d] at hab)

lemma mem_coverRadius_34 : (3/4 : ℝ) ∈ coverRadius :=
  ⟨by norm_num, C6, covers_C6⟩

lemma mem_coverRadiusInj_34 : (3/4 : ℝ) ∈ coverRadiusInj :=
  ⟨by norm_num, C6d, C6d_injective, covers_C6d⟩

lemma bdd_coverRadius : BddBelow coverRadius :=
  ⟨0, fun _ hr => hr.1⟩

lemma bdd_coverRadiusInj : BddBelow coverRadiusInj :=
  ⟨0, fun _ hr => hr.1⟩

/-- `r_6 ≤ 3/4`. -/
lemma r6_le : r6 ≤ 3/4 :=
  csInf_le bdd_coverRadius mem_coverRadius_34

/-- `r_6` with distinct centres satisfies `r_6 ≤ 3/4`. -/
lemma r6Inj_le : r6Inj ≤ 3/4 :=
  csInf_le bdd_coverRadiusInj mem_coverRadiusInj_34

/-- The conjectured expression `(1+√3)/2·(√3−1)` is exactly `1`. -/
lemma conjectured_expr_eq_one : (1 + Real.sqrt 3) / 2 * (Real.sqrt 3 - 1) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (1/2 : ℝ) * h3

/-- The conjecture fails: the value `(1+√3)/2·(√3−1)` is not `r_6`, under either the
unrestricted-centre definition or the distinct-centre definition. -/
theorem conjecture_00000001559_fails :
    ¬ (r6 = (1 + Real.sqrt 3) / 2 * (Real.sqrt 3 - 1)) ∧
    ¬ (r6Inj = (1 + Real.sqrt 3) / 2 * (Real.sqrt 3 - 1)) := by
  constructor
  · intro h
    have h1 := r6_le
    rw [h, conjectured_expr_eq_one] at h1
    norm_num at h1
  · intro h
    have h1 := r6Inj_le
    rw [h, conjectured_expr_eq_one] at h1
    norm_num at h1

end TLMC1559

#print axioms TLMC1559.conjecture_00000001559_fails
