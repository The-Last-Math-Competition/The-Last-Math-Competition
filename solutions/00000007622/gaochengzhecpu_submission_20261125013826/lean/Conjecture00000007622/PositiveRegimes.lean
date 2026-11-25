/-
  Conjecture 00000007622 — Positive Restricted-Truth Regimes & Non-Vacuity Witnesses
  Proves the three restricted regimes that motivate the conjecture and demonstrate
  non-vacuity of all definitions:
  - Theorem P1 (`vec_zeroDivisor_iff_isotropic` / `vecMinus_zeroDivisor_iff_isotropic`):
    For grade-1 vectors `v ∈ V` in ANY dimension `n` and under BOTH sign conventions,
    `v` is a zero divisor in `Cl(V, Q)` if and only if `v` is an isotropic vector.
  - Theorem P2 (`dim1_zeroDivisor_iff_norm_zero`, `dim2_zeroDivisor_iff_norm_zero`,
    `cl01_division_algebra`, `cl02_division_algebra`):
    When `dim V ≤ 2`, `x * conj x` is ALWAYS scalar and vanishes iff `x ≠ 0` is a
    zero divisor; over any ordered field (ℚ, ℝ), `Cl_{0,1}` and `Cl_{0,2}` are
    division algebras with zero zero-divisors.
  - Theorem P3 (`cl11_spinor_minimal_left_ideal`):
    In the split plane `Cl_{1,1}(F) ≅ M₂(F)`, the primitive idempotent
    `f = (1 + e₀)/2` generates a minimal left ideal `S = Cl_{1,1}(F)·f` consisting
    of zero divisors (plus 0) that is a simple faithful spinor module.
-/

import Conjecture00000007622.Clifford

namespace Conjecture00000007622

open Clifford

/-! ### Theorem P1: Grade-1 Vectors Are Zero Divisors Iff Isotropic -/

section GradeOneCriterion
variable {F : Type} [FieldOps F]

theorem embed_ne_zero_iff {sig : List F} (v : Vec F sig) :
    embed v ≠ 0 ↔ v ≠ Vec.zeroVec sig := by
  constructor
  · intro he hv
    rw [hv, embed_zero] at he
    exact he rfl
  · intro hv he
    rw [← embed_zero sig] at he
    exact hv (embed_injective he)

theorem embed_isUnit_of_quadForm_ne_zero {sig : List F} {v : Vec F sig}
    (hq : Vec.quadForm v ≠ 0) : IsUnitElem (embed v) := by
  refine ⟨smul (Vec.quadForm v)⁻¹ (embed v), ?_, ?_⟩
  · rw [mul_smul, embed_sq, smul_scalar, f_inv_mul_cancel hq, scalar_one]
  · rw [smul_mul, embed_sq, smul_scalar, f_inv_mul_cancel hq, scalar_one]

/-- Theorem P1 (+Q convention): A vector `v ∈ V` embeds as a left zero divisor
    in `Cl⁺(V, Q)` if and only if `v` is a nonzero isotropic vector (`Q(v) = 0`). -/
theorem vec_leftZeroDivisor_iff_isotropic {sig : List F} (v : Vec F sig) :
    IsLeftZeroDivisor (embed v) ↔ IsIsotropic v := by
  constructor
  · intro hzd
    have hv : v ≠ Vec.zeroVec sig := (embed_ne_zero_iff v).mp hzd.1
    refine ⟨hv, ?_⟩
    exact Classical.byContradiction fun hq =>
      unit_not_leftZeroDivisor (embed_isUnit_of_quadForm_ne_zero hq) hzd
  · intro ⟨hv, hq⟩
    have he : embed v ≠ 0 := (embed_ne_zero_iff v).mpr hv
    refine ⟨he, embed v, he, ?_⟩
    rw [embed_sq, hq, scalar_zero]

/-- Theorem P1 (+Q convention, two-sided): `embed v` is a zero divisor iff isotropic. -/
theorem vec_zeroDivisor_iff_isotropic {sig : List F} (v : Vec F sig) :
    IsZeroDivisor (embed v) ↔ IsIsotropic v := by
  constructor
  · intro hzd
    have hv : v ≠ Vec.zeroVec sig := (embed_ne_zero_iff v).mp hzd.1
    refine ⟨hv, ?_⟩
    exact Classical.byContradiction fun hq =>
      unit_not_zeroDivisor (embed_isUnit_of_quadForm_ne_zero hq) hzd
  · intro hiso
    exact leftZD_to_ZD ((vec_leftZeroDivisor_iff_isotropic v).mpr hiso)

/-- Theorem P1 (-Q convention): `embedMinus v` is a zero divisor in `Cl⁻(V, Q)`
    if and only if `v` is an isotropic vector of `(V, Q)`. -/
theorem vecMinus_zeroDivisor_iff_isotropic {sig : List F} (v : Vec F sig) :
    IsZeroDivisor (embedMinus v) ↔ IsIsotropic v := by
  unfold embedMinus
  rw [vec_zeroDivisor_iff_isotropic]
  unfold IsIsotropic
  constructor
  · intro ⟨hne, hq⟩
    refine ⟨fun hv => hne ((Vec.toNeg_eq_zero_iff v).mpr hv), ?_⟩
    rw [Vec.quadForm_toNeg, r_neg_eq_zero] at hq
    exact hq
  · intro ⟨hv, hq⟩
    refine ⟨fun hne => hv ((Vec.toNeg_eq_zero_iff v).mp hne), ?_⟩
    rw [Vec.quadForm_toNeg, hq, r_neg_zero]

end GradeOneCriterion

/-! ### Theorem P2: Low-Dimensional Norm Criterion (`dim V ≤ 2`) & Division Algebras -/

section LowDimensionNorm

theorem scalar_smul_one {R : Type} [CommRingOps R] (sig : List R) (r : R) :
    smul r (1 : Clifford R sig) = scalar sig r := by
  rw [← scalar_mul, mul_one]

theorem scalar_mul_scalar {R : Type} [CommRingOps R] (sig : List R) (r s : R) :
    scalar sig r * scalar sig s = scalar sig (r * s) := by
  rw [scalar_mul, smul_scalar]

/-- In dimension 0 (`sig = []`), `x * conj x` and `conj x * x` are scalar. -/
theorem dim0_norm_scalar {R : Type} [CommRingOps R] (x : Clifford R []) :
    x * conj x = scalar [] (cliffordScalarNorm x) ∧
    conj x * x = scalar [] (cliffordScalarNorm x) := by
  match x with
  | .base _ => exact ⟨rfl, rfl⟩

/-- `Clifford R [c]` (dimension 1) is commutative. -/
theorem dim1_mul_comm {R : Type} [CommRingOps R] {c : R} (x y : Clifford R [c]) :
    x * y = y * x := by
  match x, y with
  | .step (.base a₀) (.base a₁), .step (.base b₀) (.base b₁) =>
    change step (base (a₀ * b₀ + c * (a₁ * b₁))) (base (a₀ * b₁ + a₁ * b₀)) =
           step (base (b₀ * a₀ + c * (b₁ * a₁))) (base (b₀ * a₁ + b₁ * a₀))
    rw [CommRingOps.mul_comm a₀ b₀, CommRingOps.mul_comm a₁ b₁,
        CommRingOps.mul_comm a₀ b₁, CommRingOps.mul_comm a₁ b₀,
        CommRingOps.add_comm (b₁ * a₀) (b₀ * a₁)]

theorem dim1_rev_eq_self {R : Type} [CommRingOps R] {c : R} (x : Clifford R [c]) :
    rev x = x := by
  match x with
  | .step (.base _) (.base _) => rfl

theorem dim1_gradeInvol_eq_conj {R : Type} [CommRingOps R] {c : R} (x : Clifford R [c]) :
    gradeInvol x = conj x := by
  rw [conj, dim1_rev_eq_self]

/-- In dimension 1 (`sig = [c]`), `x * conj x` and `conj x * x` are ALWAYS scalar. -/
theorem dim1_norm_scalar {R : Type} [CommRingOps R] {c : R} (x : Clifford R [c]) :
    x * conj x = scalar [c] (cliffordScalarNorm x) ∧
    conj x * x = scalar [c] (cliffordScalarNorm x) := by
  match x with
  | .step (.base a₀) (.base a₁) =>
    have h1 : step (c := c) (base a₀) (base a₁) * conj (step (c := c) (base a₀) (base a₁)) =
              scalar [c] (cliffordScalarNorm (step (c := c) (base a₀) (base a₁))) := by
      change step (base (a₀ * a₀ + c * (a₁ * -a₁))) (base (a₀ * -a₁ + a₁ * a₀)) =
             step (base (a₀ * a₀ + c * (a₁ * -a₁))) (base 0)
      apply step_congr rfl
      apply congrArg base
      rw [r_mul_neg, CommRingOps.mul_comm a₁ a₀, r_neg_add_cancel]
    exact ⟨h1, by rw [dim1_mul_comm, h1]⟩

/-- In dimension 2 (`sig = [c₀, c₁]`), `x * conj x` and `conj x * x` are ALWAYS scalar. -/
theorem dim2_norm_scalar {R : Type} [CommRingOps R] {c₀ c₁ : R}
    (x : Clifford R [c₀, c₁]) :
    x * conj x = scalar [c₀, c₁] (cliffordScalarNorm x) ∧
    conj x * x = scalar [c₀, c₁] (cliffordScalarNorm x) := by
  match x with
  | .step u v =>
    have hconj : conj (step (c := c₀) u v) = step (c := c₀) (conj u) (-v) := by
      unfold conj
      change gradeInvol (step (rev u) (gradeInvol (rev v))) = step (conj u) (-v)
      rw [dim1_rev_eq_self v]
      change step (gradeInvol (rev u)) (-(gradeInvol (gradeInvol v))) = step (conj u) (-v)
      rw [gradeInvol_gradeInvol, ← conj]
    have ⟨hu1, hu2⟩ := dim1_norm_scalar u
    have ⟨_, hv2⟩ := dim1_norm_scalar v
    have h_prod1 : step (c := c₀) u v * conj (step (c := c₀) u v) =
        scalar [c₀, c₁] (cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v)) := by
      rw [hconj]
      change step (u * conj u + smul c₀ (gradeInvol v * -v))
                  (gradeInvol u * -v + v * conj u) =
             step (scalar [c₁] (cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v))) 0
      rw [dim1_gradeInvol_eq_conj v, dim1_gradeInvol_eq_conj u,
          mul_neg, mul_neg, hu1, hv2,
          dim1_mul_comm (conj u) v, neg_add_cancel,
          smul_neg, smul_scalar, ← scalar_neg, ← scalar_add]
    have h_prod2 : conj (step (c := c₀) u v) * step (c := c₀) u v =
        scalar [c₀, c₁] (cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v)) := by
      rw [hconj]
      change step (conj u * u + smul c₀ (gradeInvol (-v) * v))
                  (gradeInvol (conj u) * v + (-v) * u) =
             step (scalar [c₁] (cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v))) 0
      have hgu : gradeInvol (conj u) = u := by
        rw [dim1_gradeInvol_eq_conj, conj_conj]
      rw [gradeInvol_neg, dim1_gradeInvol_eq_conj v, hgu,
          neg_mul, neg_mul, hu2, hv2,
          dim1_mul_comm v u, add_neg_cancel,
          smul_neg, smul_scalar, ← scalar_neg, ← scalar_add]
    have hsc : cliffordScalarNorm (step (c := c₀) u v) =
               cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v) := by
      change scalarPart (step (c := c₀) u v * conj (step (c := c₀) u v)) =
             cliffordScalarNorm u + -(c₀ * cliffordScalarNorm v)
      rw [h_prod1, scalarPart_scalar]
    rw [hsc]
    exact ⟨h_prod1, h_prod2⟩

/-- General bridge: whenever `x * conj x` and `conj x * x` equal the scalar
    `cliffordScalarNorm x`, vanishing of the Clifford norm is BOTH necessary and
    sufficient for `x ≠ 0` to be a zero divisor. -/
theorem zeroDivisor_iff_of_norm_scalar {F : Type} [FieldOps F] {sig : List F}
    {x : Clifford F sig}
    (h1 : x * conj x = scalar sig (cliffordScalarNorm x))
    (h2 : conj x * x = scalar sig (cliffordScalarNorm x)) :
    (IsLeftZeroDivisor x ↔ (x ≠ 0 ∧ x * conj x = 0)) ∧
    (IsZeroDivisor x ↔ (x ≠ 0 ∧ cliffordScalarNorm x = 0)) := by
  have hunit_of_ne : cliffordScalarNorm x ≠ 0 → IsUnitElem x := by
    intro hn
    refine ⟨smul (cliffordScalarNorm x)⁻¹ (conj x), ?_, ?_⟩
    · rw [mul_smul, h1, smul_scalar, f_inv_mul_cancel hn, scalar_one]
    · rw [smul_mul, h2, smul_scalar, f_inv_mul_cancel hn, scalar_one]
  constructor
  · constructor
    · intro hzd
      refine ⟨hzd.1, ?_⟩
      by_cases hn : cliffordScalarNorm x = 0
      · rw [h1, hn, scalar_zero]
      · exact absurd hzd (unit_not_leftZeroDivisor (hunit_of_ne hn))
    · intro ⟨hx, hxx⟩
      exact ⟨hx, conj x, conj_ne_zero hx, hxx⟩
  · constructor
    · intro hzd
      refine ⟨hzd.1, ?_⟩
      exact Classical.byContradiction fun hn =>
        unit_not_zeroDivisor (hunit_of_ne hn) hzd
    · intro ⟨hx, hn⟩
      have hxx : x * conj x = 0 := by rw [h1, hn, scalar_zero]
      exact ⟨hx, conj x, conj_ne_zero hx, Or.inl hxx⟩

/-- Theorem P2 (Dimension 1): Over ANY field `F` and ANY `c : F`, the Clifford norm
    vanishing criterion `x * conj x = 0` is necessary and sufficient for `x ≠ 0`
    to be a zero divisor in `Cl(F, [c])`. -/
theorem dim1_zeroDivisor_iff_norm_zero {F : Type} [FieldOps F] {c : F}
    (x : Clifford F [c]) :
    (IsLeftZeroDivisor x ↔ (x ≠ 0 ∧ x * conj x = 0)) ∧
    (IsZeroDivisor x ↔ (x ≠ 0 ∧ cliffordScalarNorm x = 0)) := by
  have ⟨h1, h2⟩ := dim1_norm_scalar x
  exact zeroDivisor_iff_of_norm_scalar h1 h2

/-- Theorem P2 (Dimension 2): Over ANY field `F` and ANY `c₀, c₁ : F`, the Clifford
    norm vanishing criterion `x * conj x = 0` is necessary and sufficient for
    `x ≠ 0` to be a zero divisor in `Cl(F, [c₀, c₁])`. -/
theorem dim2_zeroDivisor_iff_norm_zero {F : Type} [FieldOps F] {c₀ c₁ : F}
    (x : Clifford F [c₀, c₁]) :
    (IsLeftZeroDivisor x ↔ (x ≠ 0 ∧ x * conj x = 0)) ∧
    (IsZeroDivisor x ↔ (x ≠ 0 ∧ cliffordScalarNorm x = 0)) := by
  have ⟨h1, h2⟩ := dim2_norm_scalar x
  exact zeroDivisor_iff_of_norm_scalar h1 h2

/-- Non-vacuity witness 1: Over any ordered field (including ℚ and ℝ),
    `Cl_{0,1}(F) = Cl(F, [-1])` (complex-type) is a division algebra:
    every nonzero element is invertible and no zero divisors exist. -/
theorem cl01_division_algebra {F : Type} [OrderedField F] :
    (∀ x : Clifford F [-1], x ≠ 0 → IsUnitElem x) ∧
    ¬ ∃ x : Clifford F [-1], IsZeroDivisor x := by
  have hunit : ∀ x : Clifford F [-1], x ≠ 0 → IsUnitElem x := by
    intro x hx
    have ⟨h1, h2⟩ := dim1_norm_scalar x
    have hn : cliffordScalarNorm x ≠ 0 := by
      match x with
      | .step (.base a₀) (.base a₁) =>
        intro hnorm
        change a₀ * a₀ + (-1 : F) * (a₁ * -a₁) = 0 at hnorm
        rw [r_mul_neg, r_neg_one_mul, r_neg_neg] at hnorm
        have ⟨ha₀, ha₁⟩ := sum_two_sq_eq_zero hnorm
        exact hx (by rw [ha₀, ha₁]; rfl)
    refine ⟨smul (cliffordScalarNorm x)⁻¹ (conj x), ?_, ?_⟩
    · rw [mul_smul, h1, smul_scalar, f_inv_mul_cancel hn, scalar_one]
    · rw [smul_mul, h2, smul_scalar, f_inv_mul_cancel hn, scalar_one]
  refine ⟨hunit, ?_⟩
  intro ⟨x, hzd⟩
  exact unit_not_zeroDivisor (hunit x hzd.1) hzd

/-- Non-vacuity witness 2: Over any ordered field (including ℚ and ℝ),
    `Cl_{0,2}(F) = Cl(F, [-1, -1])` (Hamilton quaternion algebra) is a division algebra:
    every nonzero element is invertible and no zero divisors exist. -/
theorem cl02_division_algebra {F : Type} [OrderedField F] :
    (∀ x : Clifford F [-1, -1], x ≠ 0 → IsUnitElem x) ∧
    ¬ ∃ x : Clifford F [-1, -1], IsZeroDivisor x := by
  have hunit : ∀ x : Clifford F [-1, -1], x ≠ 0 → IsUnitElem x := by
    intro x hx
    have ⟨h1, h2⟩ := dim2_norm_scalar x
    have hn : cliffordScalarNorm x ≠ 0 := by
      match x with
      | .step (.step (.base a₀) (.base a₁)) (.step (.base b₀) (.base b₁)) =>
        intro hnorm
        let u : Clifford F [-1] := step (base a₀) (base a₁)
        let v : Clifford F [-1] := step (base b₀) (base b₁)
        have hu : cliffordScalarNorm u = a₀ * a₀ + a₁ * a₁ := by
          change a₀ * a₀ + (-1 : F) * (a₁ * -a₁) = a₀ * a₀ + a₁ * a₁
          rw [r_mul_neg, r_neg_one_mul, r_neg_neg]
        have hv : cliffordScalarNorm v = b₀ * b₀ + b₁ * b₁ := by
          change b₀ * b₀ + (-1 : F) * (b₁ * -b₁) = b₀ * b₀ + b₁ * b₁
          rw [r_mul_neg, r_neg_one_mul, r_neg_neg]
        have hconj : conj (step (c := (-1 : F)) u v) = step (conj u) (-v) := by
          unfold conj
          change gradeInvol (step (rev u) (gradeInvol (rev v))) = step (conj u) (-v)
          rw [dim1_rev_eq_self v]
          change step (gradeInvol (rev u)) (-(gradeInvol (gradeInvol v))) = step (conj u) (-v)
          rw [gradeInvol_gradeInvol, ← conj]
        have hsc : cliffordScalarNorm (step (c := (-1 : F)) u v) =
                   (a₀ * a₀ + a₁ * a₁) + (b₀ * b₀ + b₁ * b₁) := by
          unfold cliffordScalarNorm
          rw [hconj]
          change scalarPart (u * conj u + smul (-1 : F) (gradeInvol v * -v)) = _
          rw [dim1_gradeInvol_eq_conj, mul_neg, (dim1_norm_scalar u).1, (dim1_norm_scalar v).2,
              hu, hv, smul_neg, neg_smul, neg_neg, one_smul,
              scalarPart_add, scalarPart_scalar, scalarPart_scalar]
        change cliffordScalarNorm (step (c := (-1 : F)) u v) = 0 at hnorm
        rw [hsc] at hnorm
        have ⟨ha₀, ha₁, hb₀, hb₁⟩ := sum_four_sq_eq_zero hnorm
        exact hx (by rw [ha₀, ha₁, hb₀, hb₁]; rfl)
    refine ⟨smul (cliffordScalarNorm x)⁻¹ (conj x), ?_, ?_⟩
    · rw [mul_smul, h1, smul_scalar, f_inv_mul_cancel hn, scalar_one]
    · rw [smul_mul, h2, smul_scalar, f_inv_mul_cancel hn, scalar_one]
  refine ⟨hunit, ?_⟩
  intro ⟨x, hzd⟩
  exact unit_not_zeroDivisor (hunit x hzd.1) hzd

end LowDimensionNorm

/-! ### Theorem P3: Split Plane `Cl_{1,1}(F) ≅ M₂(F)` Simple Faithful Spinor Ideal -/

section SplitPlaneSpinor
variable {F : Type} [CharNeTwoField F]

def cl11E0 (F : Type) [CommRingOps F] : Clifford F [1, -1] :=
  step 0 1

def cl11E1 (F : Type) [CommRingOps F] : Clifford F [1, -1] :=
  step (step 0 1) 0

def cl11Idem (F : Type) [CharNeTwoField F] : Clifford F [1, -1] :=
  smul (halfF F) (step 1 1)

def cl11SpinorIdeal (F : Type) [CharNeTwoField F] : LeftIdeal ([1, -1] : List F) :=
  principalLeftIdeal (cl11Idem F)

theorem cl11_one_add_e0 : (1 : Clifford F [1, -1]) + cl11E0 F = step 1 1 := by
  change step ((1 : Clifford F [-1]) + 0) ((0 : Clifford F [-1]) + 1) = step 1 1
  rw [add_zero, zero_add]

theorem cl11E0_sq : cl11E0 F * cl11E0 F = 1 := by
  change step (0 * 0 + smul (1 : F) (gradeInvol (1 : Clifford F [-1]) * 1))
              (gradeInvol (0 : Clifford F [-1]) * 1 + (1 : Clifford F [-1]) * 0) = step 1 0
  rw [gradeInvol_one, gradeInvol_zero, mul_zero, zero_mul, mul_one, mul_zero,
      one_smul, zero_add, add_zero]

theorem cl11_step11_sq :
    (step 1 1 : Clifford F [1, -1]) * step 1 1 = smul (twoR F) (step 1 1) := by
  change step (1 * 1 + smul (1 : F) (gradeInvol (1 : Clifford F [-1]) * 1))
              (gradeInvol (1 : Clifford F [-1]) * 1 + 1 * 1) =
         step (smul (twoR F) 1) (smul (twoR F) 1)
  rw [gradeInvol_one, mul_one, one_smul, twoR, add_smul, one_smul]

theorem cl11Idem_idem : cl11Idem F * cl11Idem F = cl11Idem F := by
  unfold cl11Idem
  rw [smul_mul, mul_smul, cl11_step11_sq, smul_smul, smul_smul,
      CommRingOps.mul_assoc, half_mul_two, r_mul_one]

theorem cl11Idem_ne_zero : cl11Idem F ≠ 0 := by
  intro h
  have hs := congrArg scalarPart h
  unfold cl11Idem at hs
  rw [scalarPart_smul, scalarPart_zero] at hs
  change halfF F * 1 = 0 at hs
  rw [r_mul_one] at hs
  exact half_ne_zero hs

theorem cl11_mem_spinor_iff (x : Clifford F [1, -1]) :
    (cl11SpinorIdeal F).carrier x ↔
    ∃ w : Clifford F [-1], x = step w (gradeInvol w) := by
  constructor
  · rintro ⟨a, rfl⟩
    match a with
    | .step u v =>
      refine ⟨smul (halfF F) (u + gradeInvol v), ?_⟩
      unfold cl11Idem
      rw [mul_smul]
      have hmul : step (c := (1 : F)) u v * step 1 1 =
                  step (u + gradeInvol v) (gradeInvol u + v) := by
        change step (u * 1 + smul (1 : F) (gradeInvol v * 1))
                    (gradeInvol u * 1 + v * 1) =
               step (u + gradeInvol v) (gradeInvol u + v)
        rw [mul_one, mul_one, mul_one, mul_one, one_smul]
      rw [hmul]
      change step (smul (halfF F) (u + gradeInvol v))
                  (smul (halfF F) (gradeInvol u + v)) =
             step (smul (halfF F) (u + gradeInvol v))
                  (gradeInvol (smul (halfF F) (u + gradeInvol v)))
      rw [gradeInvol_smul, gradeInvol_add, gradeInvol_gradeInvol]
  · rintro ⟨w, rfl⟩
    refine ⟨step w (gradeInvol w), ?_⟩
    unfold cl11Idem
    rw [mul_smul]
    have hmul : step (c := (1 : F)) w (gradeInvol w) * step 1 1 =
                smul (twoR F) (step w (gradeInvol w)) := by
      change step (w * 1 + smul (1 : F) (gradeInvol (gradeInvol w) * 1))
                  (gradeInvol w * 1 + gradeInvol w * 1) =
             step (smul (twoR F) w) (smul (twoR F) (gradeInvol w))
      rw [gradeInvol_gradeInvol, mul_one, mul_one, one_smul]
      have h2w : ∀ z : Clifford F [-1], z + z = smul (twoR F) z := by
        intro z; rw [twoR, add_smul, one_smul]
      rw [h2w w, h2w (gradeInvol w)]
    rw [hmul, smul_smul, half_mul_two, one_smul]

/-- Theorem P3: In the simple split Clifford algebra `Cl_{1,1}(F) ≅ M₂(F)`,
    `S = Cl_{1,1}(F)·f` is a minimal left ideal, every nonzero element of `S` is a
    left zero divisor, and `S` is a faithful left `Cl_{1,1}(F)`-module (spinor module). -/
theorem cl11_spinor_minimal_left_ideal :
    (cl11SpinorIdeal F).IsMinimal ∧
    (cl11SpinorIdeal F).ConsistsOfZeroDivisors ∧
    (cl11SpinorIdeal F).IsFaithful := by
  have hmem_idem : (cl11SpinorIdeal F).carrier (cl11Idem F) :=
    ⟨1, (one_mul _).symm⟩
  have hmin : (cl11SpinorIdeal F).IsMinimal := by
    refine ⟨⟨cl11Idem F, cl11Idem_ne_zero, hmem_idem⟩, ?_⟩
    intro J ⟨z, hz_ne, hzJ⟩ hsub x hxS
    have ⟨w, hw⟩ := (cl11_mem_spinor_iff z).mp (hsub z hzJ)
    match w with
    | .step (.base p) (.base q) =>
      have recover_idem : ∀ (p' q' : F), p' ≠ 0 →
          J.carrier (step (step (base p') (base q')) (gradeInvol (step (base p') (base q')))) →
          J.carrier (cl11Idem F) := by
        intro p' q' hp' hmem'
        let elem : Clifford F [1, -1] :=
          step (step (base p') (base q')) (gradeInvol (step (base p') (base q')))
        have he0_elem : J.carrier (elem + cl11E0 F * elem) :=
          J.add_mem hmem' (J.mul_left_mem (cl11E0 F) hmem')
        have hcalc : elem + cl11E0 F * elem = smul (twoR F * (twoR F * p')) (cl11Idem F) := by
          have he0_mul : cl11E0 F * elem =
              step (step (base p') (base (-q'))) (step (base p') (base q')) := by
            change step (0 * step (base p') (base q') +
                         smul (1 : F) (gradeInvol (1 : Clifford F [-1]) *
                           step (base p') (base (-q'))))
                        (gradeInvol (0 : Clifford F [-1]) * step (base p') (base (-q')) +
                         1 * step (base p') (base q')) = _
            rw [zero_mul, gradeInvol_one, gradeInvol_zero, zero_mul, one_mul, one_mul,
                one_smul, zero_add, zero_add]
          rw [he0_mul]
          change step (step (base (p' + p')) (base (q' + -q')))
                      (step (base (p' + p')) (base (-q' + q'))) =
                 step (step (base ((twoR F * (twoR F * p')) * (halfF F * 1)))
                            (base ((twoR F * (twoR F * p')) * (halfF F * 0))))
                      (step (base ((twoR F * (twoR F * p')) * (halfF F * 1)))
                            (base ((twoR F * (twoR F * p')) * (halfF F * 0))))
          rw [r_add_neg_cancel, r_neg_add_cancel, r_mul_zero, r_mul_zero, r_mul_one,
              CommRingOps.mul_comm (twoR F) (twoR F * p'),
              CommRingOps.mul_assoc (twoR F * p') (twoR F) (halfF F),
              two_mul_half, r_mul_one, r_two_mul]
        rw [hcalc] at he0_elem
        have hcoef_ne : twoR F * (twoR F * p') ≠ 0 := by
          intro hc
          rcases f_mul_eq_zero.mp hc with h2 | h2p
          · exact twoR_ne_zero h2
          · rcases f_mul_eq_zero.mp h2p with h2 | hp0
            · exact twoR_ne_zero h2
            · exact hp' hp0
        have hscale := J.mul_left_mem (scalar _ (twoR F * (twoR F * p'))⁻¹) he0_elem
        rw [scalar_mul, smul_smul, f_inv_mul_cancel hcoef_ne, one_smul] at hscale
        exact hscale
      have hidemJ : J.carrier (cl11Idem F) := by
        rw [hw] at hzJ
        by_cases hp : p = 0
        · have hq : q ≠ 0 := by
            intro hq0
            apply hz_ne
            rw [hw, hp, hq0]
            change step (step (base 0) (base 0)) (step (base 0) (base (-0))) =
                   step (step (base 0) (base 0)) (step (base 0) (base 0))
            rw [r_neg_zero]
          have he1z : J.carrier (cl11E1 F * step (step (base p) (base q))
                        (gradeInvol (step (base p) (base q)))) :=
            J.mul_left_mem (cl11E1 F) hzJ
          have he1_eq : cl11E1 F * step (c := (1 : F)) (step (c := (-1 : F)) (base p) (base q))
                          (gradeInvol (step (base p) (base q))) =
                        step (step (base (-q)) (base p))
                             (gradeInvol (step (base (-q)) (base p))) := by
            change step (step (base 0) (base 1) * step (base p) (base q) +
                         smul (1 : F) (gradeInvol (0 : Clifford F [-1]) *
                           step (base p) (base (-q))))
                        (gradeInvol (step (c := (-1 : F)) (base 0) (base 1)) *
                           step (base p) (base (-q)) +
                         0 * step (base p) (base q)) =
                   step (step (base (-q)) (base p)) (step (base (-q)) (base (-p)))
            rw [gradeInvol_zero, zero_mul, zero_mul, smul_zero, add_zero, add_zero]
            change step (step (base (0 * p + (-1) * (1 * q))) (base (0 * q + 1 * p)))
                        (step (base (0 * p + (-1) * (-1 * -q))) (base (0 * -q + -1 * p))) =
                   step (step (base (-q)) (base p)) (step (base (-q)) (base (-p)))
            simp only [r_zero_mul, r_one_mul, r_neg_one_mul, r_neg_neg, r_zero_add]
          rw [he1_eq] at he1z
          have hnq : -q ≠ 0 := fun h0 => hq (r_neg_eq_zero.mp h0)
          exact recover_idem (-q) p hnq he1z
        · exact recover_idem p q hp hzJ
      rcases hxS with ⟨a, rfl⟩
      exact J.mul_left_mem a hidemJ
  have hzd : (cl11SpinorIdeal F).ConsistsOfZeroDivisors := by
    intro x ⟨a, ha⟩ hx_ne
    refine ⟨hx_ne, 1 - cl11Idem F, ?_, ?_⟩
    · intro h1f
      have hs := congrArg scalarPart h1f
      unfold cl11Idem at hs
      change scalarPart (1 + -(smul (halfF F) (step 1 1))) = 0 at hs
      rw [← neg_smul, scalarPart_add, scalarPart_one, scalarPart_smul] at hs
      change 1 + -halfF F * 1 = 0 at hs
      rw [r_mul_one] at hs
      have hhalf1 : halfF F = 1 := by
        apply r_add_right_cancel (a := - halfF F)
        rw [r_add_neg_cancel]
        exact hs.symm
      have hm := two_mul_half (F := F)
      rw [hhalf1, r_mul_one] at hm
      unfold twoR at hm
      have h10 : (1 : F) = 0 := by
        apply r_add_left_cancel (a := 1)
        rw [r_add_zero]
        exact hm
      exact r_one_ne_zero h10
    · calc
        x * (1 - cl11Idem F)
          = (a * cl11Idem F) * (1 + - cl11Idem F) := by rw [ha]; rfl
        _ = a * (cl11Idem F * (1 + - cl11Idem F)) := mul_assoc _ _ _
        _ = a * (cl11Idem F * 1 + cl11Idem F * (- cl11Idem F)) := by rw [left_distrib]
        _ = a * (cl11Idem F + -(cl11Idem F * cl11Idem F)) := by rw [mul_one, mul_neg]
        _ = a * 0 := by rw [cl11Idem_idem, add_neg_cancel]
        _ = 0 := mul_zero a
  have hfaith : (cl11SpinorIdeal F).IsFaithful := by
    intro a hann
    match a with
    | .step u v =>
      have hs0 : (step 1 1 : Clifford F [1, -1]) = smul (twoR F) (cl11Idem F) := by
        unfold cl11Idem
        rw [smul_smul, two_mul_half, one_smul]
      have hmem0 : (cl11SpinorIdeal F).carrier (step 1 1) := by
        rw [hs0, ← scalar_mul]
        exact (cl11SpinorIdeal F).mul_left_mem _ hmem_idem
      have hmem1 : (cl11SpinorIdeal F).carrier (cl11E1 F * step 1 1) :=
        (cl11SpinorIdeal F).mul_left_mem (cl11E1 F) hmem0
      have ha0 := hann _ hmem0
      have ha1 := hann _ hmem1
      have eq0 : u + gradeInvol v = 0 := by
        change step (u * 1 + smul (1 : F) (gradeInvol v * 1))
                    (gradeInvol u * 1 + v * 1) = step 0 0 at ha0
        injection ha0 with _ _ hev _
        rw [mul_one, mul_one, one_smul] at hev
        exact hev
      let j1 : Clifford F [-1] := step (base 0) (base 1)
      have he1s : cl11E1 F * step (c := (1 : F)) 1 1 = step j1 (-j1) := by
        change step (j1 * 1 + smul (1 : F) (gradeInvol (0 : Clifford F [-1]) * 1))
                    (gradeInvol j1 * 1 + 0 * 1) = step j1 (-j1)
        rw [mul_one, mul_one, mul_one, gradeInvol_zero, zero_mul, smul_zero, add_zero, add_zero]
        change step j1 (step (base 0) (base (-1))) = step j1 (step (base (-0)) (base (-1)))
        rw [r_neg_zero]
      rw [he1s] at ha1
      have eq1 : (u + - gradeInvol v) * j1 = 0 := by
        change step (u * j1 + smul (1 : F) (gradeInvol v * (-j1)))
                    (gradeInvol u * (-j1) + v * j1) = step 0 0 at ha1
        injection ha1 with _ _ hev _
        rw [one_smul, mul_neg, ← neg_mul, ← right_distrib] at hev
        exact hev
      have hj1_sq : j1 * (-j1) = 1 := by
        change step (base (0 * -0 + (-1) * (1 * -1))) (base (0 * -1 + 1 * -0)) =
               step (base 1) (base 0)
        simp only [r_neg_zero, r_zero_mul, r_mul_zero, r_one_mul, r_neg_mul_neg, r_zero_add]
      have eq1' : u + - gradeInvol v = 0 := by
        calc
          u + - gradeInvol v = (u + - gradeInvol v) * 1 := (mul_one _).symm
          _ = (u + - gradeInvol v) * (j1 * (-j1)) := by rw [hj1_sq]
          _ = ((u + - gradeInvol v) * j1) * (-j1) := (mul_assoc _ _ _).symm
          _ = 0 * (-j1) := by rw [eq1]
          _ = 0 := zero_mul _
      have h2u : smul (twoR F) u = 0 := by
        have hsum : (u + gradeInvol v) + (u + - gradeInvol v) = 0 := by
          rw [eq0, eq1', add_zero]
        have hlhs : (u + gradeInvol v) + (u + - gradeInvol v) = u + u := by
          rw [add_assoc u (gradeInvol v), add_left_comm (gradeInvol v) u (- gradeInvol v),
              add_neg_cancel, add_zero]
        rw [hlhs] at hsum
        rw [twoR, add_smul, one_smul, hsum]
      have hu0 : u = 0 := by
        calc
          u = smul 1 u := (one_smul u).symm
          _ = smul (halfF F * twoR F) u := by rw [half_mul_two]
          _ = smul (halfF F) (smul (twoR F) u) := (smul_smul _ _ _).symm
          _ = smul (halfF F) 0 := by rw [h2u]
          _ = 0 := smul_zero _ _
      have hv0 : v = 0 := by
        rw [hu0, zero_add] at eq0
        rw [← gradeInvol_gradeInvol v, eq0, gradeInvol_zero]
      rw [hu0, hv0]
      rfl
  exact ⟨hmin, hzd, hfaith⟩

end SplitPlaneSpinor

end Conjecture00000007622
