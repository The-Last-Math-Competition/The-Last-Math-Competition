/-
  Conjecture 00000007622 — Complete Disproof Across All Standard Conventions
  Refutes all three clauses of Conjecture 00000007622 universally over ordered fields
  (including both ℚ and ℝ) and concretely over `QRat` (ℚ), as well as over arbitrary
  fields of characteristic ≠ 2 (including ℂ):
  - Clause B refuted under BOTH sign conventions `v² = +Q(v)` (`Cl_{1,0}`, `Cl_{2,0}`,
    `Cl_{4,0}`) and `v² = -Q(v)` (`Cl_{0,3}`, `Cl_{0,4}`) on strictly anisotropic
    Euclidean spaces, in 1D over arbitrary fields (`char ≠ 2`), and element-wise on
    annihilator kernels in `Cl_{1,1}`.
  - Clause A refuted in dimension 3 (`Cl_{0,3}`) and universally in dimension 4
    (BOTH `Cl_{4,0}` and `Cl_{0,4}`) across ALL canonical involutions (`conj`, `rev`,
    `gradeInvol`) and scalar-part trace norms.
  - Clause C refuted in degenerate exterior algebras `Λ(F²)` (unique minimal left
    ideal `F·ω` has trivial zero action of `V`, is not faithful, and `Λ(F²)` has no
    nontrivial idempotents), in split Clifford algebras `Cl_{1,0}(F) ≅ F ⊕ F` (two
    non-isomorphic unfaithful minimal left ideals; zero divisors not closed under `+`),
    and in division Clifford algebras `Cl_{0,1}`, `Cl_{0,2}` (no zero divisors exist).
-/

import Conjecture00000007622.PositiveRegimes

namespace Conjecture00000007622

open Clifford

/-! ### Universal Abstract Helper for Involutory Elements `u² = 1` -/

section InvolutoryHelper
variable {R : Type} [CommRingOps R]

/-- For ANY element `u` with `u * u = 1` in `Clifford R sig`, `(1 + u)` and `(1 - u)`
    annihilate each other on both sides, and `(1 + u)² = (1 + 1) + (u + u)`.
    Proved abstractly without unfolding `u`, avoiding exponential term expansion. -/
theorem involutory_zero_divisor_identities {sig : List R} {u : Clifford R sig}
    (hu : u * u = 1) :
    (1 + u) * (1 + -u) = 0 ∧
    (1 + -u) * (1 + u) = 0 ∧
    (1 + u) * (1 + u) = (1 + 1) + (u + u) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (1 + u) * (1 + -u)
        = (1 * 1 + u * 1) + (1 * -u + u * -u) := by
          rw [left_distrib, right_distrib, right_distrib]
      _ = (1 + u) + (-u + -1) := by
          rw [mul_one, mul_one, one_mul, mul_neg, hu]
      _ = 1 + (u + (-u + -1)) := add_assoc 1 u _
      _ = 1 + ((u + -u) + -1) := by rw [← add_assoc u (-u) (-1)]
      _ = 0 := by rw [add_neg_cancel, zero_add, add_neg_cancel]
  · calc
      (1 + -u) * (1 + u)
        = (1 * 1 + -u * 1) + (1 * u + -u * u) := by
          rw [left_distrib, right_distrib, right_distrib]
      _ = (1 + -u) + (u + -1) := by
          rw [mul_one, mul_one, one_mul, neg_mul, hu]
      _ = 1 + (-u + (u + -1)) := add_assoc 1 (-u) _
      _ = 1 + ((-u + u) + -1) := by rw [← add_assoc (-u) u (-1)]
      _ = 0 := by rw [neg_add_cancel, zero_add, add_neg_cancel]
  · calc
      (1 + u) * (1 + u)
        = (1 * 1 + u * 1) + (1 * u + u * u) := by
          rw [left_distrib, right_distrib, right_distrib]
      _ = (1 + u) + (u + 1) := by
          rw [mul_one, mul_one, one_mul, hu]
      _ = 1 + (u + (1 + u)) := by rw [add_comm u 1, add_assoc 1 u (1 + u)]
      _ = 1 + (1 + (u + u)) := by rw [add_left_comm u 1 u]
      _ = (1 + 1) + (u + u) := (add_assoc 1 1 (u + u)).symm

theorem one_pm_ne_zero_of_scalarPart_zero {sig : List R} {u : Clifford R sig}
    (hu0 : scalarPart u = 0) :
    (1 + u) ≠ 0 ∧ (1 + -u) ≠ 0 := by
  have hnu0 : scalarPart (-u) = 0 := by
    have h : scalarPart (u + -u) = scalarPart (0 : Clifford R sig) :=
      congrArg scalarPart (add_neg_cancel u)
    rw [scalarPart_add, hu0, r_zero_add, scalarPart_zero] at h
    exact h
  constructor
  · intro h
    have hs := congrArg scalarPart h
    rw [scalarPart_add, scalarPart_one, hu0, r_add_zero, scalarPart_zero] at hs
    exact r_one_ne_zero hs
  · intro h
    have hs := congrArg scalarPart h
    rw [scalarPart_add, scalarPart_one, hnu0, r_add_zero, scalarPart_zero] at hs
    exact r_one_ne_zero hs

end InvolutoryHelper

/-! ### 1. Disproof of Clause B: Zero Divisors Without Isotropic Vectors -/

section DisproofClauseB

/-- Even over an ARBITRARY field `F` (including `ℚ`, `ℝ`, and algebraically closed `ℂ`),
    the 1D quadratic space `(F¹, x ↦ x²)` (`sig = [1]`) has ZERO nonzero isotropic vectors,
    yet `Cl⁺(F¹, Q) = Cl_{1,0}(F)` has zero divisors `(1 + e₀)(1 - e₀) = 0` whenever `char(F) ≠ 2`. -/
theorem cl10_anisotropic_has_zero_divisors {F : Type} [CharNeTwoField F] :
    ¬ HasIsotropicVector ([1] : List F) ∧
    ∃ x : Clifford F [1], IsLeftZeroDivisor x ∧ IsRightZeroDivisor x := by
  refine ⟨?_, ?_⟩
  · rintro ⟨v, hne, hq⟩
    match v with
    | .cons a .nil =>
      apply hne
      change (1 : F) * (a * a) + 0 = 0 at hq
      rw [r_one_mul, r_add_zero] at hq
      rw [f_sq_eq_zero.mp hq]
      rfl
  · let e₀ : Clifford F [1] := step 0 1
    have he0_sq : e₀ * e₀ = 1 := by
      change step (base (0 * 0 + 1 * (1 * 1))) (base (0 * 1 + 1 * 0)) = step (base 1) (base 0)
      simp only [r_zero_mul, r_mul_zero, r_one_mul, r_zero_add]
    have ⟨hx_ne, hy_ne⟩ := one_pm_ne_zero_of_scalarPart_zero (u := e₀) rfl
    have ⟨hxy, hyx, _⟩ := involutory_zero_divisor_identities he0_sq
    exact ⟨1 + e₀, ⟨hx_ne, 1 + -e₀, hy_ne, hxy⟩, ⟨hx_ne, 1 + -e₀, hy_ne, hyx⟩⟩

/-- Element-level refutation of Clause B even when isotropic vectors DO exist:
    In `Cl_{1,1}(F)` (`sig = [1, -1]`), nonzero isotropic vectors `e₀ + e₁ ∈ V \ {0}`
    exist, yet for the zero divisor `x = 1 + e₀`, NO nonzero grade-1 vector `v ∈ V`
    lies in `ker(L_x)` (`(1 + e₀) * embed v = 0 → v = 0`). -/
theorem cl11_isotropic_exists_yet_kernel_cap_V_trivial {F : Type} [CharNeTwoField F] :
    HasIsotropicVector ([1, -1] : List F) ∧
    IsLeftZeroDivisor (1 + cl11E0 F) ∧
    ∀ v : Vec F [1, -1], (1 + cl11E0 F) * embed v = 0 → v = Vec.zeroVec [1, -1] := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨.cons 1 (.cons 1 .nil), ?_, ?_⟩
    · intro h
      injection h with _ _ h1 _
      exact r_one_ne_zero h1
    · change (1 : F) * (1 * 1) + ((-1 : F) * (1 * 1) + 0) = 0
      rw [r_mul_one, r_mul_one, r_neg_one_mul, r_add_zero, r_add_neg_cancel]
  · have ⟨hx_ne, hy_ne⟩ := one_pm_ne_zero_of_scalarPart_zero (u := cl11E0 F) rfl
    have ⟨hxy, _, _⟩ := involutory_zero_divisor_identities (cl11E0_sq (F := F))
    exact ⟨hx_ne, 1 + - cl11E0 F, hy_ne, hxy⟩
  · intro v hv
    match v with
    | .cons v₀ (.cons v₁ .nil) =>
      rw [cl11_one_add_e0] at hv
      change step ((1 : Clifford F [-1]) * step (base 0) (base v₁) +
                   smul (1 : F) (gradeInvol (1 : Clifford F [-1]) * step (base v₀) (base 0)))
                  (gradeInvol (1 : Clifford F [-1]) * step (base v₀) (base 0) +
                   1 * step (base 0) (base v₁)) = step 0 0 at hv
      injection hv with _ _ heven _
      rw [one_mul, gradeInvol_one, one_mul, one_smul] at heven
      change step (base (0 + v₀)) (base (v₁ + 0)) = step (base 0) (base 0) at heven
      rw [r_zero_add, r_add_zero] at heven
      injection heven with _ _ hb0 hb1
      injection hb0 with hv0
      injection hb1 with hv1
      rw [hv0, hv1]
      rfl

end DisproofClauseB

/-! ### 2. Disproof of Clause A & Clause B in 3D (`Cl_{0,3}`) and 4D (`Cl_{4,0}` & `Cl_{0,4}`) -/

section DisproofClauseA

/-- Helper: volume computations for `[ε, ε, ε]` when `ε² = 1`. -/
theorem vol3_properties {F : Type} [CommRingOps F] {ε : F} (hε : ε * ε = 1) :
    let sig3 : List F := [ε, ε, ε]
    let ω₃ : Clifford F sig3 := volume sig3
    gradeInvol ω₃ = -ω₃ ∧
    rev ω₃ = -ω₃ ∧
    conj ω₃ = ω₃ ∧
    ω₃ * ω₃ = scalar sig3 (-ε) := by
  intro sig3 ω₃
  have hω1_sq : volume ([ε] : List F) * volume ([ε] : List F) = scalar [ε] ε := by
    change step (base (0 * 0 + ε * (1 * 1))) (base (0 * 1 + 1 * 0)) = step (base ε) (base 0)
    simp only [r_zero_mul, r_mul_zero, r_one_mul, r_mul_one, r_zero_add]
  have hω1_gi : gradeInvol (volume ([ε] : List F)) = - volume ([ε] : List F) := by
    change step (base 0) (base (-1)) = step (base (-0)) (base (-1))
    rw [r_neg_zero]
  have hω2_sq : volume ([ε, ε] : List F) * volume ([ε, ε] : List F) =
                scalar [ε, ε] (-1) := by
    change step (0 * 0 + smul ε (gradeInvol (volume [ε]) * volume [ε]))
                (gradeInvol (0 : Clifford F [ε]) * volume [ε] + volume [ε] * 0) =
           scalar [ε, ε] (-1)
    rw [gradeInvol_zero, zero_mul, zero_mul, mul_zero, add_zero, zero_add,
        hω1_gi, neg_mul, hω1_sq, smul_neg, smul_scalar, hε, ← scalar_neg]
    rfl
  have hω2_gi : gradeInvol (volume ([ε, ε] : List F)) = volume ([ε, ε] : List F) := by
    change step (gradeInvol (0 : Clifford F [ε])) (-(gradeInvol (volume [ε]))) =
           step 0 (volume [ε])
    rw [gradeInvol_zero, hω1_gi, neg_neg]
  have hω3_gi : gradeInvol ω₃ = -ω₃ := by
    change step (gradeInvol (0 : Clifford F [ε, ε])) (-(gradeInvol (volume [ε, ε]))) =
           step (-0) (- volume [ε, ε])
    rw [gradeInvol_zero, hω2_gi, neg_zero]
  have hω2_rev : rev (volume ([ε, ε] : List F)) = - volume ([ε, ε] : List F) := by
    change step (rev (0 : Clifford F [ε])) (gradeInvol (rev (volume [ε]))) =
           step (-0) (- volume [ε])
    rw [rev_zero, dim1_rev_eq_self, hω1_gi, neg_zero]
  have hω3_rev : rev ω₃ = -ω₃ := by
    change step (rev (0 : Clifford F [ε, ε])) (gradeInvol (rev (volume [ε, ε]))) =
           step (-0) (- volume [ε, ε])
    rw [rev_zero, hω2_rev, gradeInvol_neg, hω2_gi, neg_zero]
  have hω3_conj : conj ω₃ = ω₃ := by
    unfold conj
    rw [hω3_rev, gradeInvol_neg, hω3_gi, neg_neg]
  have hω3_sq : ω₃ * ω₃ = scalar sig3 (-ε) := by
    change step (0 * 0 + smul ε (gradeInvol (volume [ε, ε]) * volume [ε, ε]))
                (gradeInvol (0 : Clifford F [ε, ε]) * volume [ε, ε] + volume [ε, ε] * 0) =
           scalar [ε, ε, ε] (-ε)
    rw [gradeInvol_zero, zero_mul, zero_mul, mul_zero, add_zero, zero_add,
        hω2_gi, hω2_sq, smul_scalar, r_mul_neg, r_mul_one]
    rfl
  exact ⟨hω3_gi, hω3_rev, hω3_conj, hω3_sq⟩

/-- Helper 3D theorem parameterized by abstract `ε` with `-ε = 1`
    (keeping `ε` atomic during elaboration, just as in `universal_dim4_counterexample`). -/
theorem cl03_counterexample_aux {F : Type} [CharNeTwoField F]
    {ε : F} (hε_neg : -ε = 1) :
    ∃ x : Clifford F [ε, ε, ε],
      IsLeftZeroDivisor x ∧
      IsRightZeroDivisor x ∧
      conj x = x ∧
      cliffordNormElem x ≠ 0 ∧
      cliffordScalarNorm x = twoR F ∧
      cliffordScalarNorm x ≠ 0 ∧
      ¬ (∃ r : F, cliffordNormElem x = scalar [ε, ε, ε] r) := by
  have hε : ε * ε = 1 := by
    rw [← r_neg_mul_neg ε ε, hε_neg, r_one_mul]
  have ⟨_, _, hω_conj, hω_sq⟩ := vol3_properties hε
  let sig3 : List F := [ε, ε, ε]
  let ω : Clifford F sig3 := volume sig3
  have hω_sq1 : ω * ω = 1 := by
    rw [hω_sq, hε_neg, scalar_one]
  have hsc_ω : scalarPart ω = 0 := rfl
  have ⟨hx_ne, hy_ne⟩ := one_pm_ne_zero_of_scalarPart_zero hsc_ω
  have ⟨hxy, hyx, hxx_sq⟩ := involutory_zero_divisor_identities hω_sq1
  let x : Clifford F sig3 := 1 + ω
  let y : Clifford F sig3 := 1 + -ω
  have hconj_x : conj x = x := by
    change conj (1 + ω) = 1 + ω
    rw [conj_add, conj_one, hω_conj]
  have hxx : cliffordNormElem x = (1 + 1) + (ω + ω) := by
    unfold cliffordNormElem
    rw [hconj_x]
    exact hxx_sq
  have hsc_norm : cliffordScalarNorm x = twoR F := by
    unfold cliffordScalarNorm
    change scalarPart (cliffordNormElem x) = twoR F
    rw [hxx, scalarPart_add, scalarPart_add, scalarPart_one, scalarPart_add,
        hsc_ω, r_add_zero, r_add_zero]
    rfl
  have hnorm_ne : cliffordNormElem x ≠ 0 := by
    intro h0
    have hs := congrArg scalarPart h0
    rw [scalarPart_zero] at hs
    exact twoR_ne_zero (hsc_norm.symm.trans hs)
  have hnot_scalar : ¬ (∃ r : F, cliffordNormElem x = scalar sig3 r) := by
    rintro ⟨r, hr⟩
    have hr_val : r = twoR F := by
      have hs := congrArg scalarPart hr
      rw [scalarPart_scalar] at hs
      exact hs.symm.trans hsc_norm
    rw [hr_val, hxx] at hr
    have hsc2 : scalar sig3 (twoR F) = (1 : Clifford F sig3) + 1 := by
      rw [twoR, scalar_add, scalar_one]
    rw [hsc2] at hr
    have h2ω : ω + ω = 0 := by
      apply add_left_cancel (x := (1 : Clifford F sig3) + 1)
      rw [add_zero]
      exact hr
    have hsmul2 : smul (twoR F) ω = 0 := by
      rw [twoR, add_smul, one_smul]
      exact h2ω
    have hω0 : ω = 0 := by
      calc
        ω = smul 1 ω := (one_smul ω).symm
        _ = smul (halfF F * twoR F) ω := by rw [half_mul_two]
        _ = smul (halfF F) (smul (twoR F) ω) := (smul_smul _ _ _).symm
        _ = smul (halfF F) 0 := by rw [hsmul2]
        _ = 0 := smul_zero _ _
    rw [hω0, zero_mul] at hω_sq1
    exact one_ne_zero sig3 hω_sq1.symm
  exact ⟨x, ⟨hx_ne, y, hy_ne, hxy⟩, ⟨hx_ne, y, hy_ne, hyx⟩,
         hconj_x, hnorm_ne, hsc_norm, by rw [hsc_norm]; exact twoR_ne_zero, hnot_scalar⟩

/-- 3D Counterexample under `v² = -Q(v)` (`Cl⁻(F³, Q_pos) = Cl_{0,3}(F)`):
    Over any ordered field `F` (ℚ, ℝ), Euclidean 3-space `posSig F 3 = [1, 1, 1]` has
    NO nonzero isotropic vectors, yet in `Cl⁻(F³, Q_pos) = Cl(F, [-1, -1, -1])`,
    `x = 1 + e₀e₁e₂` is a left and right zero divisor whose Clifford conjugation norm
    `x * conj x = 2(1 + e₀e₁e₂)` is NONZERO, NON-SCALAR, and has scalar part `2 ≠ 0`! -/
theorem cl03_minus_counterexample {F : Type} [OrderedField F] :
    ¬ HasIsotropicVector (posSig F 3) ∧
    ∃ x : Clifford F (negSig (posSig F 3)),
      IsLeftZeroDivisor x ∧
      IsRightZeroDivisor x ∧
      conj x = x ∧
      cliffordNormElem x ≠ 0 ∧
      cliffordScalarNorm x = twoR F ∧
      cliffordScalarNorm x ≠ 0 ∧
      ¬ (∃ r : F, cliffordNormElem x = scalar _ r) :=
  ⟨posSig_no_isotropic 3, cl03_counterexample_aux (r_neg_neg (1 : F))⟩

/-- Universal 4D Theorem (`[ε, ε, ε, ε]` for `ε ∈ {+1, -1}`):
    Simultaneously covers `Cl_{4,0}(F) = Cl⁺(F⁴, Q_pos)` (`ε = +1`) AND
    `Cl_{0,4}(F) = Cl⁻(F⁴, Q_pos)` (`ε = -1`) over ANY `CharNeTwoField F`!
    The element `x = 1 + e₀e₁e₂e₃` is a two-sided zero divisor that is FIXED by ALL
    three canonical involutions (`conj`, `rev`, `gradeInvol`), so `x * ι(x) = 2x ≠ 0`
    and `⟨x * ι(x)⟩₀ = 2 ≠ 0` for EVERY canonical involution `ι`! -/
theorem universal_dim4_counterexample {F : Type} [CharNeTwoField F]
    {ε : F} (hε : ε * ε = 1) :
    ∃ x : Clifford F [ε, ε, ε, ε],
      IsLeftZeroDivisor x ∧
      IsRightZeroDivisor x ∧
      conj x = x ∧
      rev x = x ∧
      gradeInvol x = x ∧
      cliffordNormElem x ≠ 0 ∧
      reversionNormElem x ≠ 0 ∧
      gradeNormElem x ≠ 0 ∧
      cliffordScalarNorm x = twoR F ∧
      reversionScalarNorm x = twoR F ∧
      cliffordScalarNorm x ≠ 0 := by
  have ⟨hω3_gi, hω3_rev, _, hω3_sq⟩ := vol3_properties hε
  let sig4 : List F := [ε, ε, ε, ε]
  let ω₄ : Clifford F sig4 := volume sig4
  have hω4_gi : gradeInvol ω₄ = ω₄ := by
    change step (gradeInvol (0 : Clifford F [ε, ε, ε])) (-(gradeInvol (volume [ε, ε, ε]))) =
           step 0 (volume [ε, ε, ε])
    rw [gradeInvol_zero, hω3_gi, neg_neg]
  have hω4_rev : rev ω₄ = ω₄ := by
    change step (rev (0 : Clifford F [ε, ε, ε])) (gradeInvol (rev (volume [ε, ε, ε]))) =
           step 0 (volume [ε, ε, ε])
    rw [rev_zero, hω3_rev, gradeInvol_neg, hω3_gi, neg_neg]
  have hω4_conj : conj ω₄ = ω₄ := by
    unfold conj; rw [hω4_rev, hω4_gi]
  have hω4_sq : ω₄ * ω₄ = 1 := by
    change step (0 * 0 + smul ε (gradeInvol (volume [ε, ε, ε]) * volume [ε, ε, ε]))
                (gradeInvol (0 : Clifford F [ε, ε, ε]) * volume [ε, ε, ε] + volume [ε, ε, ε] * 0) =
           step 1 0
    rw [gradeInvol_zero, zero_mul, zero_mul, mul_zero, add_zero, zero_add,
        hω3_gi, neg_mul, hω3_sq, scalar_neg, neg_neg,
        smul_scalar, hε, scalar_one]
  have hsc_ω4 : scalarPart ω₄ = 0 := rfl
  have ⟨hx_ne, hy_ne⟩ := one_pm_ne_zero_of_scalarPart_zero hsc_ω4
  have ⟨hxy, hyx, hxx_sq⟩ := involutory_zero_divisor_identities hω4_sq
  let x : Clifford F sig4 := 1 + ω₄
  let y : Clifford F sig4 := 1 + -ω₄
  have hgi_x : gradeInvol x = x := by
    change gradeInvol (1 + ω₄) = 1 + ω₄
    rw [gradeInvol_add, gradeInvol_one, hω4_gi]
  have hrev_x : rev x = x := by
    change rev (1 + ω₄) = 1 + ω₄
    rw [rev_add, rev_one, hω4_rev]
  have hconj_x : conj x = x := by
    change conj (1 + ω₄) = 1 + ω₄
    rw [conj_add, conj_one, hω4_conj]
  have hx_sq_sc : scalarPart (x * x) = twoR F := by
    change scalarPart ((1 + ω₄) * (1 + ω₄)) = twoR F
    rw [hxx_sq, scalarPart_add, scalarPart_add, scalarPart_one, scalarPart_add,
        hsc_ω4, r_add_zero, r_add_zero]
    rfl
  have hx_sq_ne : x * x ≠ 0 := by
    intro h0
    have hs := congrArg scalarPart h0
    rw [hx_sq_sc, scalarPart_zero] at hs
    exact twoR_ne_zero hs
  have hc_sc : cliffordScalarNorm x = twoR F := by
    unfold cliffordScalarNorm; rw [hconj_x]; exact hx_sq_sc
  refine ⟨x, ⟨hx_ne, y, hy_ne, hxy⟩, ⟨hx_ne, y, hy_ne, hyx⟩,
          hconj_x, hrev_x, hgi_x, ?_, ?_, ?_, hc_sc, ?_, ?_⟩
  · unfold cliffordNormElem; rw [hconj_x]; exact hx_sq_ne
  · unfold reversionNormElem; rw [hrev_x]; exact hx_sq_ne
  · unfold gradeNormElem; rw [hgi_x]; exact hx_sq_ne
  · unfold reversionScalarNorm; rw [hrev_x]; exact hx_sq_sc
  · rw [hc_sc]; exact twoR_ne_zero

end DisproofClauseA

/-! ### 3. Disproof of Clause C: Minimal Left Ideals vs Spinor Modules -/

section DisproofClauseC

/-- C1: Degenerate Exterior Algebra `Λ(F²) = Cl(F, [0, 0])`:
    Over ANY `CharNeTwoField F`:
    1. `M = Cl(F, [0, 0])·ω` (`ω = e₀e₁`) is the UNIQUE minimal left ideal of `Λ(F²)`;
    2. Every nonzero element of `M` is a left zero divisor;
    3. Every generator vector `v ∈ V` acts identically as ZERO on `M` (`embed v * m = 0`),
       so `M` is NOT faithful (`¬ M.IsFaithful`);
    4. `Λ(F²)` has NO nontrivial idempotents (`e * e = e → e = 0 ∨ e = 1`), so `M` is
       not generated by any primitive idempotent (not a semisimple spinor module). -/
theorem exterior2_unique_minimal_ideal_not_spinor {F : Type} [CharNeTwoField F] :
    let ω : Clifford F [0, 0] := volume [0, 0]
    let M : LeftIdeal ([0, 0] : List F) := principalLeftIdeal ω
    M.IsMinimal ∧
    M.ConsistsOfZeroDivisors ∧
    (∀ I : LeftIdeal ([0, 0] : List F), I.IsMinimal → ∀ x, I.carrier x ↔ M.carrier x) ∧
    (∀ (v : Vec F [0, 0]) (x : Clifford F [0, 0]), M.carrier x → embed v * x = 0) ∧
    ¬ M.IsFaithful ∧
    (∀ e : Clifford F [0, 0], e * e = e → e = 0 ∨ e = 1) := by
  intro ω M
  have hω_ne : ω ≠ 0 := by
    intro h
    change step (step (base 0) (base 0)) (step (base 0) (base 1)) =
           step (step (base 0) (base 0)) (step (base 0) (base 0)) at h
    injection h with _ _ _ h1
    injection h1 with _ _ _ h2
    injection h2 with h10
    exact r_one_ne_zero h10
  have hmem_ω : M.carrier ω := ⟨1, (one_mul ω).symm⟩
  have hM_char : ∀ x : Clifford F [0, 0], M.carrier x ↔ ∃ c : F, x = smul c ω := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      match a with
      | .step (.step (.base p) (.base q)) (.step (.base r) (.base s)) =>
        refine ⟨p, ?_⟩
        change step (step (base p) (base q) * 0 +
                     smul (0 : F) (gradeInvol (step (base r) (base s)) * step (base 0) (base 1)))
                    (gradeInvol (step (c := (0 : F)) (base p) (base q)) * step (base 0) (base 1) +
                     step (base r) (base s) * 0) =
               step (step (base (p * 0)) (base (p * 0)))
                    (step (base (p * 0)) (base (p * 1)))
        rw [mul_zero, mul_zero, zero_smul, add_zero, add_zero]
        change step (step (base 0) (base 0))
                    (step (base (p * 0 + 0 * (-q * 1))) (base (p * 1 + -q * 0))) =
               step (step (base (p * 0)) (base (p * 0)))
                    (step (base (p * 0)) (base (p * 1)))
        simp only [r_mul_zero, r_zero_mul, r_mul_one, r_add_zero]
    · rintro ⟨c, rfl⟩
      exact ⟨scalar [0, 0] c, (scalar_mul c ω).symm⟩
  have hJ_contains_M : ∀ J : LeftIdeal ([0, 0] : List F), J.IsNonzero →
      ∀ x, M.carrier x → J.carrier x := by
    intro J ⟨z, hz_ne, hzJ⟩ x hxM
    have hωJ : J.carrier ω := by
      match z with
      | .step (.step (.base p) (.base q)) (.step (.base r) (.base s)) =>
        by_cases hp : p ≠ 0
        · have h1 := J.mul_left_mem ω hzJ
          have hcalc : ω * step (step (base p) (base q)) (step (base r) (base s)) = smul p ω := by
            change step (0 * step (base p) (base q) +
                         smul (0 : F) (gradeInvol (step (c := (0 : F)) (base 0) (base 1)) *
                           step (base r) (base s)))
                        (gradeInvol (0 : Clifford F [0]) * step (base r) (base s) +
                         step (base 0) (base 1) * step (base p) (base q)) =
                   step (step (base (p * 0)) (base (p * 0)))
                        (step (base (p * 0)) (base (p * 1)))
            rw [zero_mul, zero_smul, gradeInvol_zero, zero_mul, add_zero, zero_add]
            change step (step (base 0) (base 0))
                        (step (base (0 * p + 0 * (1 * q))) (base (0 * q + 1 * p))) =
                   step (step (base (p * 0)) (base (p * 0)))
                        (step (base (p * 0)) (base (p * 1)))
            simp only [r_zero_mul, r_mul_zero, r_one_mul, r_mul_one, r_zero_add]
          rw [hcalc] at h1
          have h2 := J.mul_left_mem (scalar _ p⁻¹) h1
          rw [scalar_mul, smul_smul, f_inv_mul_cancel hp, one_smul] at h2
          exact h2
        · have hp0 : p = 0 := Classical.byContradiction fun h => hp h
          rw [hp0] at hzJ hz_ne
          by_cases hq : q ≠ 0
          · let e₀ : Clifford F [0, 0] := step 0 1
            have h1 := J.mul_left_mem e₀ hzJ
            have hcalc : e₀ * step (step (base 0) (base q)) (step (base r) (base s)) = smul q ω := by
              change step (0 * step (base 0) (base q) +
                           smul (0 : F) (gradeInvol (1 : Clifford F [0]) * step (base r) (base s)))
                          (gradeInvol (0 : Clifford F [0]) * step (base r) (base s) +
                           1 * step (base 0) (base q)) =
                     step (step (base (q * 0)) (base (q * 0)))
                          (step (base (q * 0)) (base (q * 1)))
              rw [zero_mul, zero_smul, gradeInvol_zero, zero_mul, one_mul, add_zero, zero_add]
              simp only [r_mul_zero, r_mul_one]
              rfl
            rw [hcalc] at h1
            have h2 := J.mul_left_mem (scalar _ q⁻¹) h1
            rw [scalar_mul, smul_smul, f_inv_mul_cancel hq, one_smul] at h2
            exact h2
          · have hq0 : q = 0 := Classical.byContradiction fun h => hq h
            rw [hq0] at hzJ hz_ne
            by_cases hr : r ≠ 0
            · let e₁ : Clifford F [0, 0] := step (step 0 1) 0
              have h1 := J.mul_left_mem e₁ hzJ
              have hcalc : e₁ * step (step (base 0) (base 0)) (step (base r) (base s)) =
                           smul (-r) ω := by
                change step (step (base 0) (base 1) * 0 +
                             smul (0 : F) (gradeInvol (0 : Clifford F [0]) * step (base r) (base s)))
                            (gradeInvol (step (c := (0 : F)) (base 0) (base 1)) * step (base r) (base s) +
                             0 * 0) =
                       step (step (base (-r * 0)) (base (-r * 0)))
                            (step (base (-r * 0)) (base (-r * 1)))
                rw [mul_zero, zero_smul, zero_mul, add_zero, add_zero]
                change step 0 (step (base (0 * r + 0 * (-1 * s))) (base (0 * s + -1 * r))) =
                       step (step (base (-r * 0)) (base (-r * 0)))
                            (step (base (-r * 0)) (base (-r * 1)))
                simp only [r_zero_mul, r_mul_zero, r_neg_one_mul, r_mul_one, r_zero_add]
                rfl
              rw [hcalc] at h1
              have hnr : -r ≠ 0 := fun h0 => hr (r_neg_eq_zero.mp h0)
              have h2 := J.mul_left_mem (scalar _ (-r)⁻¹) h1
              rw [scalar_mul, smul_smul, f_inv_mul_cancel hnr, one_smul] at h2
              exact h2
            · have hr0 : r = 0 := Classical.byContradiction fun h => hr h
              rw [hr0] at hzJ hz_ne
              have hs : s ≠ 0 := fun hs0 => hz_ne (by rw [hs0]; rfl)
              have hz_eq : step (c := (0 : F)) (step (c := (0 : F)) (base 0) (base 0))
                             (step (base 0) (base s)) = smul s ω := by
                change step (step (base 0) (base 0)) (step (base 0) (base s)) =
                       step (step (base (s * 0)) (base (s * 0)))
                            (step (base (s * 0)) (base (s * 1)))
                simp only [r_mul_zero, r_mul_one]
              rw [hz_eq] at hzJ
              have h2 := J.mul_left_mem (scalar _ s⁻¹) hzJ
              rw [scalar_mul, smul_smul, f_inv_mul_cancel hs, one_smul] at h2
              exact h2
    have ⟨c, hc⟩ := (hM_char x).mp hxM
    rw [hc, ← scalar_mul]
    exact J.mul_left_mem _ hωJ
  have hM_min : M.IsMinimal :=
    ⟨⟨ω, hω_ne, hmem_ω⟩, fun J hJ _ x hxM => hJ_contains_M J hJ x hxM⟩
  have hM_zd : M.ConsistsOfZeroDivisors := by
    intro x hxM hx_ne
    have ⟨c, hc⟩ := (hM_char x).mp hxM
    refine ⟨hx_ne, ω, hω_ne, ?_⟩
    rw [hc, smul_mul]
    have hω_sq : ω * ω = 0 := by
      change step (0 * 0 + smul (0 : F) (gradeInvol (volume [0]) * volume [0]))
                  (gradeInvol (0 : Clifford F [0]) * volume [0] + volume [0] * 0) = 0
      rw [gradeInvol_zero, zero_mul, zero_mul, mul_zero, zero_smul, add_zero]
      rfl
    rw [hω_sq, smul_zero]
  have hM_unique : ∀ I : LeftIdeal ([0, 0] : List F), I.IsMinimal →
      ∀ x, I.carrier x ↔ M.carrier x := by
    intro I ⟨hI_nz, hI_min⟩ x
    have hM_sub_I : ∀ y, M.carrier y → I.carrier y := hJ_contains_M I hI_nz
    have hI_sub_M : ∀ y, I.carrier y → M.carrier y :=
      hI_min M ⟨ω, hω_ne, hmem_ω⟩ hM_sub_I
    exact ⟨hI_sub_M x, hM_sub_I x⟩
  have hv_zero : ∀ (v : Vec F [0, 0]) (x : Clifford F [0, 0]),
      M.carrier x → embed v * x = 0 := by
    intro v x hxM
    match v with
    | .cons v₀ (.cons v₁ .nil) =>
      have ⟨c, hc⟩ := (hM_char x).mp hxM
      rw [hc, mul_smul]
      have heω : embed (Vec.cons (c := (0 : F)) v₀ (Vec.cons (c := (0 : F)) v₁ .nil)) * ω = 0 := by
        change step (step (base 0) (base v₁) * 0 +
                     smul (0 : F) (gradeInvol (scalar [0] v₀) * step (base 0) (base 1)))
                    (gradeInvol (step (c := (0 : F)) (base 0) (base v₁)) * step (base 0) (base 1) +
                     scalar [0] v₀ * 0) = 0
        rw [mul_zero, mul_zero, zero_smul, add_zero, add_zero]
        change step 0 (step (base (0 * 0 + 0 * (-v₁ * 1))) (base (0 * 1 + -v₁ * 0))) =
               step 0 0
        simp only [r_zero_mul, r_mul_zero, r_add_zero]
        rfl
      rw [heω, smul_zero]
  have hnot_faith : ¬ M.IsFaithful := by
    intro hf
    let v1 : Vec F [0, 0] := .cons 1 (.cons 0 .nil)
    have hv1_ne : v1 ≠ Vec.zeroVec [0, 0] := by
      intro h; injection h with _ _ h10 _; exact r_one_ne_zero h10
    have he1_ne : embed v1 ≠ 0 := (embed_ne_zero_iff v1).mpr hv1_ne
    exact he1_ne (hf (embed v1) (hv_zero v1))
  have hno_idem : ∀ e : Clifford F [0, 0], e * e = e → e = 0 ∨ e = 1 := by
    intro e he
    match e with
    | .step (.step (.base p) (.base q)) (.step (.base r) (.base s)) =>
      have hsc := congrArg scalarPart he
      change scalarPart (step (base p) (base q) * step (base p) (base q) +
                         smul (0 : F) (gradeInvol (step (base r) (base s)) * step (base r) (base s))) =
             p at hsc
      rw [zero_smul, add_zero] at hsc
      change p * p + 0 * (q * q) = p at hsc
      rw [r_zero_mul, r_add_zero] at hsc
      have hp01 : p = 0 ∨ p = 1 := by
        have hsub : p * (p + -1) = 0 := by
          rw [CommRingOps.left_distrib, r_mul_neg, r_mul_one, hsc, r_add_neg_cancel]
        rcases f_mul_eq_zero.mp hsub with hp0 | hp1
        · exact Or.inl hp0
        · right
          apply r_add_right_cancel (a := -1)
          rw [r_add_neg_cancel]
          exact hp1
      rcases hp01 with hp0 | hp1
      · left
        rw [hp0] at he
        change step (step (base 0) (base q) * step (base 0) (base q) +
                     smul (0 : F) (gradeInvol (step (base r) (base s)) * step (base r) (base s)))
                    (gradeInvol (step (c := (0 : F)) (base 0) (base q)) * step (base r) (base s) +
                     step (base r) (base s) * step (base 0) (base q)) =
               step (step (base 0) (base q)) (step (base r) (base s)) at he
        rw [zero_smul, add_zero] at he
        injection he with _ _ hev hod
        change step (base (0 * 0 + 0 * (q * q))) (base (0 * q + q * 0)) =
               step (base 0) (base q) at hev
        injection hev with _ _ _ hq_eq
        injection hq_eq with hq0
        simp only [r_zero_mul, r_mul_zero, r_add_zero] at hq0
        have hq_z : q = 0 := hq0.symm
        rw [hq_z] at hod
        change step (base ((0 * r + 0 * (-0 * s)) + (r * 0 + 0 * (s * 0))))
                    (base ((0 * s + -0 * r) + (r * 0 + s * 0))) =
               step (base r) (base s) at hod
        simp only [r_neg_zero, r_zero_mul, r_mul_zero, r_add_zero] at hod
        injection hod with _ _ hr_eq hs_eq
        injection hr_eq with hr0
        injection hs_eq with hs0
        rw [hp0, hq_z, ← hr0, ← hs0]
        rfl
      · right
        rw [hp1] at he
        change step (step (base 1) (base q) * step (base 1) (base q) +
                     smul (0 : F) (gradeInvol (step (base r) (base s)) * step (base r) (base s)))
                    (gradeInvol (step (c := (0 : F)) (base 1) (base q)) * step (base r) (base s) +
                     step (base r) (base s) * step (base 1) (base q)) =
               step (step (base 1) (base q)) (step (base r) (base s)) at he
        rw [zero_smul, add_zero] at he
        injection he with _ _ hev hod
        change step (base (1 * 1 + 0 * (q * q))) (base (1 * q + q * 1)) =
               step (base 1) (base q) at hev
        injection hev with _ _ _ hq_eq
        injection hq_eq with hq2
        rw [r_one_mul, r_mul_one] at hq2
        have hq_z : q = 0 := by
          apply r_add_left_cancel (a := q)
          rw [r_add_zero]
          exact hq2
        rw [hq_z] at hod
        change step (base ((1 * r + 0 * (-0 * s)) + (r * 1 + 0 * (s * 0))))
                    (base ((1 * s + -0 * r) + (r * 0 + s * 1))) =
               step (base r) (base s) at hod
        simp only [r_neg_zero, r_zero_mul, r_mul_zero, r_one_mul, r_mul_one,
                   r_add_zero, r_zero_add] at hod
        injection hod with _ _ hr_eq hs_eq
        injection hr_eq with hr2
        injection hs_eq with hs2
        have hr_z : r = 0 := by
          apply r_add_left_cancel (a := r)
          rw [r_add_zero]; exact hr2
        have hs_z : s = 0 := by
          apply r_add_left_cancel (a := s)
          rw [r_add_zero]; exact hs2
        rw [hp1, hq_z, hr_z, hs_z]
        rfl
  exact ⟨hM_min, hM_zd, hM_unique, hv_zero, hnot_faith, hno_idem⟩

/-- C2: Split Clifford Algebra `Cl_{1,0}(F) = Cl(F, [1]) ≅ F ⊕ F`:
    Over ANY `CharNeTwoField F`:
    1. `I₊ = Cl·p₊` and `I₋ = Cl·p₋` (`p_± = (1 ± e₀)/2`) are BOTH minimal left ideals
       whose nonzero elements are zero divisors;
    2. NEITHER `I₊` nor `I₋` is faithful (`¬ I₊.IsFaithful`, `¬ I₋.IsFaithful`);
    3. `I₊` and `I₋` are NOT isomorphic as left `Cl_{1,0}(F)`-modules
       (`LeftModuleIso I₊ I₋ → False`);
    4. `p₊` and `p₋` are both zero divisors, yet `p₊ + p₋ = 1` is a unit (not a zero divisor). -/
theorem cl10_split_two_nonisomorphic_unfaithful_ideals {F : Type} [CharNeTwoField F] :
    let e₀ : Clifford F [1] := step 0 1
    let pPlus : Clifford F [1] := smul (halfF F) (1 + e₀)
    let pMinus : Clifford F [1] := smul (halfF F) (1 + -e₀)
    let IPlus : LeftIdeal ([1] : List F) := principalLeftIdeal pPlus
    let IMinus : LeftIdeal ([1] : List F) := principalLeftIdeal pMinus
    IPlus.IsMinimal ∧
    IMinus.IsMinimal ∧
    IPlus.ConsistsOfZeroDivisors ∧
    IMinus.ConsistsOfZeroDivisors ∧
    ¬ IPlus.IsFaithful ∧
    ¬ IMinus.IsFaithful ∧
    (LeftModuleIso IPlus IMinus → False) ∧
    (IsLeftZeroDivisor pPlus ∧ IsLeftZeroDivisor pMinus ∧
     pPlus + pMinus = 1 ∧ ¬ IsZeroDivisor (pPlus + pMinus)) := by
  intro e₀ pPlus pMinus IPlus IMinus
  have he0_sq : e₀ * e₀ = 1 := by
    change step (base (0 * 0 + 1 * (1 * 1))) (base (0 * 1 + 1 * 0)) = step (base 1) (base 0)
    simp only [r_zero_mul, r_mul_zero, r_one_mul, r_zero_add]
  have hpP_ne : pPlus ≠ 0 := by
    intro h
    have hs := congrArg scalarPart h
    change halfF F * (1 + 0) = 0 at hs
    rw [r_add_zero, r_mul_one] at hs
    exact half_ne_zero hs
  have hpM_ne : pMinus ≠ 0 := by
    intro h
    have hs := congrArg scalarPart h
    change halfF F * (1 + -0) = 0 at hs
    rw [r_neg_zero, r_add_zero, r_mul_one] at hs
    exact half_ne_zero hs
  have ⟨he0_pm, he0_mp, _⟩ := involutory_zero_divisor_identities he0_sq
  have hpPM : pPlus * pMinus = 0 := by
    unfold pPlus pMinus
    rw [smul_mul, mul_smul, he0_pm, smul_zero, smul_zero]
  have hpMP : pMinus * pPlus = 0 := by
    unfold pPlus pMinus
    rw [smul_mul, mul_smul, he0_mp, smul_zero, smul_zero]
  have he0_pP : e₀ * pPlus = pPlus := by
    unfold pPlus
    rw [mul_smul, left_distrib, mul_one, he0_sq, add_comm]
  have he0_pM : e₀ * pMinus = - pMinus := by
    unfold pMinus
    rw [mul_smul, left_distrib, mul_one, mul_neg, he0_sq, ← smul_neg,
        neg_add, neg_neg, add_comm]
  have hsum1 : pPlus + pMinus = 1 := by
    unfold pPlus pMinus
    rw [← smul_add, add_assoc 1 e₀ (1 + -e₀), add_left_comm e₀ 1 (-e₀),
        add_neg_cancel, add_zero]
    have h11 : (1 : Clifford F [1]) + 1 = scalar [1] (twoR F) := by
      rw [twoR, scalar_add, scalar_one]
    rw [h11, smul_scalar, half_mul_two, scalar_one]
  have hIP_char : ∀ x, IPlus.carrier x → ∃ c : F, x = smul c pPlus := by
    rintro x ⟨a, rfl⟩
    match a with
    | .step (.base a₀) (.base a₁) =>
      refine ⟨a₀ + a₁, ?_⟩
      have ha_split : step (c := (1 : F)) (base a₀) (base a₁) =
                      scalar [1] a₀ + smul a₁ e₀ := by
        change step (base a₀) (base a₁) = step (base (a₀ + a₁ * 0)) (base (0 + a₁ * 1))
        rw [r_mul_zero, r_add_zero, r_zero_add, r_mul_one]
      rw [ha_split, right_distrib, scalar_mul, smul_mul, he0_pP, ← add_smul]
  have hIM_char : ∀ x, IMinus.carrier x → ∃ c : F, x = smul c pMinus := by
    rintro x ⟨a, rfl⟩
    match a with
    | .step (.base a₀) (.base a₁) =>
      refine ⟨a₀ + -a₁, ?_⟩
      have ha_split : step (c := (1 : F)) (base a₀) (base a₁) =
                      scalar [1] a₀ + smul a₁ e₀ := by
        change step (base a₀) (base a₁) = step (base (a₀ + a₁ * 0)) (base (0 + a₁ * 1))
        rw [r_mul_zero, r_add_zero, r_zero_add, r_mul_one]
      rw [ha_split, right_distrib, scalar_mul, smul_mul, he0_pM, smul_neg, ← neg_smul, ← add_smul]
  have hIP_min : IPlus.IsMinimal := by
    refine ⟨⟨pPlus, hpP_ne, ⟨1, (one_mul _).symm⟩⟩, ?_⟩
    intro J ⟨z, hz_ne, hzJ⟩ hsub x hxIP
    have ⟨c, hc⟩ := hIP_char z (hsub z hzJ)
    have hc_ne : c ≠ 0 := by
      intro hc0; rw [hc, hc0, zero_smul] at hz_ne; exact hz_ne rfl
    have hpJ : J.carrier pPlus := by
      rw [hc] at hzJ
      have h := J.mul_left_mem (scalar [1] c⁻¹) hzJ
      rw [scalar_mul, smul_smul, f_inv_mul_cancel hc_ne, one_smul] at h
      exact h
    rcases hxIP with ⟨a, rfl⟩
    exact J.mul_left_mem a hpJ
  have hIM_min : IMinus.IsMinimal := by
    refine ⟨⟨pMinus, hpM_ne, ⟨1, (one_mul _).symm⟩⟩, ?_⟩
    intro J ⟨z, hz_ne, hzJ⟩ hsub x hxIM
    have ⟨c, hc⟩ := hIM_char z (hsub z hzJ)
    have hc_ne : c ≠ 0 := by
      intro hc0; rw [hc, hc0, zero_smul] at hz_ne; exact hz_ne rfl
    have hpJ : J.carrier pMinus := by
      rw [hc] at hzJ
      have h := J.mul_left_mem (scalar [1] c⁻¹) hzJ
      rw [scalar_mul, smul_smul, f_inv_mul_cancel hc_ne, one_smul] at h
      exact h
    rcases hxIM with ⟨a, rfl⟩
    exact J.mul_left_mem a hpJ
  have hIP_zd : IPlus.ConsistsOfZeroDivisors := by
    rintro x ⟨a, rfl⟩ hx_ne
    exact ⟨hx_ne, pMinus, hpM_ne, by rw [mul_assoc, hpPM, mul_zero]⟩
  have hIM_zd : IMinus.ConsistsOfZeroDivisors := by
    rintro x ⟨a, rfl⟩ hx_ne
    exact ⟨hx_ne, pPlus, hpP_ne, by rw [mul_assoc, hpMP, mul_zero]⟩
  have hIP_nf : ¬ IPlus.IsFaithful := by
    intro hf
    apply hpM_ne
    apply hf pMinus
    rintro x ⟨a, rfl⟩
    rw [dim1_mul_comm a pPlus, ← mul_assoc, hpMP, zero_mul]
  have hIM_nf : ¬ IMinus.IsFaithful := by
    intro hf
    apply hpP_ne
    apply hf pPlus
    rintro x ⟨a, rfl⟩
    rw [dim1_mul_comm a pMinus, ← mul_assoc, hpPM, zero_mul]
  have hnot_iso : LeftModuleIso IPlus IMinus → False := by
    intro iso
    have hmemP : IPlus.carrier pPlus := ⟨1, (one_mul _).symm⟩
    let y := iso.toFun pPlus
    have hyM : IMinus.carrier y := iso.map_mem hmemP
    have ⟨c, hc⟩ := hIM_char y hyM
    have he0_y : e₀ * y = -y := by
      rw [hc, mul_smul, he0_pM, smul_neg]
    have he0_y' : y = e₀ * y := by
      have h := iso.map_mul_left e₀ hmemP
      rw [he0_pP] at h
      exact h
    have hy2 : smul (twoR F) y = 0 := by
      have hsum : y + y = 0 := by
        have h1 : y + y = y + -y := congrArg (y + ·) (he0_y'.trans he0_y)
        rw [add_neg_cancel] at h1
        exact h1
      rw [twoR, add_smul, one_smul, hsum]
    have hy0 : y = 0 := by
      calc
        y = smul 1 y := (one_smul y).symm
        _ = smul (halfF F * twoR F) y := by rw [half_mul_two]
        _ = smul (halfF F) (smul (twoR F) y) := (smul_smul _ _ _).symm
        _ = smul (halfF F) 0 := by rw [hy2]
        _ = 0 := smul_zero _ _
    have hto0 : iso.toFun 0 = 0 := by
      have h0 := iso.map_mul_left 0 IPlus.zero_mem
      rw [zero_mul, zero_mul] at h0
      exact h0
    have hp0 : pPlus = 0 := by
      calc
        pPlus = iso.invFun y := (iso.left_inv hmemP).symm
        _ = iso.invFun 0 := by rw [hy0]
        _ = iso.invFun (iso.toFun 0) := by rw [hto0]
        _ = 0 := iso.left_inv IPlus.zero_mem
    exact hpP_ne hp0
  exact ⟨hIP_min, hIM_min, hIP_zd, hIM_zd, hIP_nf, hIM_nf, hnot_iso,
         ⟨⟨hpP_ne, pMinus, hpM_ne, hpPM⟩, ⟨hpM_ne, pPlus, hpP_ne, hpMP⟩,
          hsum1, by rw [hsum1]; exact unit_not_zeroDivisor (one_isUnit [1])⟩⟩

/-- C3: Division Clifford Algebras `Cl_{0,1}(F)` and `Cl_{0,2}(F)` over any ordered field
    have NO nonzero left ideal of zero divisors at all! -/
theorem cl01_and_cl02_no_zero_divisor_left_ideal {F : Type} [OrderedField F] :
    (¬ ∃ I : LeftIdeal ([-1] : List F), I.IsNonzero ∧ I.ConsistsOfZeroDivisors) ∧
    (¬ ∃ I : LeftIdeal ([-1, -1] : List F), I.IsNonzero ∧ I.ConsistsOfZeroDivisors) := by
  constructor
  · rintro ⟨I, ⟨x, hx_ne, hxI⟩, hzd⟩
    exact cl01_division_algebra.2 ⟨x, leftZD_to_ZD (hzd x hxI hx_ne)⟩
  · rintro ⟨I, ⟨x, hx_ne, hxI⟩, hzd⟩
    exact cl02_division_algebra.2 ⟨x, leftZD_to_ZD (hzd x hxI hx_ne)⟩

end DisproofClauseC

/-! ### 4. Master Disproof Theorem & Concrete `QRat` (ℚ) Ground Specialization -/

/-- Master Disproof Proposition parameterized by any `OrderedField F` (ℚ, ℝ). -/
def Conjecture00000007622CounterexampleBundle (F : Type) [OrderedField F] : Prop :=
  (¬ HasIsotropicVector (posSig F 1) ∧
    ∃ x : Clifford F (posSig F 1), IsLeftZeroDivisor x ∧ IsRightZeroDivisor x) ∧
  (¬ HasIsotropicVector (posSig F 3) ∧
    ∃ x : Clifford F (negSig (posSig F 3)),
      IsLeftZeroDivisor x ∧ IsRightZeroDivisor x ∧ cliffordNormElem x ≠ 0 ∧
      cliffordScalarNorm x ≠ 0) ∧
  (¬ HasIsotropicVector (posSig F 4) ∧
    (∃ x : Clifford F (posSig F 4),
      IsLeftZeroDivisor x ∧ IsRightZeroDivisor x ∧
      cliffordNormElem x ≠ 0 ∧ reversionNormElem x ≠ 0 ∧ gradeNormElem x ≠ 0 ∧
      cliffordScalarNorm x ≠ 0 ∧ reversionScalarNorm x ≠ 0) ∧
    (∃ x : Clifford F (negSig (posSig F 4)),
      IsLeftZeroDivisor x ∧ IsRightZeroDivisor x ∧
      cliffordNormElem x ≠ 0 ∧ reversionNormElem x ≠ 0 ∧ gradeNormElem x ≠ 0 ∧
      cliffordScalarNorm x ≠ 0 ∧ reversionScalarNorm x ≠ 0)) ∧
  (∃ M : LeftIdeal ([0, 0] : List F),
    M.IsMinimal ∧ M.ConsistsOfZeroDivisors ∧ ¬ M.IsFaithful ∧
    (∀ e : Clifford F [0, 0], e * e = e → e = 0 ∨ e = 1)) ∧
  (∃ I₁ I₂ : LeftIdeal ([1] : List F),
    I₁.IsMinimal ∧ I₂.IsMinimal ∧ I₁.ConsistsOfZeroDivisors ∧ I₂.ConsistsOfZeroDivisors ∧
    ¬ I₁.IsFaithful ∧ ¬ I₂.IsFaithful ∧ (LeftModuleIso I₁ I₂ → False)) ∧
  (¬ ∃ I : LeftIdeal ([-1, -1] : List F), I.IsNonzero ∧ I.ConsistsOfZeroDivisors)

/-- Master Disproof Theorem over ANY ordered field `F` (including both `ℚ` and `ℝ`):
    Simultaneously refutes Clause A, Clause B, and Clause C across BOTH sign
    conventions `v² = +Q(v)` and `v² = -Q(v)` and ALL canonical involutions/norms. -/
theorem conjecture_00000007622_false_over_ordered_field (F : Type) [OrderedField F] :
    Conjecture00000007622CounterexampleBundle F := by
  have ⟨hB1_noiso, hB1_zd⟩ := cl10_anisotropic_has_zero_divisors (F := F)
  have ⟨h03_noiso, x03, h03_l, h03_r, _, h03_n, _, h03_sn, _⟩ := cl03_minus_counterexample (F := F)
  have h1sq : (1 : F) * 1 = 1 := r_one_mul 1
  have hm1sq : (-1 : F) * (-1 : F) = 1 := by rw [r_neg_mul_neg, r_one_mul]
  have ⟨x4p, h4p_l, h4p_r, _, _, _, h4p_cn, h4p_rn, h4p_gn, h4p_cs, h4p_rs, h4p_nz⟩ :=
    universal_dim4_counterexample h1sq
  have ⟨x4m, h4m_l, h4m_r, _, _, _, h4m_cn, h4m_rn, h4m_gn, h4m_cs, h4m_rs, h4m_nz⟩ :=
    universal_dim4_counterexample hm1sq
  have ⟨hM_min, hM_zd, _, _, hM_nf, hM_idem⟩ := exterior2_unique_minimal_ideal_not_spinor (F := F)
  have ⟨hIP_min, hIM_min, hIP_zd, hIM_zd, hIP_nf, hIM_nf, h_niso, _⟩ :=
    cl10_split_two_nonisomorphic_unfaithful_ideals (F := F)
  refine ⟨⟨hB1_noiso, hB1_zd⟩,
          ⟨h03_noiso, x03, h03_l, h03_r, h03_n, h03_sn⟩,
          ⟨posSig_no_isotropic 4,
           ⟨x4p, h4p_l, h4p_r, h4p_cn, h4p_rn, h4p_gn, h4p_nz,
            by rw [h4p_rs, ← h4p_cs]; exact h4p_nz⟩,
           ⟨x4m, h4m_l, h4m_r, h4m_cn, h4m_rn, h4m_gn, h4m_nz,
            by rw [h4m_rs, ← h4m_cs]; exact h4m_nz⟩⟩,
          ⟨principalLeftIdeal (volume [0, 0]), hM_min, hM_zd, hM_nf, hM_idem⟩,
          ⟨principalLeftIdeal (smul (halfF F) (1 + step 0 1)),
           principalLeftIdeal (smul (halfF F) (1 + - step 0 1)),
           hIP_min, hIM_min, hIP_zd, hIM_zd, hIP_nf, hIM_nf, h_niso⟩,
          cl01_and_cl02_no_zero_divisor_left_ideal.2⟩

/-- Concrete, hypothesis-free ground instantiation over `QRat` (ℚ), guaranteeing
    constructive non-vacuity with zero uninstantiated typeclass assumptions. -/
theorem conjecture_00000007622_disproved_over_QRat :
    Conjecture00000007622CounterexampleBundle QRat :=
  conjecture_00000007622_false_over_ordered_field QRat

end Conjecture00000007622
