import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Tactic

open scoped ENNReal
open Set

namespace Submission00000008581

noncomputable section

/-- The complex square-summable sequences on the integer line. -/
abbrev Sequence := lp (fun _ : ℤ => ℂ) 2

private theorem two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

private theorem summable_sq (u : Sequence) : Summable (fun n : ℤ => ‖u n‖ ^ 2) := by
  simpa only [two_toReal, Real.rpow_two] using
    (lp.memℓp u).summable (by rw [two_toReal]; norm_num)

private def reindexLinear (e : ℤ ≃ ℤ) : Sequence →ₗ[ℂ] Sequence where
  toFun u := ⟨fun n => u (e n),
    memℓp_gen (e.summable_iff.mpr ((lp.memℓp u).summable (by rw [two_toReal]; norm_num)))⟩
  map_add' _ _ := lp.ext (funext fun _ => rfl)
  map_smul' _ _ := lp.ext (funext fun _ => rfl)

private theorem reindexLinear_bound (e : ℤ ≃ ℤ) (u : Sequence) :
    ‖reindexLinear e u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul, lp.norm_eq_tsum_rpow (by rw [two_toReal]; norm_num),
    lp.norm_eq_tsum_rpow (by rw [two_toReal]; norm_num) u]
  exact le_of_eq (congrArg (fun x : ℝ => x ^ (1 / (2 : ℝ≥0∞).toReal))
    (e.tsum_eq fun n => ‖u n‖ ^ (2 : ℝ≥0∞).toReal))

/-- Pullback by a permutation of the integer coordinates. -/
private def reindex (e : ℤ ≃ ℤ) : Sequence →L[ℂ] Sequence :=
  (reindexLinear e).mkContinuous 1 (reindexLinear_bound e)

@[simp] private theorem reindex_apply (e : ℤ ≃ ℤ) (u : Sequence) (n : ℤ) :
    reindex e u n = u (e n) := rfl

private def shift : Sequence →L[ℂ] Sequence := reindex (Equiv.addRight 1)
private def back : Sequence →L[ℂ] Sequence := reindex (Equiv.addRight (-1))
private def reflect : Sequence →L[ℂ] Sequence := reindex (Equiv.neg ℤ)

@[simp] private theorem shift_apply (u : Sequence) (n : ℤ) : shift u n = u (n + 1) := rfl
@[simp] private theorem back_apply (u : Sequence) (n : ℤ) : back u n = u (n - 1) := by
  change u (n + -1) = u (n - 1)
  rw [sub_eq_add_neg]
@[simp] private theorem reflect_apply (u : Sequence) (n : ℤ) : reflect u n = u (-n) := rfl

private def shiftUnit : (Sequence →L[ℂ] Sequence)ˣ where
  val := shift
  inv := back
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    apply lp.ext
    apply funext
    intro n
    change back u (n + 1) = u n
    rw [back_apply, add_sub_cancel_right]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    apply lp.ext
    apply funext
    intro n
    rw [mul_apply_eq_comp, back_apply, shift_apply, sub_add_cancel]
    rfl

private theorem reindex_norm_le (e : ℤ ≃ ℤ) : ‖reindex e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (reindexLinear_bound e)

private theorem shift_norm_le : ‖shift‖ ≤ 1 := reindex_norm_le _
private theorem back_norm_le : ‖back‖ ≤ 1 := reindex_norm_le _

private theorem unit_circle_in_shift_spectrum {z : ℂ} (hz : ‖z‖ = 1) :
    z ∈ spectrum ℂ shift := by
  rw [spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
  intro h
  let delta : Sequence := lp.single 2 0 1
  obtain ⟨u, hu⟩ := h.surjective delta
  have recurrence (n : ℤ) : z * u n - u (n + 1) = delta n := by
    have hcoord := congrArg (fun v : Sequence => v n) hu
    simpa only [ContinuousLinearMap.algebraMap_apply, sub_apply,
      lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shift_apply] using hcoord
  have sameNorm (n : ℤ) (hn : n ≠ 0) : ‖u (n + 1)‖ = ‖u n‖ := by
    have heq := recurrence n
    have hd : delta n = 0 := lp.single_apply_ne 2 0 1 hn
    rw [hd, sub_eq_zero] at heq
    rw [← heq, norm_mul, hz, one_mul]
  have positive (n : ℕ) : ‖u ((n : ℤ) + 1)‖ = ‖u 1‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, sameNorm ((n : ℤ) + 1) (by omega), ih]
  have negative (n : ℕ) : ‖u (-(n : ℤ))‖ = ‖u 0‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      have hstep := sameNorm (-((n : ℤ) + 1)) (by omega)
      rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by omega] at hstep
      exact hstep.symm.trans ih
  have hpos := (summable_sq u).comp_injective
    (i := fun n : ℕ => (n : ℤ) + 1) (by
      intro a b h
      change (a : ℤ) + 1 = (b : ℤ) + 1 at h
      omega)
  have hneg := (summable_sq u).comp_injective
    (i := fun n : ℕ => -(n : ℤ)) (by
      intro a b h
      change -(a : ℤ) = -(b : ℤ) at h
      omega)
  have h1 : u 1 = 0 := by
    have hconstant : Summable (fun _ : ℕ => ‖u 1‖ ^ 2) := by
      simpa only [Function.comp_def, positive] using hpos
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((summable_const_iff _).mp hconstant))
  have h0 : u 0 = 0 := by
    have hconstant : Summable (fun _ : ℕ => ‖u 0‖ ^ 2) := by
      simpa only [Function.comp_def, negative] using hneg
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((summable_const_iff _).mp hconstant))
  have hbad := recurrence 0
  have hd : delta 0 = 1 := lp.single_apply_self 2 0 1
  rw [hd] at hbad
  simp [h0, h1] at hbad

private theorem shift_spectrum (z : ℂ) : z ∈ spectrum ℂ shift ↔ ‖z‖ = 1 := by
  refine ⟨fun hz => ?_, unit_circle_in_shift_spectrum⟩
  change z ∈ spectrum ℂ (shiftUnit : Sequence →L[ℂ] Sequence) at hz
  have hz0 := spectrum.ne_zero_of_mem_of_unit hz
  have hle := (spectrum.norm_le_norm_mul_of_mem hz).trans
    (mul_le_one₀ shift_norm_le (norm_nonneg _) ContinuousLinearMap.norm_id_le)
  let w : ℂˣ := Units.mk0 z hz0
  have hw : (↑(w⁻¹) : ℂ) ∈ spectrum ℂ (↑(shiftUnit⁻¹) : Sequence →L[ℂ] Sequence) :=
    spectrum.inv_mem_iff.mp (show (w : ℂ) ∈ spectrum ℂ (shiftUnit : Sequence →L[ℂ] Sequence) from hz)
  have hback := (spectrum.norm_le_norm_mul_of_mem hw).trans
    (mul_le_one₀ back_norm_le (norm_nonneg _) ContinuousLinearMap.norm_id_le)
  change ‖z⁻¹‖ ≤ 1 at hback
  rw [norm_inv] at hback
  exact le_antisymm hle ((inv_le_one₀ (norm_pos_iff.mpr hz0)).mp hback)

private abbrev SequenceOperator := Sequence →L[ℂ] Sequence
private abbrev scalar (z : ℂ) : SequenceOperator := algebraMap ℂ SequenceOperator z

private def shiftSum : SequenceOperator := shift + back

private theorem unit_circle_sum_iff (t : ℂ) :
    (∃ z : ℂ, ‖z‖ = 1 ∧ z + z⁻¹ = t) ↔ t ∈ Complex.ofReal '' Icc (-2) 2 := by
  have inv_eq_conj (z : ℂ) (h : ‖z‖ = 1) : z⁻¹ = starRingEnd ℂ z := by
    simp [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  have sum_eq (z : ℂ) (h : ‖z‖ = 1) : z + z⁻¹ = ((2 * z.re : ℝ) : ℂ) := by
    rw [inv_eq_conj z h]
    apply Complex.ext
    · simp; ring
    · simp
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hre := Complex.abs_re_le_norm z
    rw [hz, abs_le] at hre
    exact ⟨2 * z.re, ⟨by linarith [hre.1], by linarith [hre.2]⟩, (sum_eq z hz).symm⟩
  · rintro ⟨r, hr, rfl⟩
    have hlow := hr.1
    have hhigh := hr.2
    let z : ℂ := ⟨r / 2, Real.sqrt (1 - (r / 2) ^ 2)⟩
    have hnonneg : 0 ≤ 1 - (r / 2) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ r + 2 by linarith) (show 0 ≤ 2 - r by linarith)]
    have hzSq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change r / 2 * (r / 2) + Real.sqrt (1 - (r / 2) ^ 2) *
        Real.sqrt (1 - (r / 2) ^ 2) = 1
      rw [Real.mul_self_sqrt hnonneg]
      ring
    have hz : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    refine ⟨z, hz, (sum_eq z hz).trans ?_⟩
    apply congrArg Complex.ofReal
    change 2 * (r / 2) = r
    ring

private theorem shiftSum_spectrum :
    spectrum ℂ shiftSum = Complex.ofReal '' Icc (-2) 2 := by
  ext t
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4) (by decide : 0 < 2)
  let z := (t + d) / 2
  let w := (t - d) / 2
  have hadd : z + w = t := by dsimp [z, w]; ring
  have hmul : z * w = 1 := by dsimp [z, w]; linear_combination -hd / 4
  have hfactor : scalar t - shiftSum = -back * ((shift - scalar z) * (shift - scalar w)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply lp.ext
    funext n
    simp only [shiftSum, mul_apply_eq_comp, sub_apply, add_apply, neg_apply,
      lp.coeFn_sub, lp.coeFn_add, lp.coeFn_neg, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      ContinuousLinearMap.algebraMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      shift_apply, back_apply, sub_add_cancel]
    linear_combination -congrArg (fun x => x * u n) hadd +
      congrArg (fun x => x * u (n - 1)) hmul
  have hc : Commute (shift - scalar z) (shift - scalar w) :=
    ((Commute.refl shift).sub_right (Algebra.commutes w shift).symm).sub_left
      (Commute.sub_right (Algebra.commutes z shift) (Algebra.commutes z (scalar w)))
  have hback : IsUnit (-back) := (IsUnit.neg_iff _).2 shiftUnit⁻¹.isUnit
  have hunit : IsUnit (scalar t - shiftSum) ↔
      IsUnit (scalar z - shift) ∧ IsUnit (scalar w - shift) := by
    rw [hfactor, hback.mul_left_iff, hc.isUnit_mul_iff, ← neg_sub (scalar z) shift,
      ← neg_sub (scalar w) shift, IsUnit.neg_iff, IsUnit.neg_iff]
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hmul
  have hw : w = z⁻¹ := eq_inv_of_mul_eq_one_left (mul_comm z w ▸ hmul)
  have hnorm : ‖w‖ = 1 ↔ ‖z‖ = 1 := by
    rw [hw, norm_inv, inv_eq_one]
  rw [spectrum.mem_iff, hunit, ← spectrum.notMem_iff, ← spectrum.notMem_iff,
    shift_spectrum, shift_spectrum, hnorm, and_self, not_not]
  rw [← unit_circle_sum_iff]
  refine ⟨fun hz => ⟨z, hz, hw ▸ hadd⟩, ?_⟩
  rintro ⟨v, hv, hvt⟩
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hroots : (v - z) * (v - w) = 0 := calc
    (v - z) * (v - w) = v * (v - t) + 1 := by
      linear_combination -congrArg (fun x => x * v) hadd + hmul
    _ = 0 := by rw [← hvt]; field_simp; ring
  rcases mul_eq_zero.mp hroots with h | h
  · exact sub_eq_zero.mp h ▸ hv
  · exact hnorm.mp (sub_eq_zero.mp h ▸ hv)

/-- Even and odd sites of one scalar sequence, in separate square-summable components. -/
abbrev BlockSequence := Sequence × Sequence
abbrev BlockOperator := BlockSequence →L[ℂ] BlockSequence

private abbrev fst := ContinuousLinearMap.fst ℂ Sequence Sequence
private abbrev snd := ContinuousLinearMap.snd ℂ Sequence Sequence

/-- The two positive bonds and alternating diagonal of a period-two Jacobi matrix. -/
structure Jacobi where
  a : ℝ
  c : ℝ
  b : ℝ
  a_pos : 0 < a
  c_pos : 0 < c

/-- The diagonal coefficient at site `n`. -/
def Jacobi.diagonal (J : Jacobi) (n : ℤ) : ℝ :=
  if n % 2 = 0 then J.b else -J.b

/-- The bond from site `n` to site `n + 1`. -/
def Jacobi.bond (J : Jacobi) (n : ℤ) : ℝ :=
  if n % 2 = 0 then J.a else J.c

theorem Jacobi.bond_pos (J : Jacobi) (n : ℤ) : 0 < J.bond n := by
  unfold Jacobi.bond
  split
  · exact J.a_pos
  · exact J.c_pos

theorem Jacobi.period_two (J : Jacobi) (n : ℤ) :
    J.diagonal (n + 2) = J.diagonal n ∧ J.bond (n + 2) = J.bond n := by
  simp only [Jacobi.diagonal, Jacobi.bond, show (n + 2) % 2 = n % 2 by omega, and_self]

/-- The actual bounded Jacobi operator, in even/odd coordinates. -/
def Jacobi.operator (J : Jacobi) : BlockOperator :=
  let a : ℂ := J.a
  let c : ℂ := J.c
  let b : ℂ := J.b
  (b • fst + a • snd + c • (back.comp snd)).prod
    (a • fst + c • (shift.comp fst) - b • snd)

@[simp] theorem Jacobi.even_apply (J : Jacobi) (u : BlockSequence) (n : ℤ) :
    (J.operator u).1 n = (J.b : ℂ) * u.1 n + (J.a : ℂ) * u.2 n + (J.c : ℂ) * u.2 (n - 1) := by
  rfl

@[simp] theorem Jacobi.odd_apply (J : Jacobi) (u : BlockSequence) (n : ℤ) :
    (J.operator u).2 n = (J.a : ℂ) * u.1 n + (J.c : ℂ) * u.1 (n + 1) - (J.b : ℂ) * u.2 n :=
  rfl

/-- Read the scalar sequence at an integer site. -/
def atSite (u : BlockSequence) (n : ℤ) : ℂ :=
  if n % 2 = 0 then u.1 (n / 2) else u.2 (n / 2)

theorem Jacobi.apply_atSite (J : Jacobi) (u : BlockSequence) (n : ℤ) :
    atSite (J.operator u) n = (J.bond (n - 1) : ℂ) * atSite u (n - 1) +
      (J.diagonal n : ℂ) * atSite u n + (J.bond n : ℂ) * atSite u (n + 1) := by
  by_cases h : n % 2 = 0
  · have hprev : (n - 1) % 2 ≠ 0 := by omega
    have hnext : (n + 1) % 2 ≠ 0 := by omega
    simp only [atSite, Jacobi.diagonal, Jacobi.bond, h, hprev, hnext, if_true, if_false,
      Jacobi.even_apply, show (n - 1) / 2 = n / 2 - 1 by omega,
      show (n + 1) / 2 = n / 2 by omega]
    ring
  · have hprev : (n - 1) % 2 = 0 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp only [atSite, Jacobi.diagonal, Jacobi.bond, h, hprev, hnext, if_false, if_true,
      Jacobi.odd_apply, Complex.ofReal_neg, show (n - 1) / 2 = n / 2 by omega,
      show (n + 1) / 2 = n / 2 + 1 by omega]
    ring

private def parityIndex : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)
  invFun := fun n => if n % 2 = 0 then .inl (n / 2) else .inr (n / 2)
  left_inv := by
    rintro (n | n)
    · change (if (2 * n) % 2 = 0 then Sum.inl (2 * n / 2) else Sum.inr (2 * n / 2)) = Sum.inl n
      rw [if_pos (by omega), show 2 * n / 2 = n by omega]
    · change (if (2 * n + 1) % 2 = 0 then Sum.inl ((2 * n + 1) / 2)
        else Sum.inr ((2 * n + 1) / 2)) = Sum.inr n
      rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]
  right_inv := by
    intro n
    change Sum.elim (fun k : ℤ => 2 * k) (fun k => 2 * k + 1)
      (if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)) = n
    split
    · change 2 * (n / 2) = n
      omega
    · change 2 * (n / 2) + 1 = n
      omega

private def restrictSitesLinear (i : ℤ → ℤ) (hi : Function.Injective i) :
    Sequence →ₗ[ℂ] Sequence where
  toFun u := ⟨fun n => u (i n),
    memℓp_gen ((lp.memℓp u).summable (by rw [two_toReal]; norm_num) |>.comp_injective hi)⟩
  map_add' _ _ := lp.ext (funext fun _ => rfl)
  map_smul' _ _ := lp.ext (funext fun _ => rfl)

private def restrictSites (i : ℤ → ℤ) (hi : Function.Injective i) : Sequence →L[ℂ] Sequence :=
  (restrictSitesLinear i hi).mkContinuous 1 (by
    intro u
    rw [one_mul]
    apply lp.norm_le_of_forall_sum_le (by rw [two_toReal]; norm_num) (norm_nonneg u)
    intro s
    have h := lp.sum_rpow_le_norm_rpow (by rw [two_toReal]; norm_num) u (s.map ⟨i, hi⟩)
    rw [Finset.sum_map] at h
    exact h)

private def splitSites : Sequence →L[ℂ] BlockSequence :=
  (restrictSites (fun n => 2 * n) (by
    intro i j h
    change 2 * i = 2 * j at h
    omega)).prod
  (restrictSites (fun n => 2 * n + 1) (by
    intro i j h
    change 2 * i + 1 = 2 * j + 1 at h
    omega))

private theorem splitSites_atSite (u : Sequence) (n : ℤ) : atSite (splitSites u) n = u n := by
  unfold atSite
  split
  · change u (2 * (n / 2)) = u n
    rw [show 2 * (n / 2) = n by omega]
  · change u (2 * (n / 2) + 1) = u n
    rw [show 2 * (n / 2) + 1 = n by omega]

private def combineSites (u : BlockSequence) : Sequence :=
  ⟨atSite u, by
    apply memℓp_gen
    let f : ℤ ⊕ ℤ → ℝ := fun n => ‖atSite u (parityIndex n)‖ ^ (2 : ℝ≥0∞).toReal
    apply (parityIndex.summable_iff (f := fun n => ‖atSite u n‖ ^ (2 : ℝ≥0∞).toReal)).mp
    change Summable f
    apply Summable.sum f
    · have h : f ∘ Sum.inl = fun n => ‖u.1 n‖ ^ (2 : ℝ≥0∞).toReal := by
        funext n
        change ‖atSite u (2 * n)‖ ^ _ = ‖u.1 n‖ ^ _
        simp [atSite, show (2 * n) % 2 = 0 by omega, show 2 * n / 2 = n by omega]
      rw [h]
      exact (lp.memℓp u.1).summable (by rw [two_toReal]; norm_num)
    · have h : f ∘ Sum.inr = fun n => ‖u.2 n‖ ^ (2 : ℝ≥0∞).toReal := by
        funext n
        change ‖atSite u (2 * n + 1)‖ ^ _ = ‖u.2 n‖ ^ _
        simp [atSite, show (2 * n + 1) / 2 = n by omega]
      rw [h]
      exact (lp.memℓp u.2).summable (by rw [two_toReal]; norm_num)⟩

private theorem splitSites_bijective : Function.Bijective splitSites := by
  refine ⟨?_, ?_⟩
  · intro u v h
    apply lp.ext
    funext n
    exact (splitSites_atSite u n).symm.trans
      ((congrArg (fun w => atSite w n) h).trans (splitSites_atSite v n))
  · intro u
    refine ⟨combineSites u, Prod.ext ?_ ?_⟩
    · apply lp.ext
      funext n
      change atSite u (2 * n) = u.1 n
      simp [atSite, show (2 * n) % 2 = 0 by omega, show 2 * n / 2 = n by omega]
    · apply lp.ext
      funext n
      change atSite u (2 * n + 1) = u.2 n
      simp [atSite, show (2 * n + 1) / 2 = n by omega]

private def evenOddEquiv : Sequence ≃L[ℂ] BlockSequence :=
  ContinuousLinearEquiv.ofBijective splitSites
    (LinearMap.ker_eq_bot.mpr splitSites_bijective.injective)
    (LinearMap.range_eq_top.mpr splitSites_bijective.surjective)

/-- The same Jacobi operator on scalar sequences indexed directly by the integer line. -/
def Jacobi.siteOperator (J : Jacobi) : Sequence →L[ℂ] Sequence :=
  evenOddEquiv.symm.conjContinuousAlgEquiv J.operator

theorem Jacobi.siteOperator_apply (J : Jacobi) (u : Sequence) (n : ℤ) :
    J.siteOperator u n = (J.bond (n - 1) : ℂ) * u (n - 1) +
      (J.diagonal n : ℂ) * u n + (J.bond n : ℂ) * u (n + 1) := by
  have hleft (w : BlockSequence) (i : ℤ) : evenOddEquiv.symm w i = atSite w i := by
    rw [← splitSites_atSite (evenOddEquiv.symm w) i]
    change atSite (evenOddEquiv (evenOddEquiv.symm w)) i = atSite w i
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change evenOddEquiv.symm (J.operator (splitSites u)) n = _
  rw [hleft, J.apply_atSite]
  simp only [splitSites_atSite]

theorem Jacobi.site_spectrum (J : Jacobi) :
    spectrum ℂ J.siteOperator = spectrum ℂ J.operator :=
  AlgEquiv.spectrum_eq evenOddEquiv.symm.conjContinuousAlgEquiv J.operator

private def blockShiftSum : BlockOperator := shiftSum.prodMap shiftSum

private theorem blockShiftSum_spectrum : spectrum ℂ blockShiftSum = spectrum ℂ shiftSum := by
  ext t
  rw [spectrum.mem_iff, spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_bijective]
  let f := scalar t - shiftSum
  change (¬ Function.Bijective (Prod.map f f)) ↔ ¬ Function.Bijective f
  apply not_congr
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.prodMap h⟩
  · intro u v huv
    exact congrArg Prod.fst (h.injective (show Prod.map f f (u, 0) = Prod.map f f (v, 0) by
      exact Prod.ext huv rfl))
  · intro v
    obtain ⟨u, hu⟩ := h.surjective (v, 0)
    exact ⟨u.1, congrArg Prod.fst hu⟩

private theorem Jacobi.operator_sq (J : Jacobi) :
    J.operator ^ 2 = algebraMap ℂ BlockOperator (↑J.a ^ 2 + ↑J.c ^ 2 + ↑J.b ^ 2) +
      ((J.a : ℂ) * (J.c : ℂ)) • blockShiftSum := by
  rw [pow_two]
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · apply lp.ext
    funext n
    change (J.operator (J.operator u)).1 n =
      (↑J.a ^ 2 + ↑J.c ^ 2 + ↑J.b ^ 2) * u.1 n + ↑J.a * ↑J.c * (u.1 (n + 1) + u.1 (n - 1))
    simp only [Jacobi.even_apply, Jacobi.odd_apply, sub_add_cancel]
    ring
  · apply lp.ext
    funext n
    change (J.operator (J.operator u)).2 n =
      (↑J.a ^ 2 + ↑J.c ^ 2 + ↑J.b ^ 2) * u.2 n + ↑J.a * ↑J.c * (u.2 (n + 1) + u.2 (n - 1))
    simp only [Jacobi.even_apply, Jacobi.odd_apply, add_sub_cancel_right]
    ring

private def parityReflection : BlockOperator :=
  (reflect.comp snd).prod ((-reflect).comp fst)

private def parityReflectionUnit : BlockOperatorˣ where
  val := parityReflection
  inv := -parityReflection
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;> apply lp.ext <;> funext n
    · change -(-u.1 (-(-n))) = u.1 n
      simp
    · change -( -u.2 (-(-n))) = u.2 n
      simp
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;> apply lp.ext <;> funext n
    · change -(-u.1 (-(-n))) = u.1 n
      simp
    · change -(-u.2 (-(-n))) = u.2 n
      simp

private theorem Jacobi.anticommutes (J : Jacobi) :
    parityReflection * J.operator = (-J.operator) * parityReflection := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · apply lp.ext
    funext n
    change (J.operator u).2 (-n) = -(J.operator (parityReflection u)).1 n
    rw [Jacobi.odd_apply, Jacobi.even_apply]
    change ↑J.a * u.1 (-n) + ↑J.c * u.1 (-n + 1) - ↑J.b * u.2 (-n) =
      -(↑J.b * u.2 (-n) + ↑J.a * (-u.1 (-n)) + ↑J.c * (-u.1 (-(n - 1))))
    rw [show -(n - 1) = -n + 1 by omega]
    ring
  · apply lp.ext
    funext n
    change -(J.operator u).1 (-n) = -(J.operator (parityReflection u)).2 n
    rw [Jacobi.even_apply, Jacobi.odd_apply]
    change -(↑J.b * u.1 (-n) + ↑J.a * u.2 (-n) + ↑J.c * u.2 (-n - 1)) =
      -(↑J.a * u.2 (-n) + ↑J.c * u.2 (-(n + 1)) - ↑J.b * (-u.1 (-n)))
    rw [show -(n + 1) = -n - 1 by omega]
    ring

private theorem Jacobi.spectrum_neg (J : Jacobi) {z : ℂ} :
    -z ∈ spectrum ℂ J.operator ↔ z ∈ spectrum ℂ J.operator := by
  have hconj : (↑parityReflectionUnit : BlockOperator) * J.operator *
      (↑parityReflectionUnit⁻¹ : BlockOperator) = -J.operator := by
    change (parityReflection * J.operator) * (↑parityReflectionUnit⁻¹ : BlockOperator) =
      -J.operator
    rw [J.anticommutes, mul_assoc]
    change -J.operator * (↑parityReflectionUnit * ↑parityReflectionUnit⁻¹) = -J.operator
    simp
  have h := spectrum.units_conjugate (R := ℂ) (a := J.operator) (u := parityReflectionUnit)
  rw [hconj, ← spectrum.neg_eq] at h
  nth_rw 2 [← h]
  simp

private theorem Jacobi.mem_spectrum_sq (J : Jacobi) (z : ℂ) :
    z ^ 2 ∈ spectrum ℂ (J.operator ^ 2) ↔ z ∈ spectrum ℂ J.operator := by
  rw [spectrum.map_pow_of_pos J.operator (by decide : 0 < 2)]
  refine ⟨?_, fun h => ⟨z, h, rfl⟩⟩
  rintro ⟨x, hx, hxz⟩
  have hprod : (x - z) * (x + z) = 0 := by linear_combination hxz
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h ▸ hx
  · exact J.spectrum_neg.mp (add_eq_zero_iff_eq_neg.mp h ▸ hx)

/-- The common spectrum, with two nondegenerate intervals and an open gap. -/
def twoBands : Set ℝ := Icc (-5) (-3) ∪ Icc 3 5

private theorem square_bounds (r : ℝ) : 9 ≤ r ^ 2 ∧ r ^ 2 ≤ 25 ↔ r ∈ twoBands := by
  have hlo : 9 ≤ r ^ 2 ↔ 3 ≤ |r| := by
    rw [← show (3 : ℝ) ^ 2 = 9 by norm_num, sq_le_sq, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))]
  have hhi : r ^ 2 ≤ 25 ↔ |r| ≤ 5 := by
    rw [← show (5 : ℝ) ^ 2 = 25 by norm_num, sq_le_sq, abs_of_nonneg (by norm_num : 0 ≤ (5 : ℝ))]
  rw [hlo, hhi, le_abs, abs_le]
  unfold twoBands
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨hneg | hpos, hlow, hhigh⟩
    · exact Or.inr ⟨hneg, hhigh⟩
    · exact Or.inl ⟨hlow, by linarith⟩
  · rintro (⟨hlow, hhigh⟩ | ⟨hlow, hhigh⟩)
    · exact ⟨Or.inr (by linarith), hlow, by linarith⟩
    · exact ⟨Or.inl hlow, by linarith, hhigh⟩

private theorem scaled_square_mem (z : ℂ) :
    (z ^ 2 - 17) / 4 ∈ Complex.ofReal '' Icc (-2) 2 ↔ z ∈ Complex.ofReal '' twoBands := by
  constructor
  · rintro ⟨r, ⟨hlo, hhi⟩, hr⟩
    have hz : z ^ 2 = ((4 * r + 17 : ℝ) : ℂ) := by
      push_cast
      linear_combination -4 * hr
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      at hre him
    have hprod : z.re * z.im = 0 := by nlinarith
    have him0 : z.im = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exfalso
        rw [h, zero_mul, zero_sub] at hre
        nlinarith [sq_nonneg z.im]
      · exact h
    refine ⟨z.re, square_bounds _ |>.mp ⟨?_, ?_⟩, Complex.ext rfl (by simpa using him0.symm)⟩
    · rw [him0, mul_zero, sub_zero, ← pow_two] at hre
      linarith
    · rw [him0, mul_zero, sub_zero, ← pow_two] at hre
      linarith
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hlo, hhi⟩ := (square_bounds r).mpr hr
    refine ⟨(r ^ 2 - 17) / 4, ⟨by linarith, by linarith⟩, ?_⟩
    push_cast
    rfl

private theorem Jacobi.spectrum_of_parameters (J : Jacobi)
    (hsq : (J.a : ℂ) ^ 2 + (J.c : ℂ) ^ 2 + (J.b : ℂ) ^ 2 = 17)
    (hmul : (J.a : ℂ) * (J.c : ℂ) = 4) :
    spectrum ℂ J.operator = Complex.ofReal '' twoBands := by
  ext z
  rw [← J.mem_spectrum_sq, J.operator_sq, hsq, hmul]
  have hadd : z ^ 2 = ((z ^ 2 - 17) / 4) * 4 + 17 := by ring
  rw [hadd, spectrum.add_mem_add_iff]
  let four : ℂˣ := Units.mk0 4 (by norm_num)
  have hscale : ((z ^ 2 - 17) / 4) * 4 ∈ spectrum ℂ ((4 : ℂ) • blockShiftSum) ↔
      (z ^ 2 - 17) / 4 ∈ spectrum ℂ blockShiftSum := by
    rw [mul_comm ((z ^ 2 - 17) / 4) 4]
    exact spectrum.smul_mem_smul_iff (r := four)
  rw [hscale, blockShiftSum_spectrum, shiftSum_spectrum, scaled_square_mem]

/-- Alternating bonds 1 and 4 and a zero diagonal. -/
def first : Jacobi := ⟨1, 4, 0, by norm_num, by norm_num⟩

/-- Constant bond 2 and an alternating diagonal with magnitudes 3. -/
def second : Jacobi := ⟨2, 2, 3, by norm_num, by norm_num⟩

theorem first_spectrum : spectrum ℂ first.siteOperator = Complex.ofReal '' twoBands := by
  rw [first.site_spectrum]
  apply first.spectrum_of_parameters <;> norm_num [first]

theorem second_spectrum : spectrum ℂ second.siteOperator = Complex.ofReal '' twoBands := by
  rw [second.site_spectrum]
  apply second.spectrum_of_parameters <;> norm_num [second]

/-- The bilateral tridiagonal matrix entries, in the original site indexing. -/
def Jacobi.entry (J : Jacobi) (i j : ℤ) : ℝ :=
  if i = j then J.diagonal i
  else if j = i + 1 then J.bond i
  else if i = j + 1 then J.bond j
  else 0

theorem Jacobi.entry_symmetric (J : Jacobi) (i j : ℤ) : J.entry i j = J.entry j i := by
  by_cases h : i = j
  · subst j
    rfl
  · unfold Jacobi.entry
    rw [if_neg h, if_neg (Ne.symm h)]
    split_ifs <;> first | rfl | omega

/-- The entries are the coefficients of the scalar operator on the coordinate vectors. -/
theorem Jacobi.entry_eq_operator (J : Jacobi) (i j : ℤ) :
    (J.entry i j : ℂ) = J.siteOperator (lp.single 2 j 1 : Sequence) i := by
  rw [J.siteOperator_apply]
  unfold Jacobi.entry
  split_ifs with h hright hleft
  · subst j
    rw [lp.single_apply_ne 2 i 1 (show i - 1 ≠ i by omega), lp.single_apply_self,
      lp.single_apply_ne 2 i 1 (show i + 1 ≠ i by omega)]
    simp
  · subst j
    rw [lp.single_apply_ne 2 (i + 1) 1 (show i - 1 ≠ i + 1 by omega),
      lp.single_apply_ne 2 (i + 1) 1 h, lp.single_apply_self]
    simp
  · rw [lp.single_apply_ne 2 j 1 h, lp.single_apply_ne 2 j 1 (Ne.symm hright),
      show i - 1 = j by omega, lp.single_apply_self]
    simp
  · rw [lp.single_apply_ne 2 j 1 h, lp.single_apply_ne 2 j 1 (Ne.symm hright),
      lp.single_apply_ne 2 j 1 (show i - 1 ≠ j by omega)]
    simp

theorem first_bond_changes : first.bond 0 ≠ first.bond 1 := by
  norm_num [Jacobi.bond, first]

theorem second_diagonal_changes : second.diagonal 0 ≠ second.diagonal 1 := by
  norm_num [Jacobi.diagonal, second]

/-- Reflection about any axis of the integer line, also allowing translations. -/
def LineEquivalent (J K : Jacobi) : Prop :=
  ∃ (t : ℤ) (reflected : Bool), ∀ i j : ℤ,
    J.entry i j = K.entry (if reflected then t - i else t + i)
      (if reflected then t - j else t + j)

theorem no_site_relabeling (f : ℤ → ℤ) : ¬ ∀ i j : ℤ,
    first.entry i j = second.entry (f i) (f j) := by
  intro h
  have hdiag := h 0 0
  simp only [Jacobi.entry, if_true, Jacobi.diagonal, first, second, neg_zero, ite_self] at hdiag
  split at hdiag <;> norm_num at hdiag

/-- The mirror-uniqueness assertion restricted to period-two matrices and a common
two-band spectrum with four distinct endpoints. -/
def MirrorUniqueness : Prop :=
  ∀ (J K : Jacobi) (a b c d : ℝ), a < b → b < c → c < d →
    spectrum ℂ J.siteOperator = Complex.ofReal '' (Icc a b ∪ Icc c d) →
    spectrum ℂ K.siteOperator = Complex.ofReal '' (Icc a b ∪ Icc c d) →
    LineEquivalent J K

theorem not_mirrorUniqueness : ¬ MirrorUniqueness := by
  intro h
  obtain ⟨t, reflected, hentries⟩ := h first second (-5) (-3) 3 5
    (by norm_num) (by norm_num) (by norm_num) first_spectrum second_spectrum
  exact no_site_relabeling (fun n => if reflected then t - n else t + n) hentries

theorem conjecture_00000008581_false (P Q : Prop) : ¬ (P ∧ MirrorUniqueness ∧ Q) :=
  fun h => not_mirrorUniqueness h.2.1

#print axioms conjecture_00000008581_false

end

end Submission00000008581
