/-
  SpinorMinimalIdeals/Counterexamples.lean
  Complete formal refutations of Conjecture 00000007604 across all three
  structural regimes outside even-dimensional split/complex nondegenerate
  Clifford algebras:

    Regime I   — Odd dimensions (`n = 2m + 1`): arithmetic impossibility + `Cl_{1,0}(ℚ)`.
    Regime II  — Even-dimensional Bott division-algebra obstruction: `Cl_{0,2}(ℚ) ≅ ℍ_ℚ` (`n = 2`).
    Regime III — Degenerate quadratic forms (`Q = 0`): exterior algebra `Λ(ℚ^2)` (`n = 2`).
-/

import SpinorMinimalIdeals.PositiveSplitCl11

namespace SpinorMinimalIdeals

open PolyNorm

private theorem eq_zero_of_eq_neg {a : RatQ} (h : a = -a) : a = 0 := by
  have hsum : a + a = 0 := by
    have h1 : a + a = a + (-a) := congrArg (fun t => a + t) h
    rw [h1, RatQ.add_neg_cancel]
  have h2 : (2 : RatQ) * a = 0 := by
    have hid : (2 : RatQ) * a = a + a :=
      RatQ.eqQ_of_norm_eq [a] (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) (by decide)
    rw [hid, hsum]
  cases RatQ.mul_eq_zero h2 with
  | inl h2z => exact False.elim (RatQ.two_ne_zero h2z)
  | inr hz => exact hz

private theorem cl2_mul_smul_right {q1 q2 : RatQ} (r : RatQ) (x y : Cl2 q1 q2) :
    Cl2.mul x (Cl2.smul r y) = Cl2.smul r (Cl2.mul x y) := by
  let env := [r, q1, q2, x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12]
  let pr := PExpr.var 0; let pq1 := PExpr.var 1; let pq2 := PExpr.var 2
  let ax0 := PExpr.var 3; let ax1 := PExpr.var 4; let ax2 := PExpr.var 5; let ax3 := PExpr.var 6
  let by0 := PExpr.var 7; let by1 := PExpr.var 8; let by2 := PExpr.var 9; let by3 := PExpr.var 10
  refine Cl2.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul ax0 (.mul pr by0)) (.mul (.mul pq1 ax1) (.mul pr by1)))
                  (.mul (.mul pq2 ax2) (.mul pr by2)))
            (.mul (.mul (.mul pq1 pq2) ax3) (.mul pr by3)))
      (.mul pr (.sub (.add (.add (.mul ax0 by0) (.mul (.mul pq1 ax1) by1))
                           (.mul (.mul pq2 ax2) by2))
                     (.mul (.mul (.mul pq1 pq2) ax3) by3))) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul ax0 (.mul pr by1)) (.mul ax1 (.mul pr by0)))
                  (.mul (.mul pq2 ax2) (.mul pr by3)))
            (.mul (.mul pq2 ax3) (.mul pr by2)))
      (.mul pr (.add (.sub (.add (.mul ax0 by1) (.mul ax1 by0)) (.mul (.mul pq2 ax2) by3))
                     (.mul (.mul pq2 ax3) by2))) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul ax0 (.mul pr by2)) (.mul (.mul pq1 ax1) (.mul pr by3)))
                  (.mul ax2 (.mul pr by0)))
            (.mul (.mul pq1 ax3) (.mul pr by1)))
      (.mul pr (.sub (.add (.add (.mul ax0 by2) (.mul (.mul pq1 ax1) by3)) (.mul ax2 by0))
                     (.mul (.mul pq1 ax3) by1))) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul ax0 (.mul pr by3)) (.mul ax1 (.mul pr by2)))
                  (.mul ax2 (.mul pr by1)))
            (.mul ax3 (.mul pr by0)))
      (.mul pr (.add (.sub (.add (.mul ax0 by3) (.mul ax1 by2)) (.mul ax2 by1)) (.mul ax3 by0))) (by decide)

/-! ### Regime I: Odd Dimensions (`n = 2m + 1`) and `Cl_{1,0}(ℚ) ≅ ℚ × ℚ` (`n = 1`) -/

/-- Universal odd-dimension obstruction: for every odd dimension `n = 2m + 1`, no subspace `S`
    of any `ℚ`-algebra can have integer dimension `d` satisfying `d^2 = 2^n` (`d = 2^(n/2)`). -/
theorem odd_dim_no_half_pow_two {A : Type} (alg : QAlgebra A) (S : A → Prop) (m d : Nat)
    (_hd : HasQDim alg S d) : d * d ≠ 2 ^ (2 * m + 1) :=
  odd_pow_two_not_nat_sq m d

abbrev Cl10Q := Cl1 1
def Cl10Alg : QAlgebra Cl10Q := Cl1.alg 1

namespace Cl10

def ePlus  : Cl10Q := ⟨RatQ.half, RatQ.half⟩
def eMinus : Cl10Q := ⟨RatQ.half, -RatQ.half⟩

def SPlus  (x : Cl10Q) : Prop := x.a0 = x.a1
def SMinus (x : Cl10Q) : Prop := x.a0 = -x.a1

instance (x : Cl10Q) : Decidable (SPlus x) :=
  inferInstanceAs (Decidable (x.a0 = x.a1))

instance (x : Cl10Q) : Decidable (SMinus x) :=
  inferInstanceAs (Decidable (x.a0 = -x.a1))

theorem ePlus_idem  : Cl10Alg.IsIdempotent ePlus  := ⟨by decide, by decide⟩
theorem eMinus_idem : Cl10Alg.IsIdempotent eMinus := ⟨by decide, by decide⟩
theorem orth_plus_minus : Cl10Alg.mul ePlus eMinus = Cl10Alg.zero := by decide
theorem orth_minus_plus : Cl10Alg.mul eMinus ePlus = Cl10Alg.zero := by decide

theorem sPlus_isLeftIdeal : Cl10Alg.IsLeftIdeal SPlus := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x y hx hy
    show x.a0 + y.a0 = x.a1 + y.a1
    rw [hx, hy]
  · intro r x hx
    show r * x.a0 = r * x.a1
    rw [hx]
  · intro a x hx
    show a.a0 * x.a0 + 1 * a.a1 * x.a1 = a.a0 * x.a1 + a.a1 * x.a0
    rw [hx]
    exact RatQ.eqQ_of_norm_eq [a.a0, a.a1, x.a1]
      (.add (.mul (.var 0) (.var 2)) (.mul (.mul (.const 1) (.var 1)) (.var 2)))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) (by decide)

theorem sMinus_isLeftIdeal : Cl10Alg.IsLeftIdeal SMinus := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro x y hx hy
    show x.a0 + y.a0 = -(x.a1 + y.a1)
    rw [hx, hy]
    exact RatQ.eqQ_of_norm_eq [x.a1, y.a1]
      (.add (.neg (.var 0)) (.neg (.var 1))) (.neg (.add (.var 0) (.var 1))) (by decide)
  · intro r x hx
    show r * x.a0 = -(r * x.a1)
    rw [hx]
    exact RatQ.eqQ_of_norm_eq [r, x.a1]
      (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1))) (by decide)
  · intro a x hx
    show a.a0 * x.a0 + 1 * a.a1 * x.a1 = -(a.a0 * x.a1 + a.a1 * x.a0)
    rw [hx]
    exact RatQ.eqQ_of_norm_eq [a.a0, a.a1, x.a1]
      (.add (.mul (.var 0) (.neg (.var 2))) (.mul (.mul (.const 1) (.var 1)) (.var 2)))
      (.neg (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.neg (.var 2))))) (by decide)

theorem eq_smul_ePlus_of_sPlus {x : Cl10Q} (hx : SPlus x) :
    x = Cl10Alg.smul ((2 : RatQ) * x.a0) ePlus := by
  apply Cl1.ext
  · show x.a0 = ((2 : RatQ) * x.a0) * RatQ.half
    rw [RatQ.mul_comm (2 : RatQ) x.a0, RatQ.mul_assoc, RatQ.two_mul_half, RatQ.mul_one]
  · show x.a1 = ((2 : RatQ) * x.a0) * RatQ.half
    rw [← hx, RatQ.mul_comm (2 : RatQ) x.a0, RatQ.mul_assoc, RatQ.two_mul_half, RatQ.mul_one]

theorem eq_smul_eMinus_of_sMinus {x : Cl10Q} (hx : SMinus x) :
    x = Cl10Alg.smul ((2 : RatQ) * x.a0) eMinus := by
  have hx1 : x.a1 = -x.a0 := by
    have h : -x.a0 = -(-x.a1) := by rw [hx]
    have hnn : -(-x.a1) = x.a1 :=
      RatQ.eqQ_of_norm_eq [x.a1] (.neg (.neg (.var 0))) (.var 0) (by decide)
    rw [hnn] at h
    exact h.symm
  apply Cl1.ext
  · show x.a0 = ((2 : RatQ) * x.a0) * RatQ.half
    rw [RatQ.mul_comm (2 : RatQ) x.a0, RatQ.mul_assoc, RatQ.two_mul_half, RatQ.mul_one]
  · show x.a1 = ((2 : RatQ) * x.a0) * (-RatQ.half)
    rw [hx1]
    have hid : ((2 : RatQ) * x.a0) * (-RatQ.half) = -(x.a0 * ((2 : RatQ) * RatQ.half)) :=
      RatQ.eqQ_of_norm_eq [x.a0, RatQ.half]
        (.mul (.mul (.const 2) (.var 0)) (.neg (.var 1)))
        (.neg (.mul (.var 0) (.mul (.const 2) (.var 1)))) (by decide)
    rw [hid, RatQ.two_mul_half, RatQ.mul_one]

theorem sPlus_isMinimalLeftIdeal : Cl10Alg.IsMinimalLeftIdeal SPlus := by
  refine ⟨sPlus_isLeftIdeal, ⟨ePlus, rfl, by decide⟩, ?_⟩
  intro I hI hsub
  by_cases hall0 : ∀ x, I x → x = Cl10Alg.zero
  · exact .inl hall0
  · right
    have hex : ∃ y, I y ∧ y ≠ Cl10Alg.zero := by
      apply Classical.byContradiction
      intro hno
      apply hall0
      intro x hxI
      apply Classical.byContradiction
      intro hxz
      exact hno ⟨x, hxI, hxz⟩
    rcases hex with ⟨y, hyI, hynz⟩
    have hyS : y.a0 = y.a1 := hsub y hyI
    have hy0_nz : y.a0 ≠ 0 := by
      intro h0
      exact hynz (Cl1.ext h0 (hyS.symm.trans h0))
    let c := (2 : RatQ) * y.a0
    have hc_nz : c ≠ 0 := by
      intro h20
      cases RatQ.mul_eq_zero h20 with
      | inl h2 => exact RatQ.two_ne_zero h2
      | inr hy0 => exact hy0_nz hy0
    have hePlus_in_I : I ePlus := by
      have hy_eq : y = Cl10Alg.smul c ePlus := eq_smul_ePlus_of_sPlus hyS
      have hsmul := hI.2.2.1 c⁻¹ y hyI
      rw [hy_eq, ← Cl10Alg.mul_smul, RatQ.inv_mul_cancel hc_nz, Cl10Alg.one_smul] at hsmul
      exact hsmul
    intro z hz
    rw [eq_smul_ePlus_of_sPlus hz]
    exact hI.2.2.1 ((2 : RatQ) * z.a0) ePlus hePlus_in_I

theorem sMinus_isMinimalLeftIdeal : Cl10Alg.IsMinimalLeftIdeal SMinus := by
  refine ⟨sMinus_isLeftIdeal, ⟨eMinus, by decide, by decide⟩, ?_⟩
  intro I hI hsub
  by_cases hall0 : ∀ x, I x → x = Cl10Alg.zero
  · exact .inl hall0
  · right
    have hex : ∃ y, I y ∧ y ≠ Cl10Alg.zero := by
      apply Classical.byContradiction
      intro hno
      apply hall0
      intro x hxI
      apply Classical.byContradiction
      intro hxz
      exact hno ⟨x, hxI, hxz⟩
    rcases hex with ⟨y, hyI, hynz⟩
    have hyS : y.a0 = -y.a1 := hsub y hyI
    have hy0_nz : y.a0 ≠ 0 := by
      intro h0
      have hy1 : y.a1 = 0 := by
        have h : -y.a1 = 0 := hyS.symm.trans h0
        have h2 : -(-y.a1) = -0 := by rw [h]
        have hnn : -(-y.a1) = y.a1 :=
          RatQ.eqQ_of_norm_eq [y.a1] (.neg (.neg (.var 0))) (.var 0) (by decide)
        have hz0 : (-0 : RatQ) = 0 := by decide
        rw [hnn, hz0] at h2
        exact h2
      exact hynz (Cl1.ext h0 hy1)
    let c := (2 : RatQ) * y.a0
    have hc_nz : c ≠ 0 := by
      intro h20
      cases RatQ.mul_eq_zero h20 with
      | inl h2 => exact RatQ.two_ne_zero h2
      | inr hy0 => exact hy0_nz hy0
    have heMinus_in_I : I eMinus := by
      have hy_eq : y = Cl10Alg.smul c eMinus := eq_smul_eMinus_of_sMinus hyS
      have hsmul := hI.2.2.1 c⁻¹ y hyI
      rw [hy_eq, ← Cl10Alg.mul_smul, RatQ.inv_mul_cancel hc_nz, Cl10Alg.one_smul] at hsmul
      exact hsmul
    intro z hz
    rw [eq_smul_eMinus_of_sMinus hz]
    exact hI.2.2.1 ((2 : RatQ) * z.a0) eMinus heMinus_in_I

/-- Complete classification of minimal nonzero left ideals of `Cl_{1,0}(ℚ)`:
    every minimal left ideal is either `S_+` or `S_-`. -/
theorem minimalLeftIdeal_iff (S : Cl10Q → Prop) :
    Cl10Alg.IsMinimalLeftIdeal S ↔ (∀ x, S x ↔ SPlus x) ∨ (∀ x, S x ↔ SMinus x) := by
  constructor
  · rintro ⟨hL, ⟨y, hyS, hynz⟩, hmin⟩
    by_cases hsum : y.a0 + y.a1 = 0
    · right
      have hyM : SMinus y := by
        apply RatQ.sub_eq_zero_iff.mp
        rw [RatQ.sub_eq_add_neg]
        have hnn : -(-y.a1) = y.a1 :=
          RatQ.eqQ_of_norm_eq [y.a1] (.neg (.neg (.var 0))) (.var 0) (by decide)
        rw [hnn]
        exact hsum
      have hy0_nz : y.a0 ≠ 0 := by
        intro h0
        have hy1 : y.a1 = 0 := by
          rw [h0, RatQ.zero_add] at hsum; exact hsum
        exact hynz (Cl1.ext h0 hy1)
      let c := (2 : RatQ) * y.a0
      have hc_nz : c ≠ 0 := by
        intro h20
        cases RatQ.mul_eq_zero h20 with
        | inl h2 => exact RatQ.two_ne_zero h2
        | inr h0 => exact hy0_nz h0
      have heM_in_S : S eMinus := by
        have hy_eq : y = Cl10Alg.smul c eMinus := eq_smul_eMinus_of_sMinus hyM
        have hsmul := hL.2.2.1 c⁻¹ y hyS
        rw [hy_eq, ← Cl10Alg.mul_smul,
            RatQ.inv_mul_cancel hc_nz, Cl10Alg.one_smul] at hsmul
        exact hsmul
      have hsubM : ∀ x, SMinus x → S x := by
        intro x hxM
        rw [eq_smul_eMinus_of_sMinus hxM]
        exact hL.2.2.1 _ eMinus heM_in_S
      cases hmin SMinus sMinus_isLeftIdeal hsubM with
      | inl hall0 =>
        exact False.elim (eMinus_idem.2 (hall0 eMinus (by decide)))
      | inr hsup =>
        exact fun x => ⟨hsup x, hsubM x⟩
    · left
      have hmul : Cl10Alg.mul ePlus y = Cl10Alg.smul (y.a0 + y.a1) ePlus := by
        apply Cl1.ext
        · exact RatQ.eqQ_of_norm_eq [RatQ.half, y.a0, y.a1]
            (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 1) (.var 0)) (.var 2)))
            (.mul (.add (.var 1) (.var 2)) (.var 0)) (by decide)
        · exact RatQ.eqQ_of_norm_eq [RatQ.half, y.a0, y.a1]
            (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 1)))
            (.mul (.add (.var 1) (.var 2)) (.var 0)) (by decide)
      have heP_in_S : S ePlus := by
        have hp := hL.2.2.2 ePlus y hyS
        rw [hmul] at hp
        have hsm := hL.2.2.1 (y.a0 + y.a1)⁻¹ _ hp
        rw [← Cl10Alg.mul_smul, RatQ.inv_mul_cancel hsum, Cl10Alg.one_smul] at hsm
        exact hsm
      have hsubP : ∀ x, SPlus x → S x := by
        intro x hxP
        rw [eq_smul_ePlus_of_sPlus hxP]
        exact hL.2.2.1 _ ePlus heP_in_S
      cases hmin SPlus sPlus_isLeftIdeal hsubP with
      | inl hall0 =>
        exact False.elim (ePlus_idem.2 (hall0 ePlus rfl))
      | inr hsup =>
        exact fun x => ⟨hsup x, hsubP x⟩
  · intro hor
    cases hor with
    | inl hP =>
      have hEq : S = SPlus := funext (fun x => propext (hP x))
      rw [hEq]
      exact sPlus_isMinimalLeftIdeal
    | inr hM =>
      have hEq : S = SMinus := funext (fun x => propext (hM x))
      rw [hEq]
      exact sMinus_isMinimalLeftIdeal

theorem sPlus_hasDim_one : HasQDim Cl10Alg SPlus 1 := by
  refine ⟨{
    toVec := fun x _ _ => x.a0
    ofVec := fun v => ⟨v ⟨0, by decide⟩, v ⟨0, by decide⟩⟩
    ofVec_mem := fun _ => rfl
    left_inv := fun x hx => Cl1.ext rfl hx
    right_inv := fun v => by funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl
    ofVec_add := fun _ _ => rfl
    ofVec_smul := fun _ _ => rfl
  }⟩

theorem sMinus_hasDim_one : HasQDim Cl10Alg SMinus 1 := by
  refine ⟨{
    toVec := fun x _ _ => x.a0
    ofVec := fun v => ⟨v ⟨0, by decide⟩, -(v ⟨0, by decide⟩)⟩
    ofVec_mem := fun v =>
      RatQ.eqQ_of_norm_eq [v ⟨0, by decide⟩] (.var 0) (.neg (.neg (.var 0))) (by decide)
    left_inv := fun x hx => by
      have hx1 : -x.a0 = x.a1 := by
        rw [hx]
        exact RatQ.eqQ_of_norm_eq [x.a1] (.neg (.neg (.var 0))) (.var 0) (by decide)
      exact Cl1.ext rfl hx1
    right_inv := fun v => by funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl
    ofVec_add := fun u v => by
      refine Cl1.ext rfl ?_
      exact RatQ.eqQ_of_norm_eq [u ⟨0, by decide⟩, v ⟨0, by decide⟩]
        (.neg (.add (.var 0) (.var 1))) (.add (.neg (.var 0)) (.neg (.var 1))) (by decide)
    ofVec_smul := fun r v => by
      refine Cl1.ext rfl ?_
      exact RatQ.eqQ_of_norm_eq [r, v ⟨0, by decide⟩]
        (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.neg (.var 1))) (by decide)
  }⟩

/-- Master Refutation I (`n = 1`, `Cl_{1,0}(ℚ)`): EVERY minimal nonzero left ideal `S`
    has dimension `1` (`¬ dim 2`, and `d^2 ≠ 2^1` for any `d`), is NOT faithful,
    and cannot realize both `+1` and `-1` eigenvalues of `e_1`. -/
theorem refutation_cl10 (S : Cl10Q → Prop) (hS : Cl10Alg.IsMinimalLeftIdeal S) :
    HasQDim Cl10Alg S 1 ∧
    ¬ HasQDim Cl10Alg S 2 ∧
    (∀ d, HasQDim Cl10Alg S d → d * d ≠ 2 ^ 1) ∧
    ¬ Cl10Alg.IsFaithfulLeftIdeal S ∧
    ¬ ((∃ u, S u ∧ u ≠ Cl10Alg.zero ∧ Cl10Alg.mul (Cl1.e1 1) u = u) ∧
       (∃ v, S v ∧ v ≠ Cl10Alg.zero ∧ Cl10Alg.mul (Cl1.e1 1) v = Cl10Alg.neg v)) := by
  cases (minimalLeftIdeal_iff S).mp hS with
  | inl hP =>
    have hEq : S = SPlus := funext (fun x => propext (hP x))
    subst hEq
    refine ⟨sPlus_hasDim_one, dim_one_not_dim_two sPlus_hasDim_one,
            fun d hd => odd_dim_no_half_pow_two Cl10Alg SPlus 0 d hd, ?_, ?_⟩
    · intro hfaith
      have hann : ∀ x, SPlus x → Cl10Alg.mul eMinus x = Cl10Alg.zero := by
        intro x hx
        rw [eq_smul_ePlus_of_sPlus hx]
        have hcomm : Cl10Alg.mul eMinus (Cl10Alg.smul ((2 : RatQ) * x.a0) ePlus) =
            Cl10Alg.smul ((2 : RatQ) * x.a0) (Cl10Alg.mul eMinus ePlus) := by
          apply Cl1.ext
          · exact RatQ.eqQ_of_norm_eq [RatQ.half, x.a0]
              (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 0)))
                    (.mul (.mul (.const 1) (.neg (.var 0))) (.mul (.mul (.const 2) (.var 1)) (.var 0))))
              (.mul (.mul (.const 2) (.var 1))
                    (.add (.mul (.var 0) (.var 0)) (.mul (.mul (.const 1) (.neg (.var 0))) (.var 0)))) (by decide)
          · exact RatQ.eqQ_of_norm_eq [RatQ.half, x.a0]
              (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 0)))
                    (.mul (.neg (.var 0)) (.mul (.mul (.const 2) (.var 1)) (.var 0))))
              (.mul (.mul (.const 2) (.var 1))
                    (.add (.mul (.var 0) (.var 0)) (.mul (.neg (.var 0)) (.var 0)))) (by decide)
        rw [hcomm, orth_minus_plus, Cl10Alg.smul_zero]
      exact eMinus_idem.2 (hfaith eMinus hann)
    · rintro ⟨_, ⟨v, hvP, hvnz, hv_neg⟩⟩
      have hv_pos : Cl10Alg.mul (Cl1.e1 1) v = v := by
        apply Cl1.ext
        · show 0 * v.a0 + 1 * 1 * v.a1 = v.a0
          rw [← hvP]
          exact RatQ.eqQ_of_norm_eq [v.a0]
            (.add (.mul (.const 0) (.var 0)) (.mul (.mul (.const 1) (.const 1)) (.var 0))) (.var 0) (by decide)
        · show 0 * v.a1 + 1 * v.a0 = v.a1
          rw [hvP]
          exact RatQ.eqQ_of_norm_eq [v.a1]
            (.add (.mul (.const 0) (.var 0)) (.mul (.const 1) (.var 0))) (.var 0) (by decide)
      rw [hv_pos] at hv_neg
      have hv0 : v.a0 = 0 := eq_zero_of_eq_neg (congrArg Cl1.a0 hv_neg)
      exact hvnz (Cl1.ext hv0 (hvP.symm.trans hv0))
  | inr hM =>
    have hEq : S = SMinus := funext (fun x => propext (hM x))
    subst hEq
    refine ⟨sMinus_hasDim_one, dim_one_not_dim_two sMinus_hasDim_one,
            fun d hd => odd_dim_no_half_pow_two Cl10Alg SMinus 0 d hd, ?_, ?_⟩
    · intro hfaith
      have hann : ∀ x, SMinus x → Cl10Alg.mul ePlus x = Cl10Alg.zero := by
        intro x hx
        rw [eq_smul_eMinus_of_sMinus hx]
        have hcomm : Cl10Alg.mul ePlus (Cl10Alg.smul ((2 : RatQ) * x.a0) eMinus) =
            Cl10Alg.smul ((2 : RatQ) * x.a0) (Cl10Alg.mul ePlus eMinus) := by
          apply Cl1.ext
          · exact RatQ.eqQ_of_norm_eq [RatQ.half, x.a0]
              (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 0)))
                    (.mul (.mul (.const 1) (.var 0)) (.mul (.mul (.const 2) (.var 1)) (.neg (.var 0)))))
              (.mul (.mul (.const 2) (.var 1))
                    (.add (.mul (.var 0) (.var 0)) (.mul (.mul (.const 1) (.var 0)) (.neg (.var 0))))) (by decide)
          · exact RatQ.eqQ_of_norm_eq [RatQ.half, x.a0]
              (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.neg (.var 0))))
                    (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 0))))
              (.mul (.mul (.const 2) (.var 1))
                    (.add (.mul (.var 0) (.neg (.var 0))) (.mul (.var 0) (.var 0)))) (by decide)
        rw [hcomm, orth_plus_minus, Cl10Alg.smul_zero]
      exact ePlus_idem.2 (hfaith ePlus hann)
    · rintro ⟨⟨u, huM, hunz, hu_pos⟩, _⟩
      have hu_neg : Cl10Alg.mul (Cl1.e1 1) u = Cl10Alg.neg u := by
        apply Cl1.ext
        · show 0 * u.a0 + 1 * 1 * u.a1 = -u.a0
          rw [huM]
          exact RatQ.eqQ_of_norm_eq [u.a1]
            (.add (.mul (.const 0) (.neg (.var 0))) (.mul (.mul (.const 1) (.const 1)) (.var 0)))
            (.neg (.neg (.var 0))) (by decide)
        · show 0 * u.a1 + 1 * u.a0 = -u.a1
          rw [huM]
          exact RatQ.eqQ_of_norm_eq [u.a1]
            (.add (.mul (.const 0) (.var 0)) (.mul (.const 1) (.neg (.var 0)))) (.neg (.var 0)) (by decide)
      rw [hu_neg] at hu_pos
      have hu0 : u.a0 = 0 := eq_zero_of_eq_neg (congrArg Cl1.a0 hu_pos).symm
      have hu1 : u.a1 = 0 := by
        have h : -u.a1 = 0 := huM.symm.trans hu0
        have h2 : -(-u.a1) = -0 := by rw [h]
        have hnn : -(-u.a1) = u.a1 :=
          RatQ.eqQ_of_norm_eq [u.a1] (.neg (.neg (.var 0))) (.var 0) (by decide)
        have hz0 : (-0 : RatQ) = 0 := by decide
        rw [hnn, hz0] at h2
        exact h2
      exact hunz (Cl1.ext hu0 hu1)

end Cl10

/-! ### Regime II: Even-Dimensional Division-Algebra Obstruction (`Cl_{0,2}(ℚ) ≅ ℍ_ℚ`, `n = 2`) -/

abbrev Cl02Q := Cl2 (-1) (-1)
def Cl02Alg : QAlgebra Cl02Q := Cl2.alg (-1) (-1)

namespace Cl02

def conj (q : Cl02Q) : Cl02Q :=
  ⟨q.a0, -q.a1, -q.a2, -q.a12⟩

def normSq (q : Cl02Q) : RatQ :=
  q.a0 * q.a0 + q.a1 * q.a1 + q.a2 * q.a2 + q.a12 * q.a12

theorem mul_conj (q : Cl02Q) :
    Cl02Alg.mul q (conj q) = Cl02Alg.smul (normSq q) Cl02Alg.one := by
  let env := [q.a0, q.a1, q.a2, q.a12]
  let m1 := PExpr.neg (.const 1)
  refine Cl2.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul (.var 0) (.var 0))
                        (.mul (.mul m1 (.var 1)) (.neg (.var 1))))
                  (.mul (.mul m1 (.var 2)) (.neg (.var 2))))
            (.mul (.mul (.mul m1 m1) (.var 3)) (.neg (.var 3))))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 1)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.var 0)))
                  (.mul (.mul m1 (.var 2)) (.neg (.var 3))))
            (.mul (.mul m1 (.var 3)) (.neg (.var 2))))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul (.var 0) (.neg (.var 2)))
                        (.mul (.mul m1 (.var 1)) (.neg (.var 3))))
                  (.mul (.var 2) (.var 0)))
            (.mul (.mul m1 (.var 3)) (.neg (.var 1))))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul (.var 0) (.neg (.var 3))) (.mul (.var 1) (.neg (.var 2))))
                  (.mul (.var 2) (.neg (.var 1))))
            (.mul (.var 3) (.var 0)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)

theorem conj_mul (q : Cl02Q) :
    Cl02Alg.mul (conj q) q = Cl02Alg.smul (normSq q) Cl02Alg.one := by
  let env := [q.a0, q.a1, q.a2, q.a12]
  let m1 := PExpr.neg (.const 1)
  refine Cl2.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul (.var 0) (.var 0))
                        (.mul (.mul m1 (.neg (.var 1))) (.var 1)))
                  (.mul (.mul m1 (.neg (.var 2))) (.var 2)))
            (.mul (.mul (.mul m1 m1) (.neg (.var 3))) (.var 3)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 1)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0)))
                  (.mul (.mul m1 (.neg (.var 2))) (.var 3)))
            (.mul (.mul m1 (.neg (.var 3))) (.var 2)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.sub (.add (.add (.mul (.var 0) (.var 2))
                        (.mul (.mul m1 (.neg (.var 1))) (.var 3)))
                  (.mul (.neg (.var 2)) (.var 0)))
            (.mul (.mul m1 (.neg (.var 3))) (.var 1)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (.add (.sub (.add (.mul (.var 0) (.var 3)) (.mul (.neg (.var 1)) (.var 2)))
                  (.mul (.neg (.var 2)) (.var 1)))
            (.mul (.neg (.var 3)) (.var 0)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                        (.mul (.var 2) (.var 2)))
                  (.mul (.var 3) (.var 3))) (.const 0)) (by decide)

theorem normSq_ne_zero {q : Cl02Q} (hq : q ≠ Cl02Alg.zero) : normSq q ≠ 0 := by
  intro h0
  have ⟨ha0, ha1, ha2, ha12⟩ := RatQ.four_squares_eq_zero q.a0 q.a1 q.a2 q.a12 h0
  exact hq (Cl2.ext ha0 ha1 ha2 ha12)

/-- Explicit multiplicative inverse in the quaternion Clifford algebra `Cl_{0,2}(ℚ)`. -/
def qinv (q : Cl02Q) : Cl02Q :=
  Cl02Alg.smul (normSq q)⁻¹ (conj q)

theorem mul_qinv {q : Cl02Q} (hq : q ≠ Cl02Alg.zero) :
    Cl02Alg.mul q (qinv q) = Cl02Alg.one := by
  unfold qinv
  change Cl2.mul q (Cl2.smul (normSq q)⁻¹ (conj q)) = Cl02Alg.one
  rw [cl2_mul_smul_right]
  change Cl02Alg.smul (normSq q)⁻¹ (Cl02Alg.mul q (conj q)) = Cl02Alg.one
  rw [mul_conj, ← Cl02Alg.mul_smul, RatQ.inv_mul_cancel (normSq_ne_zero hq), Cl02Alg.one_smul]

theorem qinv_mul {q : Cl02Q} (hq : q ≠ Cl02Alg.zero) :
    Cl02Alg.mul (qinv q) q = Cl02Alg.one := by
  unfold qinv
  rw [Cl02Alg.smul_mul_left, conj_mul, ← Cl02Alg.mul_smul,
      RatQ.inv_mul_cancel (normSq_ne_zero hq), Cl02Alg.one_smul]

/-- In `Cl_{0,2}(ℚ) ≅ ℍ_ℚ`, only `0` and `1` are idempotents (no proper primitive idempotents!). -/
theorem idempotent_trivial (e : Cl02Q) (he : Cl02Alg.mul e e = e) :
    e = Cl02Alg.zero ∨ e = Cl02Alg.one := by
  by_cases hz : e = Cl02Alg.zero
  · exact .inl hz
  · right
    have hmul : Cl02Alg.mul (qinv e) (Cl02Alg.mul e e) = Cl02Alg.mul (qinv e) e := by rw [he]
    rw [← Cl02Alg.mul_assoc, qinv_mul hz, Cl02Alg.one_mul] at hmul
    exact hmul

/-- Every nonzero left ideal of `Cl_{0,2}(ℚ)` is the entire 4-dimensional algebra. -/
theorem leftIdeal_eq_top_of_nonzero (I : Cl02Q → Prop) (hI : Cl02Alg.IsLeftIdeal I)
    {q : Cl02Q} (hqI : I q) (hqnz : q ≠ Cl02Alg.zero) : ∀ x, I x := by
  intro x
  have h1 : I (Cl02Alg.mul (Cl02Alg.mul x (qinv q)) q) := hI.2.2.2 (Cl02Alg.mul x (qinv q)) q hqI
  rw [Cl02Alg.mul_assoc, qinv_mul hqnz, Cl02Alg.mul_one] at h1
  exact h1

def FullCl02 (_ : Cl02Q) : Prop := True

theorem fullCl02_isMinimalLeftIdeal : Cl02Alg.IsMinimalLeftIdeal FullCl02 := by
  refine ⟨⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => trivial⟩,
          ⟨Cl02Alg.one, trivial, by decide⟩, ?_⟩
  intro I hI _
  by_cases hall0 : ∀ x, I x → x = Cl02Alg.zero
  · exact .inl hall0
  · right
    have hex : ∃ q, I q ∧ q ≠ Cl02Alg.zero := by
      apply Classical.byContradiction
      intro hno
      apply hall0
      intro x hxI
      apply Classical.byContradiction
      intro hxz
      exact hno ⟨x, hxI, hxz⟩
    rcases hex with ⟨q, hqI, hqnz⟩
    intro x _
    exact leftIdeal_eq_top_of_nonzero I hI hqI hqnz x

/-- Complete classification of minimal nonzero left ideals of `Cl_{0,2}(ℚ) ≅ ℍ_ℚ`:
    the unique minimal nonzero left ideal is the full 4-dimensional algebra itself! -/
theorem minimalLeftIdeal_iff (S : Cl02Q → Prop) :
    Cl02Alg.IsMinimalLeftIdeal S ↔ ∀ x, S x := by
  constructor
  · rintro ⟨hL, ⟨q, hqS, hqnz⟩, _⟩
    exact leftIdeal_eq_top_of_nonzero S hL hqS hqnz
  · intro hall
    have hEq : S = FullCl02 := funext (fun x => propext ⟨fun _ => trivial, fun _ => hall x⟩)
    rw [hEq]
    exact fullCl02_isMinimalLeftIdeal

theorem fullCl02_hasDim_four : HasQDim Cl02Alg FullCl02 4 := by
  refine ⟨{
    toVec := fun x _ ⟨i, hi⟩ =>
      match i, hi with
      | 0, _ => x.a0
      | 1, _ => x.a1
      | 2, _ => x.a2
      | 3, _ => x.a12
    ofVec := fun v => ⟨v ⟨0, by decide⟩, v ⟨1, by decide⟩, v ⟨2, by decide⟩, v ⟨3, by decide⟩⟩
    ofVec_mem := fun _ => trivial
    left_inv := fun x _ => by cases x; rfl
    right_inv := fun v => by
      funext ⟨i, hi⟩
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
    ofVec_add := fun _ _ => rfl
    ofVec_smul := fun _ _ => rfl
  }⟩

/-- Master Refutation II (`n = 2` EVEN, nondegenerate `Cl_{0,2}(ℚ) ≅ ℍ_ℚ`):
    EVERY minimal nonzero left ideal `S` has dimension `4`, does NOT have dimension `2 = 2^(2/2)`,
    contains no proper idempotents, and admits NO rational eigenvalues for `e_1`. -/
theorem refutation_cl02 (S : Cl02Q → Prop) (hS : Cl02Alg.IsMinimalLeftIdeal S) :
    HasQDim Cl02Alg S 4 ∧
    ¬ HasQDim Cl02Alg S (2 ^ (2 / 2)) ∧
    (∀ e, Cl02Alg.mul e e = e → e = Cl02Alg.zero ∨ e = Cl02Alg.one) ∧
    (∀ (v : Cl02Q) (lam : RatQ), S v → v ≠ Cl02Alg.zero →
      Cl02Alg.mul (Cl2.e1 (-1) (-1)) v ≠ Cl02Alg.smul lam v) := by
  have hall := (minimalLeftIdeal_iff S).mp hS
  have hEq : S = FullCl02 := funext (fun x => propext ⟨fun _ => trivial, fun _ => hall x⟩)
  subst hEq
  refine ⟨fullCl02_hasDim_four, dim_four_not_dim_two fullCl02_hasDim_four, idempotent_trivial, ?_⟩
  intro v lam _ hvnz heig
  let iGen := Cl2.e1 (-1) (-1)
  have hstep1 : Cl02Alg.mul iGen (Cl02Alg.mul iGen v) = Cl02Alg.smul (lam * lam) v := by
    rw [heig]
    change Cl2.mul iGen (Cl2.smul lam v) = Cl02Alg.smul (lam * lam) v
    rw [cl2_mul_smul_right]
    change Cl02Alg.smul lam (Cl02Alg.mul iGen v) = Cl02Alg.smul (lam * lam) v
    rw [heig, ← Cl02Alg.mul_smul]
  have hstep2 : Cl02Alg.mul iGen iGen = Cl02Alg.smul (lam * lam) Cl02Alg.one := by
    rw [← Cl02Alg.mul_assoc] at hstep1
    have hr : Cl02Alg.mul (Cl02Alg.mul (Cl02Alg.mul iGen iGen) v) (qinv v) =
              Cl02Alg.mul (Cl02Alg.smul (lam * lam) v) (qinv v) :=
      congrArg (fun t => Cl02Alg.mul t (qinv v)) hstep1
    rw [Cl02Alg.mul_assoc, mul_qinv hvnz, Cl02Alg.mul_one,
        Cl02Alg.smul_mul_left, mul_qinv hvnz] at hr
    exact hr
  have hi_sq : (Cl02Alg.mul iGen iGen).a0 = -1 := by decide
  have hrhs_a0 : (Cl02Alg.smul (lam * lam) Cl02Alg.one).a0 = lam * lam := by
    show (lam * lam) * 1 = lam * lam
    exact RatQ.mul_one (lam * lam)
  have hlam_sq : lam * lam = -1 := by
    have h0 := congrArg Cl2.a0 hstep2
    rw [hi_sq, hrhs_a0] at h0
    exact h0.symm
  have hzero : lam * lam + 1 = 0 := by
    rw [hlam_sq]
    decide
  exact RatQ.sq_add_one_ne_zero lam hzero

end Cl02

/-! ### Regime III: Degenerate Quadratic Form (`Q = 0`), Exterior Algebra `Λ(ℚ^2) = Cl2 0 0` (`n = 2`) -/

abbrev Ext2Q := Cl2 0 0
def Ext2Alg : QAlgebra Ext2Q := Cl2.alg 0 0

namespace Ext2

/-- Top-degree exterior line `Λ^2(ℚ^2) = ℚ · e_{12}` (unique minimal nonzero left ideal). -/
def TopSocle (x : Ext2Q) : Prop :=
  x.a0 = 0 ∧ x.a1 = 0 ∧ x.a2 = 0

theorem eq_smul_e12_of_topSocle {x : Ext2Q} (hx : TopSocle x) :
    x = Ext2Alg.smul x.a12 (Cl2.e12 0 0) := by
  rcases hx with ⟨h0, h1, h2⟩
  refine Cl2.ext ?_ ?_ ?_ ?_
  · show x.a0 = x.a12 * 0; rw [h0, RatQ.mul_zero]
  · show x.a1 = x.a12 * 0; rw [h1, RatQ.mul_zero]
  · show x.a2 = x.a12 * 0; rw [h2, RatQ.mul_zero]
  · show x.a12 = x.a12 * 1; rw [RatQ.mul_one]

theorem topSocle_isLeftIdeal : Ext2Alg.IsLeftIdeal TopSocle := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    refine ⟨?_, ?_, ?_⟩
    · show x.a0 + y.a0 = 0; rw [hx0, hy0, RatQ.add_zero]
    · show x.a1 + y.a1 = 0; rw [hx1, hy1, RatQ.add_zero]
    · show x.a2 + y.a2 = 0; rw [hx2, hy2, RatQ.add_zero]
  · rintro r x ⟨hx0, hx1, hx2⟩
    refine ⟨?_, ?_, ?_⟩
    · show r * x.a0 = 0; rw [hx0, RatQ.mul_zero]
    · show r * x.a1 = 0; rw [hx1, RatQ.mul_zero]
    · show r * x.a2 = 0; rw [hx2, RatQ.mul_zero]
  · rintro a x ⟨hx0, hx1, hx2⟩
    refine ⟨?_, ?_, ?_⟩
    · show a.a0 * x.a0 + 0 * a.a1 * x.a1 + 0 * a.a2 * x.a2 - 0 * 0 * a.a12 * x.a12 = 0
      rw [hx0]
      exact RatQ.eqQ_of_norm_eq [a.a0, a.a1, a.a2, a.a12, x.a1, x.a2, x.a12]
        (.sub (.add (.add (.mul (.var 0) (.const 0)) (.mul (.mul (.const 0) (.var 1)) (.var 4)))
                    (.mul (.mul (.const 0) (.var 2)) (.var 5)))
              (.mul (.mul (.mul (.const 0) (.const 0)) (.var 3)) (.var 6)))
        (.const 0) (by decide)
    · show a.a0 * x.a1 + a.a1 * x.a0 - 0 * a.a2 * x.a12 + 0 * a.a12 * x.a2 = 0
      rw [hx0, hx1]
      exact RatQ.eqQ_of_norm_eq [a.a0, a.a1, a.a2, a.a12, x.a2, x.a12]
        (.add (.sub (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.const 0)))
                    (.mul (.mul (.const 0) (.var 2)) (.var 5)))
              (.mul (.mul (.const 0) (.var 3)) (.var 4)))
        (.const 0) (by decide)
    · show a.a0 * x.a2 + 0 * a.a1 * x.a12 + a.a2 * x.a0 - 0 * a.a12 * x.a1 = 0
      rw [hx0, hx2]
      exact RatQ.eqQ_of_norm_eq [a.a0, a.a1, a.a2, a.a12, x.a1, x.a12]
        (.sub (.add (.add (.mul (.var 0) (.const 0)) (.mul (.mul (.const 0) (.var 1)) (.var 5)))
                    (.mul (.var 2) (.const 0)))
              (.mul (.mul (.const 0) (.var 3)) (.var 4)))
        (.const 0) (by decide)

/-- Key structural lemma: EVERY nonzero left ideal `I` of `Λ(ℚ^2)` contains `e_{12}`! -/
theorem mem_e12_of_nonzero_leftIdeal (I : Ext2Q → Prop) (hI : Ext2Alg.IsLeftIdeal I)
    {y : Ext2Q} (hyI : I y) (hynz : y ≠ Ext2Alg.zero) : I (Cl2.e12 0 0) := by
  by_cases ha0 : y.a0 ≠ 0
  · -- `(y.a0⁻¹ • e12) * y = e12`
    let m := Ext2Alg.smul y.a0⁻¹ (Cl2.e12 0 0)
    have hmul : Ext2Alg.mul m y = Cl2.e12 0 0 := by
      have hm : Ext2Alg.mul (Cl2.e12 0 0) y = Ext2Alg.smul y.a0 (Cl2.e12 0 0) := by
        refine Cl2.ext ?_ ?_ ?_ ?_
        · exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
            (.sub (.add (.add (.mul (.const 0) (.var 0)) (.mul (.mul (.const 0) (.const 0)) (.var 1)))
                        (.mul (.mul (.const 0) (.const 0)) (.var 2)))
                  (.mul (.mul (.mul (.const 0) (.const 0)) (.const 1)) (.var 3)))
            (.mul (.var 0) (.const 0)) (by decide)
        · exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
            (.add (.sub (.add (.mul (.const 0) (.var 1)) (.mul (.const 0) (.var 0)))
                        (.mul (.mul (.const 0) (.const 0)) (.var 3)))
                  (.mul (.mul (.const 0) (.const 1)) (.var 2)))
            (.mul (.var 0) (.const 0)) (by decide)
        · exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
            (.sub (.add (.add (.mul (.const 0) (.var 2)) (.mul (.mul (.const 0) (.const 0)) (.var 3)))
                        (.mul (.const 0) (.var 0)))
                  (.mul (.mul (.const 0) (.const 1)) (.var 1)))
            (.mul (.var 0) (.const 0)) (by decide)
        · exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
            (.add (.sub (.add (.mul (.const 0) (.var 3)) (.mul (.const 0) (.var 2)))
                        (.mul (.const 0) (.var 1)))
                  (.mul (.const 1) (.var 0)))
            (.mul (.var 0) (.const 1)) (by decide)
      show Ext2Alg.mul (Ext2Alg.smul y.a0⁻¹ (Cl2.e12 0 0)) y = Cl2.e12 0 0
      rw [Ext2Alg.smul_mul_left, hm, ← Ext2Alg.mul_smul, RatQ.inv_mul_cancel ha0, Ext2Alg.one_smul]
    rw [← hmul]
    exact hI.2.2.2 m y hyI
  · have hy0 : y.a0 = 0 := Classical.byContradiction (fun h => ha0 h)
    by_cases ha1 : y.a1 ≠ 0
    · -- `(-(y.a1⁻¹) • e2) * y = e12`
      let m := Ext2Alg.smul (-y.a1⁻¹) (Cl2.e2 0 0)
      have hmul : Ext2Alg.mul m y = Cl2.e12 0 0 := by
        have hm : Ext2Alg.mul (Cl2.e2 0 0) y = Ext2Alg.smul (-y.a1) (Cl2.e12 0 0) := by
          refine Cl2.ext ?_ ?_ ?_ ?_
          · show 0 * y.a0 + 0 * 0 * y.a1 + 0 * 1 * y.a2 - 0 * 0 * 0 * y.a12 = (-y.a1) * 0
            exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
              (.sub (.add (.add (.mul (.const 0) (.var 0)) (.mul (.mul (.const 0) (.const 0)) (.var 1)))
                          (.mul (.mul (.const 0) (.const 1)) (.var 2)))
                    (.mul (.mul (.mul (.const 0) (.const 0)) (.const 0)) (.var 3)))
              (.mul (.neg (.var 1)) (.const 0)) (by decide)
          · show 0 * y.a1 + 0 * y.a0 - 0 * 1 * y.a12 + 0 * 0 * y.a2 = (-y.a1) * 0
            exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
              (.add (.sub (.add (.mul (.const 0) (.var 1)) (.mul (.const 0) (.var 0)))
                          (.mul (.mul (.const 0) (.const 1)) (.var 3)))
                    (.mul (.mul (.const 0) (.const 0)) (.var 2)))
              (.mul (.neg (.var 1)) (.const 0)) (by decide)
          · show 0 * y.a2 + 0 * 0 * y.a12 + 1 * y.a0 - 0 * 0 * y.a1 = (-y.a1) * 0
            rw [hy0]
            exact RatQ.eqQ_of_norm_eq [y.a1, y.a2, y.a12]
              (.sub (.add (.add (.mul (.const 0) (.var 1)) (.mul (.mul (.const 0) (.const 0)) (.var 2)))
                          (.mul (.const 1) (.const 0)))
                    (.mul (.mul (.const 0) (.const 0)) (.var 0)))
              (.mul (.neg (.var 0)) (.const 0)) (by decide)
          · show 0 * y.a12 + 0 * y.a2 - 1 * y.a1 + 0 * y.a0 = (-y.a1) * 1
            exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
              (.add (.sub (.add (.mul (.const 0) (.var 3)) (.mul (.const 0) (.var 2)))
                          (.mul (.const 1) (.var 1)))
                    (.mul (.const 0) (.var 0)))
              (.mul (.neg (.var 1)) (.const 1)) (by decide)
        show Ext2Alg.mul (Ext2Alg.smul (-y.a1⁻¹) (Cl2.e2 0 0)) y = Cl2.e12 0 0
        have hnn : (-y.a1⁻¹) * (-y.a1) = y.a1⁻¹ * y.a1 :=
          RatQ.eqQ_of_norm_eq [y.a1⁻¹, y.a1]
            (.mul (.neg (.var 0)) (.neg (.var 1))) (.mul (.var 0) (.var 1)) (by decide)
        rw [Ext2Alg.smul_mul_left, hm, ← Ext2Alg.mul_smul, hnn,
            RatQ.inv_mul_cancel ha1, Ext2Alg.one_smul]
      rw [← hmul]
      exact hI.2.2.2 m y hyI
    · have hy1 : y.a1 = 0 := Classical.byContradiction (fun h => ha1 h)
      by_cases ha2 : y.a2 ≠ 0
      · -- `(y.a2⁻¹ • e1) * y = e12`
        let m := Ext2Alg.smul y.a2⁻¹ (Cl2.e1 0 0)
        have hmul : Ext2Alg.mul m y = Cl2.e12 0 0 := by
          have hm : Ext2Alg.mul (Cl2.e1 0 0) y = Ext2Alg.smul y.a2 (Cl2.e12 0 0) := by
            refine Cl2.ext ?_ ?_ ?_ ?_
            · show 0 * y.a0 + 0 * 1 * y.a1 + 0 * 0 * y.a2 - 0 * 0 * 0 * y.a12 = y.a2 * 0
              exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
                (.sub (.add (.add (.mul (.const 0) (.var 0)) (.mul (.mul (.const 0) (.const 1)) (.var 1)))
                            (.mul (.mul (.const 0) (.const 0)) (.var 2)))
                      (.mul (.mul (.mul (.const 0) (.const 0)) (.const 0)) (.var 3)))
                (.mul (.var 2) (.const 0)) (by decide)
            · show 0 * y.a1 + 1 * y.a0 - 0 * 0 * y.a12 + 0 * 0 * y.a2 = y.a2 * 0
              rw [hy0]
              exact RatQ.eqQ_of_norm_eq [y.a1, y.a2, y.a12]
                (.add (.sub (.add (.mul (.const 0) (.var 0)) (.mul (.const 1) (.const 0)))
                            (.mul (.mul (.const 0) (.const 0)) (.var 2)))
                      (.mul (.mul (.const 0) (.const 0)) (.var 1)))
                (.mul (.var 1) (.const 0)) (by decide)
            · show 0 * y.a2 + 0 * 1 * y.a12 + 0 * y.a0 - 0 * 0 * y.a1 = y.a2 * 0
              exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
                (.sub (.add (.add (.mul (.const 0) (.var 2)) (.mul (.mul (.const 0) (.const 1)) (.var 3)))
                            (.mul (.const 0) (.var 0)))
                      (.mul (.mul (.const 0) (.const 0)) (.var 1)))
                (.mul (.var 2) (.const 0)) (by decide)
            · show 0 * y.a12 + 1 * y.a2 - 0 * y.a1 + 0 * y.a0 = y.a2 * 1
              exact RatQ.eqQ_of_norm_eq [y.a0, y.a1, y.a2, y.a12]
                (.add (.sub (.add (.mul (.const 0) (.var 3)) (.mul (.const 1) (.var 2)))
                            (.mul (.const 0) (.var 1)))
                      (.mul (.const 0) (.var 0)))
                (.mul (.var 2) (.const 1)) (by decide)
          show Ext2Alg.mul (Ext2Alg.smul y.a2⁻¹ (Cl2.e1 0 0)) y = Cl2.e12 0 0
          rw [Ext2Alg.smul_mul_left, hm, ← Ext2Alg.mul_smul, RatQ.inv_mul_cancel ha2, Ext2Alg.one_smul]
        rw [← hmul]
        exact hI.2.2.2 m y hyI
      · have hy2 : y.a2 = 0 := Classical.byContradiction (fun h => ha2 h)
        let c := y.a12
        have hc : c ≠ 0 := fun h12 => hynz (Cl2.ext hy0 hy1 hy2 h12)
        have hy_eq : y = Ext2Alg.smul c (Cl2.e12 0 0) :=
          eq_smul_e12_of_topSocle ⟨hy0, hy1, hy2⟩
        have hsm := hI.2.2.1 c⁻¹ y hyI
        rw [hy_eq, ← Ext2Alg.mul_smul, RatQ.inv_mul_cancel hc, Ext2Alg.one_smul] at hsm
        exact hsm

theorem topSocle_isMinimalLeftIdeal : Ext2Alg.IsMinimalLeftIdeal TopSocle := by
  refine ⟨topSocle_isLeftIdeal, ⟨Cl2.e12 0 0, ⟨rfl, rfl, rfl⟩, by decide⟩, ?_⟩
  intro I hI _
  by_cases hall0 : ∀ x, I x → x = Ext2Alg.zero
  · exact .inl hall0
  · right
    have hex : ∃ y, I y ∧ y ≠ Ext2Alg.zero := by
      apply Classical.byContradiction
      intro hno
      apply hall0
      intro x hxI
      apply Classical.byContradiction
      intro hxz
      exact hno ⟨x, hxI, hxz⟩
    rcases hex with ⟨y, hyI, hynz⟩
    have he12 := mem_e12_of_nonzero_leftIdeal I hI hyI hynz
    intro z hz
    rw [eq_smul_e12_of_topSocle hz]
    exact hI.2.2.1 z.a12 (Cl2.e12 0 0) he12

/-- Complete classification of minimal nonzero left ideals of `Λ(ℚ^2)`:
    `TopSocle = ℚ · e_{12}` is the UNIQUE minimal nonzero left ideal! -/
theorem minimalLeftIdeal_iff (S : Ext2Q → Prop) :
    Ext2Alg.IsMinimalLeftIdeal S ↔ ∀ x, S x ↔ TopSocle x := by
  constructor
  · rintro ⟨hL, ⟨y, hyS, hynz⟩, hmin⟩
    have he12 := mem_e12_of_nonzero_leftIdeal S hL hyS hynz
    have hsub : ∀ x, TopSocle x → S x := by
      intro x hx
      rw [eq_smul_e12_of_topSocle hx]
      exact hL.2.2.1 x.a12 (Cl2.e12 0 0) he12
    cases hmin TopSocle topSocle_isLeftIdeal hsub with
    | inl hall0 =>
      have hz : Cl2.e12 0 0 = Ext2Alg.zero := hall0 (Cl2.e12 0 0) ⟨rfl, rfl, rfl⟩
      exact False.elim ((by decide : Cl2.e12 0 0 ≠ Ext2Alg.zero) hz)
    | inr hsup =>
      exact fun x => ⟨hsup x, hsub x⟩
  · intro hiff
    have hEq : S = TopSocle := funext (fun x => propext (hiff x))
    rw [hEq]
    exact topSocle_isMinimalLeftIdeal

theorem topSocle_hasDim_one : HasQDim Ext2Alg TopSocle 1 := by
  refine ⟨{
    toVec := fun x _ _ => x.a12
    ofVec := fun v => ⟨0, 0, 0, v ⟨0, by decide⟩⟩
    ofVec_mem := fun _ => ⟨rfl, rfl, rfl⟩
    left_inv := fun x ⟨h0, h1, h2⟩ => Cl2.ext h0.symm h1.symm h2.symm rfl
    right_inv := fun v => by funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl
    ofVec_add := fun _ _ => by
      refine Cl2.ext ?_ ?_ ?_ rfl <;> (show 0 = 0 + 0; rw [RatQ.add_zero])
    ofVec_smul := fun r _ => by
      refine Cl2.ext ?_ ?_ ?_ rfl <;> (show 0 = r * 0; rw [RatQ.mul_zero])
  }⟩

theorem topSocle_isNilpotent : Ext2Alg.IsNilpotentIdeal TopSocle := by
  intro x y hx hy
  rw [eq_smul_e12_of_topSocle hx, eq_smul_e12_of_topSocle hy, Ext2Alg.smul_mul_left]
  change Ext2Alg.smul x.a12 (Cl2.mul (Cl2.e12 0 0) (Cl2.smul y.a12 (Cl2.e12 0 0))) = Ext2Alg.zero
  rw [cl2_mul_smul_right]
  have he12_sq : Cl2.mul (Cl2.e12 0 0) (Cl2.e12 0 0) = Ext2Alg.zero := by decide
  rw [he12_sq]
  change Ext2Alg.smul x.a12 (Ext2Alg.smul y.a12 Ext2Alg.zero) = Ext2Alg.zero
  rw [Ext2Alg.smul_zero, Ext2Alg.smul_zero]

/-- Master Refutation III (`n = 2` EVEN, degenerate `Λ(ℚ^2) = Cl2 0 0`):
    EVERY minimal nonzero left ideal `S` equals `ℚ · e_{12}`, has dimension `1`
    (`¬ dim 2 = 2^(2/2)`), is nilpotent (`S^2 = 0`, containing NO nonzero idempotent),
    is NOT faithful, and is annihilated by every vector `v ∈ V = span(e_1, e_2)`. -/
theorem refutation_ext2 (S : Ext2Q → Prop) (hS : Ext2Alg.IsMinimalLeftIdeal S) :
    HasQDim Ext2Alg S 1 ∧
    ¬ HasQDim Ext2Alg S (2 ^ (2 / 2)) ∧
    Ext2Alg.IsNilpotentIdeal S ∧
    (∀ e, S e → ¬ Ext2Alg.IsIdempotent e) ∧
    ¬ Ext2Alg.IsFaithfulLeftIdeal S ∧
    (∀ (x1 x2 : RatQ) (s : Ext2Q), S s →
      Ext2Alg.mul (Ext2Alg.add (Ext2Alg.smul x1 (Cl2.e1 0 0))
                               (Ext2Alg.smul x2 (Cl2.e2 0 0))) s = Ext2Alg.zero) := by
  have hiff := (minimalLeftIdeal_iff S).mp hS
  have hEq : S = TopSocle := funext (fun x => propext (hiff x))
  subst hEq
  have hkill : ∀ (x1 x2 : RatQ) (s : Ext2Q), TopSocle s →
      Ext2Alg.mul (Ext2Alg.add (Ext2Alg.smul x1 (Cl2.e1 0 0))
                               (Ext2Alg.smul x2 (Cl2.e2 0 0))) s = Ext2Alg.zero := by
    intro x1 x2 s hs
    rw [eq_smul_e12_of_topSocle hs]
    change Cl2.mul (Ext2Alg.add (Ext2Alg.smul x1 (Cl2.e1 0 0)) (Ext2Alg.smul x2 (Cl2.e2 0 0)))
                   (Cl2.smul s.a12 (Cl2.e12 0 0)) = Ext2Alg.zero
    rw [cl2_mul_smul_right]
    change Ext2Alg.smul s.a12
      (Ext2Alg.mul (Ext2Alg.add (Ext2Alg.smul x1 (Cl2.e1 0 0)) (Ext2Alg.smul x2 (Cl2.e2 0 0)))
                   (Cl2.e12 0 0)) = Ext2Alg.zero
    rw [Ext2Alg.right_distrib, Ext2Alg.smul_mul_left, Ext2Alg.smul_mul_left]
    have z1 : Ext2Alg.mul (Cl2.e1 0 0) (Cl2.e12 0 0) = Ext2Alg.zero := by decide
    have z2 : Ext2Alg.mul (Cl2.e2 0 0) (Cl2.e12 0 0) = Ext2Alg.zero := by decide
    rw [z1, z2, Ext2Alg.smul_zero, Ext2Alg.smul_zero, Ext2Alg.add_zero, Ext2Alg.smul_zero]
  refine ⟨topSocle_hasDim_one, dim_one_not_dim_two topSocle_hasDim_one, topSocle_isNilpotent, ?_, ?_, hkill⟩
  · intro e heS ⟨he_sq, he_nz⟩
    have hz := topSocle_isNilpotent e e heS heS
    rw [he_sq] at hz
    exact he_nz hz
  · intro hfaith
    have hann : ∀ s, TopSocle s → Ext2Alg.mul (Cl2.e1 0 0) s = Ext2Alg.zero := by
      intro s hs
      have hk := hkill 1 0 s hs
      rw [Ext2Alg.one_smul, Ext2Alg.zero_smul, Ext2Alg.add_zero] at hk
      exact hk
    exact (by decide : Cl2.e1 0 0 ≠ Ext2Alg.zero) (hfaith (Cl2.e1 0 0) hann)

end Ext2

end SpinorMinimalIdeals
