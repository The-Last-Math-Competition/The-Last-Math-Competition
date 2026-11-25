/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Formalization for Conjecture 00000007605:
  1. Group representation spectrum of Pin groups:
     - `Pin(1,0) ≅ C_2 × C_2` admits 4 pairwise non-isomorphic 1D irreducible group representations.
     - `Pin^-(2,0)(F)` admits an INFINITE family `k ↦ harmonicRep k` of pairwise non-isomorphic
       2-dimensional irreducible `F`-representations (proved via `(3 + 4i)^(n+1) ≡ 3 + 4i (mod 5)`
       and 2D operator trace invariance).
  2. Positive Non-Vacuity & Complex Salvage Theorems (over `K = ComplexOver F`, modelling `ℂ`):
     - Even complex Clifford algebra `ℂl_2(K) = M_2(K)`: unique irreducible complex spinor module `K²`
       with unique division-ring type `End_{ℂl_2}(K²) ≅ K` and 1-dimensional center `K · I_2`.
     - Odd complex Clifford algebra `ℂl_3(K) = M_2(K) × M_2(K)` (Pauli spinors): exactly TWO
       non-isomorphic irreducible complex Pin spinor modules `S_+^K, S_-^K`, distinguished by the
       Clifford center `Z(ℂl_3(K)) ≅ K × K` (central volume element `ω = (I_2, -I_2)`), whose
       restrictions to the even Spin subalgebra `ℂl_3^0(K)` become isomorphic!
-/

import Conjecture00000007605.RealCliffordCounterexamples

namespace Conjecture00000007605

section InfinitePinSpectrum

variable {F : Type} [FormallyRealField F]

/-- Subgroup type of `Pin` elements inside `(alg, ι, Q)`. -/
abbrev PinGroup {A V : Type} (alg : Alg F A) (ι : V → A) (Q : V → F) : Type :=
  { g : A // InPin alg ι Q g }

/-- Arbitrary `F`-linear group representation of `Pin(p,q)` (not required to extend
    linearly to `Cl_{p,q}`). -/
structure PinGroupRep {A V S : Type} (alg : Alg F A) (ι : V → A) (Q : V → F)
    (vecS : VecSpace F S) where
  act : PinGroup alg ι Q → S → S
  act_one : ∀ s : S, act ⟨alg.one, InPin.one⟩ s = s
  act_mul : ∀ g₁ g₂ : PinGroup alg ι Q, ∀ s : S,
    act ⟨alg.mul g₁.1 g₂.1, InPin.mul g₁.2 g₂.2⟩ s = act g₁ (act g₂ s)
  act_add : ∀ g : PinGroup alg ι Q, ∀ s t : S,
    act g (vecS.add s t) = vecS.add (act g s) (act g t)
  act_smul : ∀ g : PinGroup alg ι Q, ∀ c : F, ∀ s : S,
    act g (vecS.smul c s) = vecS.smul c (act g s)

def PinGroupInvariant {A V S : Type} {alg : Alg F A} {ι : V → A} {Q : V → F}
    {vecS : VecSpace F S} (π : PinGroupRep alg ι Q vecS) (W : Subspace F vecS) : Prop :=
  ∀ g : PinGroup alg ι Q, ∀ s : S, W.mem s → W.mem (π.act g s)

def PinGroupIrreducible {A V S : Type} {alg : Alg F A} {ι : V → A} {Q : V → F}
    {vecS : VecSpace F S} (π : PinGroupRep alg ι Q vecS) : Prop :=
  (∃ s : S, s ≠ vecS.zero) ∧
  ∀ W : Subspace F vecS, PinGroupInvariant π W →
    (∀ s : S, W.mem s → s = vecS.zero) ∨ (∀ s : S, W.mem s)

structure PinGroupIso {A V S₁ S₂ : Type} {alg : Alg F A} {ι : V → A} {Q : V → F}
    {V₁ : VecSpace F S₁} {V₂ : VecSpace F S₂}
    (π₁ : PinGroupRep alg ι Q V₁) (π₂ : PinGroupRep alg ι Q V₂) where
  toFun : S₁ → S₂
  map_add : ∀ x y : S₁, toFun (V₁.add x y) = V₂.add (toFun x) (toFun y)
  map_smul : ∀ c : F, ∀ x : S₁, toFun (V₁.smul c x) = V₂.smul c (toFun x)
  map_act : ∀ g : PinGroup alg ι Q, ∀ x : S₁, toFun (π₁.act g x) = π₂.act g (toFun x)
  invFun : S₂ → S₁
  left_inv : ∀ x : S₁, invFun (toFun x) = x
  right_inv : ∀ y : S₂, toFun (invFun y) = y

/-! ### 1. Four Pairwise Non-Isomorphic Irreducible Group Representations of `Pin(1,0)` -/

namespace Pin10Chars

def mkCharRep (χ : Cl10 F → F)
    (h1 : χ Cl10.one = 1)
    (hmul : ∀ x y : Cl10 F, χ (Cl10.mul x y) = χ x * χ y) :
    PinGroupRep (Cl10.alg F) Cl10.ι Cl10.Qpos (realAlg F).toVecSpace where
  act g s := χ g.1 * s
  act_one s := by change χ Cl10.one * s = s; rw [h1, CommRingOps.one_mul]
  act_mul g₁ g₂ s := by
    change χ (Cl10.mul g₁.1 g₂.1) * s = χ g₁.1 * (χ g₂.1 * s)
    rw [hmul, CommRingOps.mul_assoc]
  act_add g s t := CommRingOps.left_distrib (χ g.1) s t
  act_smul g c s := cr_mul_left_comm (χ g.1) c s

theorem charRep_irreducible (χ : Cl10 F → F) (h1 : χ Cl10.one = 1)
    (hmul : ∀ x y : Cl10 F, χ (Cl10.mul x y) = χ x * χ y) :
    PinGroupIrreducible (mkCharRep χ h1 hmul) := by
  refine ⟨⟨1, one_ne_zeroF⟩, fun W _ => ?_⟩
  by_cases hex : ∃ s : F, W.mem s ∧ s ≠ 0
  · right
    obtain ⟨s₀, hs₀mem, hs₀ne⟩ := hex
    intro x
    have hx : x = (x * s₀⁻¹) * s₀ := by
      rw [CommRingOps.mul_assoc, inv_mul_cancelF hs₀ne, cr_mul_one]
    rw [hx]
    exact W.smul_mem (x * s₀⁻¹) s₀ hs₀mem
  · left
    intro s hs
    by_cases hsz : s = 0
    · exact hsz
    · exact False.elim (hex ⟨s, hs, hsz⟩)

def rep00 (F : Type) [FormallyRealField F] :=
  mkCharRep (F := F) (fun _ => 1) rfl (fun _ _ => (CommRingOps.one_mul 1).symm)

def rep01 (F : Type) [FormallyRealField F] :=
  mkCharRep (F := F) (fun x => x.a * x.a - x.b * x.b)
    (RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .sub (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl)
    (fun x y => RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b])
      (e₁ := .sub (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
                  (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                        (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))))
      (e₂ := .mul (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                  (.sub (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) rfl)

def rep10 (F : Type) [FormallyRealField F] :=
  mkCharRep (F := F) (fun x => x.a + x.b)
    (RExpr.eq_of_norm_eq (envGet (0 : F) []) (e₁ := .add .one .zero) (e₂ := .one) rfl)
    (fun x y => RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b])
      (e₁ := .add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
      (e₂ := .mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))) rfl)

def rep11 (F : Type) [FormallyRealField F] :=
  mkCharRep (F := F) (fun x => x.a - x.b)
    (RExpr.eq_of_norm_eq (envGet (0 : F) []) (e₁ := .sub .one .zero) (e₂ := .one) rfl)
    (fun x y => RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b])
      (e₁ := .sub (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
      (e₂ := .mul (.sub (.var 0) (.var 1)) (.sub (.var 2) (.var 3))) rfl)

def pinNegOne : PinGroup (Cl10.alg F) Cl10.ι Cl10.Qpos :=
  ⟨Cl10.mul Cl10.e1 (Cl10.ι (-(1 : F))),
   InPin.mul Cl10.e1_inPin
     (InPin.gen (-(1 : F)) (Or.inl (RExpr.eq_of_norm_eq (envGet (0 : F) [])
       (e₁ := .mul (.neg .one) (.neg .one)) (e₂ := .one) rfl)))⟩

def pinE1 : PinGroup (Cl10.alg F) Cl10.ι Cl10.Qpos := ⟨Cl10.e1, Cl10.e1_inPin⟩

private theorem charRep_ne_of_diff {χ₁ χ₂ : Cl10 F → F} {h1₁ hmul₁ h1₂ hmul₂}
    (g : PinGroup (Cl10.alg F) Cl10.ι Cl10.Qpos)
    (hdiff : χ₁ g.1 - χ₂ g.1 ≠ 0) :
    ¬ Nonempty (PinGroupIso (mkCharRep χ₁ h1₁ hmul₁) (mkCharRep χ₂ h1₂ hmul₂)) := by
  rintro ⟨e⟩
  have hm := e.map_act g 1
  change e.toFun (χ₁ g.1 * 1) = χ₂ g.1 * e.toFun 1 at hm
  have hm2 : χ₁ g.1 * e.toFun 1 = χ₂ g.1 * e.toFun 1 := by
    have hsm := e.map_smul (χ₁ g.1) 1
    change e.toFun (χ₁ g.1 * 1) = χ₁ g.1 * e.toFun 1 at hsm
    exact hsm.symm.trans hm
  have hprod0 : (χ₁ g.1 - χ₂ g.1) * e.toFun 1 = 0 := by
    calc
      (χ₁ g.1 - χ₂ g.1) * e.toFun 1 = χ₁ g.1 * e.toFun 1 - χ₂ g.1 * e.toFun 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [χ₁ g.1, χ₂ g.1, e.toFun 1])
          (e₁ := .mul (.sub (.var 0) (.var 1)) (.var 2))
          (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) rfl
      _ = χ₂ g.1 * e.toFun 1 - χ₂ g.1 * e.toFun 1 := by rw [hm2]
      _ = 0 := RExpr.eq_of_norm_eq (envGet (0 : F) [χ₂ g.1 * e.toFun 1])
                 (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
  cases mul_eq_zeroF hprod0 with
  | inl hd => exact hdiff hd
  | inr ht0 =>
    have h0 : e.toFun 0 = 0 := by
      have hsm := e.map_smul 0 0
      change e.toFun (0 * 0) = 0 * e.toFun 0 at hsm
      rw [cr_zero_mul, cr_zero_mul] at hsm
      exact hsm
    have h10 : (1 : F) = 0 := by
      calc
        (1 : F) = e.invFun (e.toFun 1) := (e.left_inv 1).symm
        _ = e.invFun 0 := by rw [ht0]
        _ = e.invFun (e.toFun 0) := by rw [h0]
        _ = 0 := e.left_inv 0
    exact one_ne_zeroF h10

theorem pin10_four_pairwise_noniso_irreps :
    PinGroupIrreducible (rep00 F) ∧
    PinGroupIrreducible (rep01 F) ∧
    PinGroupIrreducible (rep10 F) ∧
    PinGroupIrreducible (rep11 F) ∧
    ¬ Nonempty (PinGroupIso (rep00 F) (rep01 F)) ∧
    ¬ Nonempty (PinGroupIso (rep00 F) (rep10 F)) ∧
    ¬ Nonempty (PinGroupIso (rep00 F) (rep11 F)) ∧
    ¬ Nonempty (PinGroupIso (rep01 F) (rep10 F)) ∧
    ¬ Nonempty (PinGroupIso (rep01 F) (rep11 F)) ∧
    ¬ Nonempty (PinGroupIso (rep10 F) (rep11 F)) := by
  have htwo : twoF F ≠ 0 := two_ne_zeroF
  have hneg2 : -(twoF F) ≠ 0 := fun h => htwo (by rw [← cr_neg_neg (twoF F), h, cr_neg_zero])
  refine ⟨charRep_irreducible _ _ _, charRep_irreducible _ _ _,
          charRep_irreducible _ _ _, charRep_irreducible _ _ _,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply charRep_ne_of_diff pinE1
    have heq : (1 : F) - ((0 : F) * 0 - 1 * 1) = twoF F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub .one (.sub (.mul .zero .zero) (.mul .one .one)))
        (e₂ := .add .one .one) rfl
    exact fun h => htwo (heq ▸ h)
  · apply charRep_ne_of_diff pinNegOne
    have heq : (1 : F) - (((0 : F) * 0 + 1 * -(1 : F)) + ((0 : F) * -(1 : F) + 1 * 0)) = twoF F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub .one (.add (.add (.mul .zero .zero) (.mul .one (.neg .one)))
                               (.add (.mul .zero (.neg .one)) (.mul .one .zero))))
        (e₂ := .add .one .one) rfl
    exact fun h => htwo (heq ▸ h)
  · apply charRep_ne_of_diff pinE1
    have heq : (1 : F) - ((0 : F) - 1) = twoF F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub .one (.sub .zero .one)) (e₂ := .add .one .one) rfl
    exact fun h => htwo (heq ▸ h)
  · apply charRep_ne_of_diff pinE1
    have heq : ((0 : F) * 0 - 1 * 1) - ((0 : F) + 1) = -(twoF F) :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub (.sub (.mul .zero .zero) (.mul .one .one)) (.add .zero .one))
        (e₂ := .neg (.add .one .one)) rfl
    exact fun h => hneg2 (heq ▸ h)
  · apply charRep_ne_of_diff pinNegOne
    let na := (0 : F) * 0 + 1 * -(1 : F)
    let nb := (0 : F) * -(1 : F) + 1 * 0
    have heq : (na * na - nb * nb) - (na - nb) = twoF F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub (.sub (.mul (.add (.mul .zero .zero) (.mul .one (.neg .one)))
                                (.add (.mul .zero .zero) (.mul .one (.neg .one))))
                          (.mul (.add (.mul .zero (.neg .one)) (.mul .one .zero))
                                (.add (.mul .zero (.neg .one)) (.mul .one .zero))))
                    (.sub (.add (.mul .zero .zero) (.mul .one (.neg .one)))
                          (.add (.mul .zero (.neg .one)) (.mul .one .zero))))
        (e₂ := .add .one .one) rfl
    exact fun h => htwo (heq ▸ h)
  · apply charRep_ne_of_diff pinE1
    have heq : ((0 : F) + 1) - ((0 : F) - 1) = twoF F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub (.add .zero .one) (.sub .zero .one)) (e₂ := .add .one .one) rfl
    exact fun h => htwo (heq ▸ h)

end Pin10Chars

/-! ### 2. Infinite Family of Pairwise Non-Isomorphic Irreducible 2D Representations of `Pin^-(2,0)(F)` -/

namespace Pin2Harmonics

/-- Every element of `Pin^-(2,0)(F)` lies in the two-component subgroup `Spin(2) ⊔ Spin(2)·i`. -/
def InO2Cover (g : QuatOver F) : Prop :=
  (g.x = 0 ∧ g.y = 0 ∧ g.w * g.w + g.z * g.z = 1) ∨
  (g.w = 0 ∧ g.z = 0 ∧ g.x * g.x + g.y * g.y = 1)

theorem inO2Cover_of_inPin {g : QuatOver F}
    (hg : InPin (QuatOver.alg F) ClQuat.ι ClQuat.Q20 g) : InO2Cover g := by
  induction hg with
  | one =>
    left
    refine ⟨rfl, rfl, ?_⟩
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .add (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl
  | gen v hv =>
    cases hv with
    | inl hv1 =>
      right
      exact ⟨rfl, rfl, hv1⟩
    | inr hvneg =>
      exfalso
      have hsq : v.1 * v.1 + v.2 * v.2 + (1 : F) * 1 + 0 * 0 = 0 := by
        unfold ClQuat.Q20 at hvneg
        rw [hvneg, cr_mul_one, CommRingOps.neg_add_cancel, cr_mul_zero, cr_add_zero]
      exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero v.1 v.2 1 0 hsq).2.2.1
  | mul _hp₁ _hp₂ ih₁ ih₂ =>
    rename_i g₁ g₂
    cases ih₁ with
    | inl h1 =>
      obtain ⟨hx1, hy1, hn1⟩ := h1
      cases ih₂ with
      | inl h2 =>
        obtain ⟨hx2, hy2, hn2⟩ := h2
        left
        refine ⟨?_, ?_, ?_⟩
        · change g₁.w * g₂.x + g₁.x * g₂.w + g₁.y * g₂.z - g₁.z * g₂.y = 0
          rw [hx1, hy1, hx2, hy2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.w, g₂.z])
            (e₁ := .sub (.add (.add (.mul (.var 0) .zero) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
                        (.mul (.var 1) .zero))
            (e₂ := .zero) rfl
        · change g₁.w * g₂.y - g₁.x * g₂.z + g₁.y * g₂.w + g₁.z * g₂.x = 0
          rw [hx1, hy1, hx2, hy2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.w, g₂.z])
            (e₁ := .add (.add (.sub (.mul (.var 0) .zero) (.mul .zero (.var 3))) (.mul .zero (.var 2)))
                        (.mul (.var 1) .zero))
            (e₂ := .zero) rfl
        · change (QuatOver.mul g₁ g₂).w * (QuatOver.mul g₁ g₂).w +
                 (QuatOver.mul g₁ g₂).z * (QuatOver.mul g₁ g₂).z = 1
          have hw : (QuatOver.mul g₁ g₂).w = g₁.w * g₂.w - g₁.z * g₂.z := by
            change g₁.w * g₂.w - g₁.x * g₂.x - g₁.y * g₂.y - g₁.z * g₂.z = _
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.w, g₂.z])
              (e₁ := .sub (.sub (.sub (.mul (.var 0) (.var 2)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 3)))
              (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
          have hz : (QuatOver.mul g₁ g₂).z = g₁.w * g₂.z + g₁.z * g₂.w := by
            change g₁.w * g₂.z + g₁.x * g₂.y - g₁.y * g₂.x + g₁.z * g₂.w = _
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.w, g₂.z])
              (e₁ := .add (.sub (.add (.mul (.var 0) (.var 3)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 2)))
              (e₂ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) rfl
          rw [hw, hz]
          calc
            (g₁.w * g₂.w - g₁.z * g₂.z) * (g₁.w * g₂.w - g₁.z * g₂.z) +
                (g₁.w * g₂.z + g₁.z * g₂.w) * (g₁.w * g₂.z + g₁.z * g₂.w)
                = (g₁.w * g₁.w + g₁.z * g₁.z) * (g₂.w * g₂.w + g₂.z * g₂.z) :=
              RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.w, g₂.z])
                (e₁ := .add (.mul (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                                  (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
                            (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                                  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))))
                (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) rfl
            _ = 1 * 1 := by rw [hn1, hn2]
            _ = 1 := cr_mul_one 1
      | inr h2 =>
        obtain ⟨hw2, hz2, hn2⟩ := h2
        right
        refine ⟨?_, ?_, ?_⟩
        · change g₁.w * g₂.w - g₁.x * g₂.x - g₁.y * g₂.y - g₁.z * g₂.z = 0
          rw [hx1, hy1, hw2, hz2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.x, g₂.y])
            (e₁ := .sub (.sub (.sub (.mul (.var 0) .zero) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
                        (.mul (.var 1) .zero))
            (e₂ := .zero) rfl
        · change g₁.w * g₂.z + g₁.x * g₂.y - g₁.y * g₂.x + g₁.z * g₂.w = 0
          rw [hx1, hy1, hw2, hz2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.x, g₂.y])
            (e₁ := .add (.sub (.add (.mul (.var 0) .zero) (.mul .zero (.var 3))) (.mul .zero (.var 2)))
                        (.mul (.var 1) .zero))
            (e₂ := .zero) rfl
        · have hx : (QuatOver.mul g₁ g₂).x = g₁.w * g₂.x - g₁.z * g₂.y := by
            change g₁.w * g₂.x + g₁.x * g₂.w + g₁.y * g₂.z - g₁.z * g₂.y = _
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.x, g₂.y])
              (e₁ := .sub (.add (.add (.mul (.var 0) (.var 2)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 3)))
              (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
          have hy : (QuatOver.mul g₁ g₂).y = g₁.w * g₂.y + g₁.z * g₂.x := by
            change g₁.w * g₂.y - g₁.x * g₂.z + g₁.y * g₂.w + g₁.z * g₂.x = _
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.x, g₂.y])
              (e₁ := .add (.add (.sub (.mul (.var 0) (.var 3)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 2)))
              (e₂ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) rfl
          change (QuatOver.mul g₁ g₂).x * (QuatOver.mul g₁ g₂).x +
                 (QuatOver.mul g₁ g₂).y * (QuatOver.mul g₁ g₂).y = 1
          rw [hx, hy]
          calc
            (g₁.w * g₂.x - g₁.z * g₂.y) * (g₁.w * g₂.x - g₁.z * g₂.y) +
                (g₁.w * g₂.y + g₁.z * g₂.x) * (g₁.w * g₂.y + g₁.z * g₂.x)
                = (g₁.w * g₁.w + g₁.z * g₁.z) * (g₂.x * g₂.x + g₂.y * g₂.y) :=
              RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.w, g₁.z, g₂.x, g₂.y])
                (e₁ := .add (.mul (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                                  (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
                            (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                                  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))))
                (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) rfl
            _ = 1 * 1 := by rw [hn1, hn2]
            _ = 1 := cr_mul_one 1
    | inr h1 =>
      obtain ⟨hw1, hz1, hn1⟩ := h1
      cases ih₂ with
      | inl h2 =>
        obtain ⟨hx2, hy2, hn2⟩ := h2
        right
        refine ⟨?_, ?_, ?_⟩
        · change g₁.w * g₂.w - g₁.x * g₂.x - g₁.y * g₂.y - g₁.z * g₂.z = 0
          rw [hw1, hz1, hx2, hy2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.w, g₂.z])
            (e₁ := .sub (.sub (.sub (.mul .zero (.var 2)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                        (.mul .zero (.var 3)))
            (e₂ := .zero) rfl
        · change g₁.w * g₂.z + g₁.x * g₂.y - g₁.y * g₂.x + g₁.z * g₂.w = 0
          rw [hw1, hz1, hx2, hy2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.w, g₂.z])
            (e₁ := .add (.sub (.add (.mul .zero (.var 3)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                        (.mul .zero (.var 2)))
            (e₂ := .zero) rfl
        · have hx : (QuatOver.mul g₁ g₂).x = g₁.x * g₂.w + g₁.y * g₂.z := by
            change g₁.w * g₂.x + g₁.x * g₂.w + g₁.y * g₂.z - g₁.z * g₂.y = _
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.w, g₂.z])
              (e₁ := .sub (.add (.add (.mul .zero .zero) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3)))
                          (.mul .zero .zero))
              (e₂ := .add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
          have hy : (QuatOver.mul g₁ g₂).y = g₁.y * g₂.w - g₁.x * g₂.z := by
            change g₁.w * g₂.y - g₁.x * g₂.z + g₁.y * g₂.w + g₁.z * g₂.x = _
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.w, g₂.z])
              (e₁ := .add (.add (.sub (.mul .zero .zero) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 2)))
                          (.mul .zero .zero))
              (e₂ := .sub (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) rfl
          change (QuatOver.mul g₁ g₂).x * (QuatOver.mul g₁ g₂).x +
                 (QuatOver.mul g₁ g₂).y * (QuatOver.mul g₁ g₂).y = 1
          rw [hx, hy]
          calc
            (g₁.x * g₂.w + g₁.y * g₂.z) * (g₁.x * g₂.w + g₁.y * g₂.z) +
                (g₁.y * g₂.w - g₁.x * g₂.z) * (g₁.y * g₂.w - g₁.x * g₂.z)
                = (g₁.x * g₁.x + g₁.y * g₁.y) * (g₂.w * g₂.w + g₂.z * g₂.z) :=
              RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.w, g₂.z])
                (e₁ := .add (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                                  (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
                            (.mul (.sub (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
                                  (.sub (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))))
                (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) rfl
            _ = 1 * 1 := by rw [hn1, hn2]
            _ = 1 := cr_mul_one 1
      | inr h2 =>
        obtain ⟨hw2, hz2, hn2⟩ := h2
        left
        refine ⟨?_, ?_, ?_⟩
        · change g₁.w * g₂.x + g₁.x * g₂.w + g₁.y * g₂.z - g₁.z * g₂.y = 0
          rw [hw1, hz1, hw2, hz2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.x, g₂.y])
            (e₁ := .sub (.add (.add (.mul .zero (.var 2)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                        (.mul .zero (.var 3)))
            (e₂ := .zero) rfl
        · change g₁.w * g₂.y - g₁.x * g₂.z + g₁.y * g₂.w + g₁.z * g₂.x = 0
          rw [hw1, hz1, hw2, hz2]
          exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.x, g₂.y])
            (e₁ := .add (.add (.sub (.mul .zero (.var 3)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                        (.mul .zero (.var 2)))
            (e₂ := .zero) rfl
        · have hw : (QuatOver.mul g₁ g₂).w = -(g₁.x * g₂.x + g₁.y * g₂.y) := by
            change g₁.w * g₂.w - g₁.x * g₂.x - g₁.y * g₂.y - g₁.z * g₂.z = _
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.x, g₂.y])
              (e₁ := .sub (.sub (.sub (.mul .zero .zero) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3)))
                          (.mul .zero .zero))
              (e₂ := .neg (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))) rfl
          have hz : (QuatOver.mul g₁ g₂).z = g₁.x * g₂.y - g₁.y * g₂.x := by
            change g₁.w * g₂.z + g₁.x * g₂.y - g₁.y * g₂.x + g₁.z * g₂.w = _
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.x, g₂.y])
              (e₁ := .add (.sub (.add (.mul .zero .zero) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 2)))
                          (.mul .zero .zero))
              (e₂ := .sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) rfl
          change (QuatOver.mul g₁ g₂).w * (QuatOver.mul g₁ g₂).w +
                 (QuatOver.mul g₁ g₂).z * (QuatOver.mul g₁ g₂).z = 1
          rw [hw, hz]
          calc
            (-(g₁.x * g₂.x + g₁.y * g₂.y)) * (-(g₁.x * g₂.x + g₁.y * g₂.y)) +
                (g₁.x * g₂.y - g₁.y * g₂.x) * (g₁.x * g₂.y - g₁.y * g₂.x)
                = (g₁.x * g₁.x + g₁.y * g₁.y) * (g₂.x * g₂.x + g₂.y * g₂.y) :=
              RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.x, g₁.y, g₂.x, g₂.y])
                (e₁ := .add (.mul (.neg (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
                                  (.neg (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))))
                            (.mul (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                                  (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))))
                (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))) rfl
            _ = 1 * 1 := by rw [hn1, hn2]
            _ = 1 := cr_mul_one 1

end Pin2Harmonics

private theorem cmul_assoc (x y z : ComplexOver F) :
    ComplexOver.mul (ComplexOver.mul x y) z = ComplexOver.mul x (ComplexOver.mul y z) :=
  (ComplexOver.alg F).mul_assoc x y z

private theorem cmul_comm (x y : ComplexOver F) :
    ComplexOver.mul x y = ComplexOver.mul y x :=
  ComplexOver.isComm x y

private theorem cone_mul (x : ComplexOver F) :
    ComplexOver.mul ComplexOver.one x = x :=
  (ComplexOver.alg F).one_mul x

private theorem cmul_one (x : ComplexOver F) :
    ComplexOver.mul x ComplexOver.one = x :=
  (ComplexOver.alg F).mul_one x

private theorem cmul_smul (c d : F) (x : ComplexOver F) :
    ComplexOver.smul (c * d) x = ComplexOver.smul c (ComplexOver.smul d x) :=
  (ComplexOver.alg F).mul_smul c d x

private theorem cone_smul (x : ComplexOver F) :
    ComplexOver.smul 1 x = x :=
  (ComplexOver.alg F).one_smul x

private theorem csmul_mul_left (c : F) (x y : ComplexOver F) :
    ComplexOver.mul (ComplexOver.smul c x) y = ComplexOver.smul c (ComplexOver.mul x y) :=
  (ComplexOver.alg F).smul_mul_left c x y

private theorem csmul_mul_right (c : F) (x y : ComplexOver F) :
    ComplexOver.mul x (ComplexOver.smul c y) = ComplexOver.smul c (ComplexOver.mul x y) :=
  (ComplexOver.alg F).smul_mul_right c x y

private theorem csmul_add (c : F) (x y : ComplexOver F) :
    ComplexOver.smul c (ComplexOver.add x y) =
      ComplexOver.add (ComplexOver.smul c x) (ComplexOver.smul c y) :=
  (ComplexOver.alg F).smul_add c x y

namespace Pin2Harmonics

def cpow : ComplexOver F → Nat → ComplexOver F
  | _, 0 => ComplexOver.one
  | z, n + 1 => ComplexOver.mul z (cpow z n)

theorem cpow_zero_succ (n : Nat) : cpow (ComplexOver.zero (F := F)) (n + 1) = ComplexOver.zero := by
  unfold cpow
  ext
  · change 0 * (cpow ComplexOver.zero n).re - 0 * (cpow ComplexOver.zero n).im = 0
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [(cpow ComplexOver.zero n).re, (cpow ComplexOver.zero n).im])
      (e₁ := .sub (.mul .zero (.var 0)) (.mul .zero (.var 1))) (e₂ := .zero) rfl
  · change 0 * (cpow ComplexOver.zero n).im + 0 * (cpow ComplexOver.zero n).re = 0
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [(cpow ComplexOver.zero n).re, (cpow ComplexOver.zero n).im])
      (e₁ := .add (.mul .zero (.var 1)) (.mul .zero (.var 0))) (e₂ := .zero) rfl

theorem cpow_one (n : Nat) : cpow (ComplexOver.one (F := F)) n = ComplexOver.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold cpow
    rw [ih]
    exact (ComplexOver.alg F).one_mul _

theorem cpow_mul (z w : ComplexOver F) (n : Nat) :
    cpow (ComplexOver.mul z w) n = ComplexOver.mul (cpow z n) (cpow w n) := by
  induction n with
  | zero => exact ((ComplexOver.alg F).one_mul _).symm
  | succ n ih =>
    unfold cpow
    rw [ih]
    exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [z, w, cpow z n, cpow w n])
      (e₁ := .mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (e₂ := .mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl

theorem conj_mul_commC (z w : ComplexOver F) :
    ComplexOver.conj (ComplexOver.mul z w) =
      ComplexOver.mul (ComplexOver.conj z) (ComplexOver.conj w) := by
  let env := envGet (0 : F) [z.re, z.im, w.re, w.im]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.neg (.var 1)) (.neg (.var 3)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .neg (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
      (e₂ := .add (.mul (.var 0) (.neg (.var 3))) (.mul (.neg (.var 1)) (.var 2))) rfl

theorem conj_conjC (z : ComplexOver F) : ComplexOver.conj (ComplexOver.conj z) = z := by
  ext
  · rfl
  · exact cr_neg_neg z.im

theorem cpow_conj (z : ComplexOver F) (n : Nat) :
    cpow (ComplexOver.conj z) n = ComplexOver.conj (cpow z n) := by
  induction n with
  | zero =>
    ext
    · rfl
    · exact cr_neg_zero.symm
  | succ n ih =>
    unfold cpow
    rw [ih, ← conj_mul_commC]

theorem cpow_neg_even (z : ComplexOver F) (k : Nat) :
    cpow (ComplexOver.neg z) (2 * k) = cpow z (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h2]
    change ComplexOver.mul (ComplexOver.neg z)
             (ComplexOver.mul (ComplexOver.neg z) (cpow (ComplexOver.neg z) (2 * k))) =
           ComplexOver.mul z (ComplexOver.mul z (cpow z (2 * k)))
    rw [ih]
    have hsq : ComplexOver.mul (ComplexOver.neg z) (ComplexOver.neg z) = ComplexOver.mul z z :=
      RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [z])
        (e₁ := .mul (.neg (.var 0)) (.neg (.var 0))) (e₂ := .mul (.var 0) (.var 0)) rfl
    calc
      ComplexOver.mul (ComplexOver.neg z) (ComplexOver.mul (ComplexOver.neg z) (cpow z (2 * k)))
          = ComplexOver.mul (ComplexOver.mul (ComplexOver.neg z) (ComplexOver.neg z)) (cpow z (2 * k)) :=
            ((ComplexOver.alg F).mul_assoc _ _ _).symm
      _ = ComplexOver.mul (ComplexOver.mul z z) (cpow z (2 * k)) := by rw [hsq]
      _ = ComplexOver.mul z (ComplexOver.mul z (cpow z (2 * k))) :=
            (ComplexOver.alg F).mul_assoc _ _ _

theorem cpow_add (z : ComplexOver F) (m n : Nat) :
    cpow z (m + n) = ComplexOver.mul (cpow z m) (cpow z n) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    exact ((ComplexOver.alg F).one_mul _).symm
  | succ m ih =>
    rw [Nat.succ_add]
    change ComplexOver.mul z (cpow z (m + n)) =
           ComplexOver.mul (ComplexOver.mul z (cpow z m)) (cpow z n)
    rw [ih, cmul_assoc]

/-- The `k`-th even harmonic 2D representation (`m = 2(k + 1)`) of `Pin^-(2,0)(F)` on `ComplexOver F`:
    `σ_{2(k+1)}(g)(u) = ⟨g.w, g.z⟩^{2(k+1)} · u + ⟨g.x, g.y⟩^{2(k+1)} · conj(u)`. -/
def harmonicAct (m : Nat) (g : QuatOver F) (u : ComplexOver F) : ComplexOver F :=
  ComplexOver.add
    (ComplexOver.mul (cpow ⟨g.w, g.z⟩ m) u)
    (ComplexOver.mul (cpow ⟨g.x, g.y⟩ m) (ComplexOver.conj u))

def harmonicRep (k : Nat) :
    PinGroupRep (QuatOver.alg F) ClQuat.ι ClQuat.Q20 (ComplexOver.alg F).toVecSpace where
  act g u := harmonicAct (2 * (k + 1)) g.1 u
  act_one u := by
    change harmonicAct (2 * (k + 1)) QuatOver.one u = u
    unfold harmonicAct
    have hm : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have hz : cpow (⟨(QuatOver.one (F := F)).x, (QuatOver.one (F := F)).y⟩ : ComplexOver F)
                (2 * (k + 1)) = ComplexOver.zero := by
      rw [hm]
      exact cpow_zero_succ (2 * k + 1)
    have ho : cpow (⟨(QuatOver.one (F := F)).w, (QuatOver.one (F := F)).z⟩ : ComplexOver F)
                (2 * (k + 1)) = ComplexOver.one := cpow_one _
    rw [ho, hz]
    exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [u, ComplexOver.conj u])
      (e₁ := .add (.mul .one (.var 0)) (.mul .zero (.var 1))) (e₂ := .var 0) rfl
  act_mul g₁ g₂ u := by
    change harmonicAct (2 * (k + 1)) (QuatOver.mul g₁.1 g₂.1) u =
           harmonicAct (2 * (k + 1)) g₁.1 (harmonicAct (2 * (k + 1)) g₂.1 u)
    unfold harmonicAct
    have hm : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have hz0 : cpow (ComplexOver.zero (F := F)) (2 * (k + 1)) = ComplexOver.zero := by
      rw [hm]; exact cpow_zero_succ _
    have hcov1 := inO2Cover_of_inPin g₁.2
    have hcov2 := inO2Cover_of_inPin g₂.2
    cases hcov1 with
    | inl h1 =>
      obtain ⟨hx1, hy1, _⟩ := h1
      have hp1 : (⟨g₁.1.x, g₁.1.y⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hx1; exact hy1
      cases hcov2 with
      | inl h2 =>
        obtain ⟨hx2, hy2, _⟩ := h2
        have hp2 : (⟨g₂.1.x, g₂.1.y⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hx2; exact hy2
        have hxy12 : (⟨(QuatOver.mul g₁.1 g₂.1).x, (QuatOver.mul g₁.1 g₂.1).y⟩ : ComplexOver F) =
            ComplexOver.zero := by
          ext
          · change g₁.1.w * g₂.1.x + g₁.1.x * g₂.1.w + g₁.1.y * g₂.1.z - g₁.1.z * g₂.1.y = 0
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.w, g₂.1.z])
              (e₁ := .sub (.add (.add (.mul (.var 0) .zero) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
                          (.mul (.var 1) .zero)) (e₂ := .zero) rfl
          · change g₁.1.w * g₂.1.y - g₁.1.x * g₂.1.z + g₁.1.y * g₂.1.w + g₁.1.z * g₂.1.x = 0
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.w, g₂.1.z])
              (e₁ := .add (.add (.sub (.mul (.var 0) .zero) (.mul .zero (.var 3))) (.mul .zero (.var 2)))
                          (.mul (.var 1) .zero)) (e₂ := .zero) rfl
        have hwz12 : (⟨(QuatOver.mul g₁.1 g₂.1).w, (QuatOver.mul g₁.1 g₂.1).z⟩ : ComplexOver F) =
            ComplexOver.mul ⟨g₁.1.w, g₁.1.z⟩ ⟨g₂.1.w, g₂.1.z⟩ := by
          ext
          · change g₁.1.w * g₂.1.w - g₁.1.x * g₂.1.x - g₁.1.y * g₂.1.y - g₁.1.z * g₂.1.z = _
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.w, g₂.1.z])
              (e₁ := .sub (.sub (.sub (.mul (.var 0) (.var 2)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 3)))
              (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
          · change g₁.1.w * g₂.1.z + g₁.1.x * g₂.1.y - g₁.1.y * g₂.1.x + g₁.1.z * g₂.1.w = _
            rw [hx1, hy1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.w, g₂.1.z])
              (e₁ := .add (.sub (.add (.mul (.var 0) (.var 3)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 2)))
              (e₂ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) rfl
        rw [hp1, hp2, hxy12, hwz12, hz0, cpow_mul]
        exact RExpr.eq_of_norm_eq
          (envGet (ComplexOver.zero (F := F))
            [cpow ⟨g₁.1.w, g₁.1.z⟩ (2 * (k + 1)), cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1)), u,
             ComplexOver.conj u,
             ComplexOver.conj (ComplexOver.add (ComplexOver.mul (cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1))) u)
                               (ComplexOver.mul ComplexOver.zero (ComplexOver.conj u)))])
          (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul .zero (.var 3)))
          (e₂ := .add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul .zero (.var 3))))
                      (.mul .zero (.var 4))) rfl
      | inr h2 =>
        obtain ⟨hw2, hz2, _⟩ := h2
        have hp2 : (⟨g₂.1.w, g₂.1.z⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hw2; exact hz2
        have hwz12 : (⟨(QuatOver.mul g₁.1 g₂.1).w, (QuatOver.mul g₁.1 g₂.1).z⟩ : ComplexOver F) =
            ComplexOver.zero := by
          ext
          · change g₁.1.w * g₂.1.w - g₁.1.x * g₂.1.x - g₁.1.y * g₂.1.y - g₁.1.z * g₂.1.z = 0
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.x, g₂.1.y])
              (e₁ := .sub (.sub (.sub (.mul (.var 0) .zero) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
                          (.mul (.var 1) .zero)) (e₂ := .zero) rfl
          · change g₁.1.w * g₂.1.z + g₁.1.x * g₂.1.y - g₁.1.y * g₂.1.x + g₁.1.z * g₂.1.w = 0
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.x, g₂.1.y])
              (e₁ := .add (.sub (.add (.mul (.var 0) .zero) (.mul .zero (.var 3))) (.mul .zero (.var 2)))
                          (.mul (.var 1) .zero)) (e₂ := .zero) rfl
        have hxy12 : (⟨(QuatOver.mul g₁.1 g₂.1).x, (QuatOver.mul g₁.1 g₂.1).y⟩ : ComplexOver F) =
            ComplexOver.mul ⟨g₁.1.w, g₁.1.z⟩ ⟨g₂.1.x, g₂.1.y⟩ := by
          ext
          · change g₁.1.w * g₂.1.x + g₁.1.x * g₂.1.w + g₁.1.y * g₂.1.z - g₁.1.z * g₂.1.y = _
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.x, g₂.1.y])
              (e₁ := .sub (.add (.add (.mul (.var 0) (.var 2)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 3)))
              (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
          · change g₁.1.w * g₂.1.y - g₁.1.x * g₂.1.z + g₁.1.y * g₂.1.w + g₁.1.z * g₂.1.x = _
            rw [hx1, hy1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.w, g₁.1.z, g₂.1.x, g₂.1.y])
              (e₁ := .add (.add (.sub (.mul (.var 0) (.var 3)) (.mul .zero .zero)) (.mul .zero .zero))
                          (.mul (.var 1) (.var 2)))
              (e₂ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) rfl
        rw [hp1, hp2, hwz12, hxy12, hz0, cpow_mul]
        exact RExpr.eq_of_norm_eq
          (envGet (ComplexOver.zero (F := F))
            [cpow ⟨g₁.1.w, g₁.1.z⟩ (2 * (k + 1)), cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1)), u,
             ComplexOver.conj u,
             ComplexOver.conj (ComplexOver.add (ComplexOver.mul ComplexOver.zero u)
                               (ComplexOver.mul (cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1))) (ComplexOver.conj u)))])
          (e₁ := .add (.mul .zero (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
          (e₂ := .add (.mul (.var 0) (.add (.mul .zero (.var 2)) (.mul (.var 1) (.var 3))))
                      (.mul .zero (.var 4))) rfl
    | inr h1 =>
      obtain ⟨hw1, hz1, _⟩ := h1
      have hp1 : (⟨g₁.1.w, g₁.1.z⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hw1; exact hz1
      cases hcov2 with
      | inl h2 =>
        obtain ⟨hx2, hy2, _⟩ := h2
        have hp2 : (⟨g₂.1.x, g₂.1.y⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hx2; exact hy2
        have hwz12 : (⟨(QuatOver.mul g₁.1 g₂.1).w, (QuatOver.mul g₁.1 g₂.1).z⟩ : ComplexOver F) =
            ComplexOver.zero := by
          ext
          · change g₁.1.w * g₂.1.w - g₁.1.x * g₂.1.x - g₁.1.y * g₂.1.y - g₁.1.z * g₂.1.z = 0
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.w, g₂.1.z])
              (e₁ := .sub (.sub (.sub (.mul .zero (.var 2)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                          (.mul .zero (.var 3))) (e₂ := .zero) rfl
          · change g₁.1.w * g₂.1.z + g₁.1.x * g₂.1.y - g₁.1.y * g₂.1.x + g₁.1.z * g₂.1.w = 0
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.w, g₂.1.z])
              (e₁ := .add (.sub (.add (.mul .zero (.var 3)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                          (.mul .zero (.var 2))) (e₂ := .zero) rfl
        have hxy12 : (⟨(QuatOver.mul g₁.1 g₂.1).x, (QuatOver.mul g₁.1 g₂.1).y⟩ : ComplexOver F) =
            ComplexOver.mul ⟨g₁.1.x, g₁.1.y⟩ (ComplexOver.conj ⟨g₂.1.w, g₂.1.z⟩) := by
          ext
          · change g₁.1.w * g₂.1.x + g₁.1.x * g₂.1.w + g₁.1.y * g₂.1.z - g₁.1.z * g₂.1.y = _
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.w, g₂.1.z])
              (e₁ := .sub (.add (.add (.mul .zero .zero) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3)))
                          (.mul .zero .zero))
              (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.neg (.var 3)))) rfl
          · change g₁.1.w * g₂.1.y - g₁.1.x * g₂.1.z + g₁.1.y * g₂.1.w + g₁.1.z * g₂.1.x = _
            rw [hw1, hz1, hx2, hy2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.w, g₂.1.z])
              (e₁ := .add (.add (.sub (.mul .zero .zero) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 2)))
                          (.mul .zero .zero))
              (e₂ := .add (.mul (.var 0) (.neg (.var 3))) (.mul (.var 1) (.var 2))) rfl
        rw [hp1, hp2, hwz12, hxy12, hz0, cpow_mul, cpow_conj]
        have hinner :
            ComplexOver.add (ComplexOver.mul (cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1))) u)
                            (ComplexOver.mul ComplexOver.zero (ComplexOver.conj u)) =
            ComplexOver.mul (cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1))) u :=
          RExpr.eq_of_norm_eq
            (envGet (ComplexOver.zero (F := F)) [cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1)), u, ComplexOver.conj u])
            (e₁ := .add (.mul (.var 0) (.var 1)) (.mul .zero (.var 2)))
            (e₂ := .mul (.var 0) (.var 1)) rfl
        rw [hinner, conj_mul_commC]
        exact RExpr.eq_of_norm_eq
          (envGet (ComplexOver.zero (F := F))
            [cpow ⟨g₁.1.x, g₁.1.y⟩ (2 * (k + 1)),
             ComplexOver.conj (cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1))),
             u, ComplexOver.conj u,
             ComplexOver.mul (cpow ⟨g₂.1.w, g₂.1.z⟩ (2 * (k + 1))) u])
          (e₁ := .add (.mul .zero (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
          (e₂ := .add (.mul .zero (.var 4)) (.mul (.var 0) (.mul (.var 1) (.var 3)))) rfl
      | inr h2 =>
        obtain ⟨hw2, hz2, _⟩ := h2
        have hp2 : (⟨g₂.1.w, g₂.1.z⟩ : ComplexOver F) = ComplexOver.zero := by ext; exact hw2; exact hz2
        have hxy12 : (⟨(QuatOver.mul g₁.1 g₂.1).x, (QuatOver.mul g₁.1 g₂.1).y⟩ : ComplexOver F) =
            ComplexOver.zero := by
          ext
          · change g₁.1.w * g₂.1.x + g₁.1.x * g₂.1.w + g₁.1.y * g₂.1.z - g₁.1.z * g₂.1.y = 0
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.x, g₂.1.y])
              (e₁ := .sub (.add (.add (.mul .zero (.var 2)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                          (.mul .zero (.var 3))) (e₂ := .zero) rfl
          · change g₁.1.w * g₂.1.y - g₁.1.x * g₂.1.z + g₁.1.y * g₂.1.w + g₁.1.z * g₂.1.x = 0
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.x, g₂.1.y])
              (e₁ := .add (.add (.sub (.mul .zero (.var 3)) (.mul (.var 0) .zero)) (.mul (.var 1) .zero))
                          (.mul .zero (.var 2))) (e₂ := .zero) rfl
        have hwz12 : (⟨(QuatOver.mul g₁.1 g₂.1).w, (QuatOver.mul g₁.1 g₂.1).z⟩ : ComplexOver F) =
            ComplexOver.neg (ComplexOver.mul ⟨g₁.1.x, g₁.1.y⟩ (ComplexOver.conj ⟨g₂.1.x, g₂.1.y⟩)) := by
          ext
          · change g₁.1.w * g₂.1.w - g₁.1.x * g₂.1.x - g₁.1.y * g₂.1.y - g₁.1.z * g₂.1.z = _
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.x, g₂.1.y])
              (e₁ := .sub (.sub (.sub (.mul .zero .zero) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3)))
                          (.mul .zero .zero))
              (e₂ := .neg (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.neg (.var 3))))) rfl
          · change g₁.1.w * g₂.1.z + g₁.1.x * g₂.1.y - g₁.1.y * g₂.1.x + g₁.1.z * g₂.1.w = _
            rw [hw1, hz1, hw2, hz2]
            exact RExpr.eq_of_norm_eq (envGet (0 : F) [g₁.1.x, g₁.1.y, g₂.1.x, g₂.1.y])
              (e₁ := .add (.sub (.add (.mul .zero .zero) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 2)))
                          (.mul .zero .zero))
              (e₂ := .neg (.add (.mul (.var 0) (.neg (.var 3))) (.mul (.var 1) (.var 2)))) rfl
        rw [hp1, hp2, hxy12, hwz12, hz0, cpow_neg_even, cpow_mul, cpow_conj]
        have hinner :
            ComplexOver.add (ComplexOver.mul ComplexOver.zero u)
                            (ComplexOver.mul (cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1))) (ComplexOver.conj u)) =
            ComplexOver.mul (cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1))) (ComplexOver.conj u) :=
          RExpr.eq_of_norm_eq
            (envGet (ComplexOver.zero (F := F)) [cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1)), u, ComplexOver.conj u])
            (e₁ := .add (.mul .zero (.var 1)) (.mul (.var 0) (.var 2)))
            (e₂ := .mul (.var 0) (.var 2)) rfl
        rw [hinner, conj_mul_commC, conj_conjC]
        exact RExpr.eq_of_norm_eq
          (envGet (ComplexOver.zero (F := F))
            [cpow ⟨g₁.1.x, g₁.1.y⟩ (2 * (k + 1)),
             ComplexOver.conj (cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1))),
             u, ComplexOver.conj u,
             ComplexOver.mul (cpow ⟨g₂.1.x, g₂.1.y⟩ (2 * (k + 1))) (ComplexOver.conj u)])
          (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul .zero (.var 3)))
          (e₂ := .add (.mul .zero (.var 4)) (.mul (.var 0) (.mul (.var 1) (.var 2)))) rfl
  act_add g s t := by
    change harmonicAct (2 * (k + 1)) g.1 (ComplexOver.add s t) =
           ComplexOver.add (harmonicAct (2 * (k + 1)) g.1 s) (harmonicAct (2 * (k + 1)) g.1 t)
    unfold harmonicAct
    have hconj : ComplexOver.conj (ComplexOver.add s t) =
        ComplexOver.add (ComplexOver.conj s) (ComplexOver.conj t) := by
      ext
      · rfl
      · exact cr_neg_add_distrib s.im t.im
    rw [hconj]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cpow ⟨g.1.w, g.1.z⟩ (2 * (k + 1)), cpow ⟨g.1.x, g.1.y⟩ (2 * (k + 1)),
         s, t, ComplexOver.conj s, ComplexOver.conj t])
      (e₁ := .add (.mul (.var 0) (.add (.var 2) (.var 3))) (.mul (.var 1) (.add (.var 4) (.var 5))))
      (e₂ := .add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 4)))
                  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 5)))) rfl
  act_smul g c s := by
    change harmonicAct (2 * (k + 1)) g.1 (ComplexOver.smul c s) =
           ComplexOver.smul c (harmonicAct (2 * (k + 1)) g.1 s)
    unfold harmonicAct
    have hconj : ComplexOver.conj (ComplexOver.smul c s) = ComplexOver.smul c (ComplexOver.conj s) := by
      ext
      · rfl
      · exact (cr_mul_neg c s.im).symm
    rw [hconj, csmul_mul_right, csmul_mul_right, ← csmul_add]

/-! #### Explicit Pythagorean Rotation `g₀ = (3/5, 0, 0, 4/5) ∈ Pin^-(2,0)(F)` and `(3 + 4i)^N ≡ 3 + 4i (mod 5)` -/

def pythPair : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 =>
    let p := pythPair n
    (3 * p.1 - 4 * p.2, 4 * p.1 + 3 * p.2)

theorem pythPair_mod5 (n : Nat) :
    (pythPair (n + 1)).1 % 5 = 3 ∧ (pythPair (n + 1)).2 % 5 = 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold pythPair
    dsimp only
    omega

theorem pythPair_im_ne_zero (n : Nat) : (pythPair (n + 1)).2 ≠ 0 := by
  have h := (pythPair_mod5 n).2
  omega

def fiveF (F : Type) [FormallyRealField F] : F := twoF F * twoF F + 1

theorem five_ne_zeroF : fiveF F ≠ 0 :=
  sq_add_one_ne_zeroF (twoF F)

def powF (a : F) : Nat → F
  | 0 => 1
  | n + 1 => a * powF a n

theorem powF_ne_zero {a : F} (ha : a ≠ 0) (n : Nat) : powF a n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zeroF
  | succ n ih =>
    intro h
    cases mul_eq_zeroF h with
    | inl h1 => exact ha h1
    | inr h2 => exact ih h2

def c35 (F : Type) [FormallyRealField F] : F := (twoF F + 1) * (fiveF F)⁻¹
def s45 (F : Type) [FormallyRealField F] : F := (twoF F * twoF F) * (fiveF F)⁻¹

theorem c35_sq_add_s45_sq : c35 F * c35 F + s45 F * s45 F = 1 := by
  have h5 : fiveF F * (fiveF F)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ five_ne_zeroF
  calc
    c35 F * c35 F + s45 F * s45 F
        = (fiveF F * (fiveF F)⁻¹) * (fiveF F * (fiveF F)⁻¹) :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [(fiveF F)⁻¹])
            (e₁ := .add (.mul (.mul (.add (.add .one .one) .one) (.var 0))
                              (.mul (.add (.add .one .one) .one) (.var 0)))
                        (.mul (.mul (.mul (.add .one .one) (.add .one .one)) (.var 0))
                              (.mul (.mul (.add .one .one) (.add .one .one)) (.var 0))))
            (e₂ := .mul (.mul (.add (.mul (.add .one .one) (.add .one .one)) .one) (.var 0))
                        (.mul (.add (.mul (.add .one .one) (.add .one .one)) .one) (.var 0))) rfl
    _ = 1 * 1 := by rw [h5]
    _ = 1 := cr_mul_one 1

def zeta345 (F : Type) [FormallyRealField F] : ComplexOver F := ⟨c35 F, s45 F⟩

theorem cpow_zeta345_scaled (n : Nat) :
    ComplexOver.smul (powF (fiveF F) n) (cpow (zeta345 F) n) =
      ⟨crOfInt F (pythPair n).1, crOfInt F (pythPair n).2⟩ := by
  induction n with
  | zero =>
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .mul .one .one) (e₂ := .add .zero .one) rfl
    · exact cr_mul_zero 1
  | succ n ih =>
    unfold powF cpow pythPair
    have hmul :
        ComplexOver.smul (fiveF F * powF (fiveF F) n)
          (ComplexOver.mul (zeta345 F) (cpow (zeta345 F) n)) =
        ComplexOver.mul (ComplexOver.smul (fiveF F) (zeta345 F))
          (ComplexOver.smul (powF (fiveF F) n) (cpow (zeta345 F) n)) := by
      rw [cmul_smul, ← csmul_mul_right, ← csmul_mul_left]
    rw [hmul, ih]
    have h5inv : fiveF F * (fiveF F)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ five_ne_zeroF
    have hsz : ComplexOver.smul (fiveF F) (zeta345 F) = ⟨crOfInt F 3, crOfInt F 4⟩ := by
      ext
      · change fiveF F * ((twoF F + 1) * (fiveF F)⁻¹) = (((0 : F) + 1) + 1) + 1
        calc
          fiveF F * ((twoF F + 1) * (fiveF F)⁻¹) = (twoF F + 1) * (fiveF F * (fiveF F)⁻¹) :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [fiveF F, twoF F, (fiveF F)⁻¹])
              (e₁ := .mul (.var 0) (.mul (.add (.var 1) .one) (.var 2)))
              (e₂ := .mul (.add (.var 1) .one) (.mul (.var 0) (.var 2))) rfl
          _ = (twoF F + 1) * 1 := by rw [h5inv]
          _ = _ := RExpr.eq_of_norm_eq (envGet (0 : F) [])
              (e₁ := .mul (.add (.add .one .one) .one) .one)
              (e₂ := .add (.add (.add .zero .one) .one) .one) rfl
      · change fiveF F * ((twoF F * twoF F) * (fiveF F)⁻¹) = ((((0 : F) + 1) + 1) + 1) + 1
        calc
          fiveF F * ((twoF F * twoF F) * (fiveF F)⁻¹) = (twoF F * twoF F) * (fiveF F * (fiveF F)⁻¹) :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [fiveF F, twoF F, (fiveF F)⁻¹])
              (e₁ := .mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
              (e₂ := .mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 2))) rfl
          _ = (twoF F * twoF F) * 1 := by rw [h5inv]
          _ = _ := RExpr.eq_of_norm_eq (envGet (0 : F) [])
              (e₁ := .mul (.mul (.add .one .one) (.add .one .one)) .one)
              (e₂ := .add (.add (.add (.add .zero .one) .one) .one) .one) rfl
    rw [hsz]
    ext
    · change crOfInt F 3 * crOfInt F (pythPair n).1 - crOfInt F 4 * crOfInt F (pythPair n).2 =
             crOfInt F (3 * (pythPair n).1 - 4 * (pythPair n).2)
      rw [Int.sub_eq_add_neg, crOfInt_add, crOfInt_neg, crOfInt_mul, crOfInt_mul,
          CommRingOps.sub_eq_add_neg]
    · change crOfInt F 3 * crOfInt F (pythPair n).2 + crOfInt F 4 * crOfInt F (pythPair n).1 =
             crOfInt F (4 * (pythPair n).1 + 3 * (pythPair n).2)
      rw [crOfInt_add, crOfInt_mul, crOfInt_mul, CommRingOps.add_comm]

theorem cpow_zeta345_im_ne_zero (n : Nat) : (cpow (zeta345 F) (n + 1)).im ≠ 0 := by
  intro him0
  have hsc := congrArg ComplexOver.im (cpow_zeta345_scaled (F := F) (n + 1))
  change powF (fiveF F) (n + 1) * (cpow (zeta345 F) (n + 1)).im = crOfInt F (pythPair (n + 1)).2 at hsc
  rw [him0, cr_mul_zero] at hsc
  exact crOfInt_ne_zeroF (pythPair_im_ne_zero n) hsc.symm

def pinG0 (F : Type) [FormallyRealField F] : PinGroup (QuatOver.alg F) ClQuat.ι ClQuat.Q20 := by
  refine ⟨QuatOver.mul QuatOver.qi (ClQuat.ι (-(c35 F), s45 F)),
          InPin.mul ClQuat.qi_inPin_20 (InPin.gen (-(c35 F), s45 F) (Or.inl ?_))⟩
  unfold ClQuat.Q20
  calc
    (-(c35 F)) * (-(c35 F)) + s45 F * s45 F = c35 F * c35 F + s45 F * s45 F :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [c35 F, s45 F])
        (e₁ := .add (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 1) (.var 1)))
        (e₂ := .add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) rfl
    _ = 1 := c35_sq_add_s45_sq

theorem pinG0_val : (pinG0 F).1 = ⟨c35 F, 0, 0, s45 F⟩ := by
  let env := envGet (0 : F) [c35 F, s45 F]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulW .zero .one .zero .zero .zero (.neg (.var 0)) (.var 1) .zero)
      (e₂ := .var 0) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulX .zero .one .zero .zero .zero (.neg (.var 0)) (.var 1) .zero)
      (e₂ := .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulY .zero .one .zero .zero .zero (.neg (.var 0)) (.var 1) .zero)
      (e₂ := .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulZ .zero .one .zero .zero .zero (.neg (.var 0)) (.var 1) .zero)
      (e₂ := .var 1) rfl

def pinQi (F : Type) [FormallyRealField F] : PinGroup (QuatOver.alg F) ClQuat.ι ClQuat.Q20 :=
  ⟨QuatOver.qi, ClQuat.qi_inPin_20⟩

theorem harmonicRep_act_qi (k : Nat) (u : ComplexOver F) :
    (harmonicRep (F := F) k).act (pinQi F) u = ComplexOver.conj u := by
  change harmonicAct (2 * (k + 1)) QuatOver.qi u = ComplexOver.conj u
  unfold harmonicAct
  have hm : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  have hz : cpow (⟨(QuatOver.qi (F := F)).w, (QuatOver.qi (F := F)).z⟩ : ComplexOver F)
              (2 * (k + 1)) = ComplexOver.zero := by
    rw [hm]; exact cpow_zero_succ _
  have ho : cpow (⟨(QuatOver.qi (F := F)).x, (QuatOver.qi (F := F)).y⟩ : ComplexOver F)
              (2 * (k + 1)) = ComplexOver.one := cpow_one _
  rw [hz, ho]
  exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [u, ComplexOver.conj u])
    (e₁ := .add (.mul .zero (.var 0)) (.mul .one (.var 1))) (e₂ := .var 1) rfl

theorem harmonicRep_act_g0 (k : Nat) (u : ComplexOver F) :
    (harmonicRep (F := F) k).act (pinG0 F) u =
      ComplexOver.mul (cpow (zeta345 F) (2 * (k + 1))) u := by
  change harmonicAct (2 * (k + 1)) (pinG0 F).1 u = _
  rw [pinG0_val]
  unfold harmonicAct
  have hm : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  have hz : cpow (⟨(0 : F), (0 : F)⟩ : ComplexOver F) (2 * (k + 1)) = ComplexOver.zero := by
    rw [hm]; exact cpow_zero_succ _
  change ComplexOver.add (ComplexOver.mul (cpow (zeta345 F) (2 * (k + 1))) u)
                         (ComplexOver.mul (cpow ⟨0, 0⟩ (2 * (k + 1))) (ComplexOver.conj u)) = _
  rw [hz]
  exact RExpr.eq_of_norm_eq
    (envGet (ComplexOver.zero (F := F)) [cpow (zeta345 F) (2 * (k + 1)), u, ComplexOver.conj u])
    (e₁ := .add (.mul (.var 0) (.var 1)) (.mul .zero (.var 2)))
    (e₂ := .mul (.var 0) (.var 1)) rfl

/-- Every `harmonicRep k` (`k ∈ ℕ`) is an irreducible 2-dimensional `F`-representation of `Pin^-(2,0)(F)`. -/
theorem harmonicRep_irreducible (k : Nat) : PinGroupIrreducible (harmonicRep (F := F) k) := by
  refine ⟨⟨ComplexOver.one, fun h => one_ne_zeroF (congrArg ComplexOver.re h)⟩, fun W hinv => ?_⟩
  by_cases hex : ∃ u : ComplexOver F, W.mem u ∧ u ≠ ComplexOver.zero
  · right
    obtain ⟨u₀, hu₀mem, hu₀ne⟩ := hex
    let w := cpow (zeta345 F) (2 * (k + 1))
    have hwim : w.im ≠ 0 := by
      have hm : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      change (cpow (zeta345 F) (2 * (k + 1))).im ≠ 0
      rw [hm]
      exact cpow_zeta345_im_ne_zero (2 * k + 1)
    -- Step 1: produce `ComplexOver.one ∈ W`!
    have hone_mem : W.mem ComplexOver.one := by
      have hconj_mem : W.mem (ComplexOver.conj u₀) := by
        rw [← harmonicRep_act_qi k u₀]
        exact hinv (pinQi F) u₀ hu₀mem
      by_cases hre : u₀.re ≠ 0
      · have hsum : ComplexOver.add u₀ (ComplexOver.conj u₀) =
            ComplexOver.smul (twoF F * u₀.re) ComplexOver.one := by
          ext
          · exact RExpr.eq_of_norm_eq (envGet (0 : F) [u₀.re])
              (e₁ := .add (.var 0) (.var 0)) (e₂ := .mul (.mul (.add .one .one) (.var 0)) .one) rfl
          · exact RExpr.eq_of_norm_eq (envGet (0 : F) [u₀.re, u₀.im])
              (e₁ := .add (.var 1) (.neg (.var 1)))
              (e₂ := .mul (.mul (.add .one .one) (.var 0)) .zero) rfl
        have hmem2 := W.add_mem _ _ hu₀mem hconj_mem
        change W.mem (ComplexOver.add u₀ (ComplexOver.conj u₀)) at hmem2
        rw [hsum] at hmem2
        have h2re : twoF F * u₀.re ≠ 0 := fun h => by
          cases mul_eq_zeroF h with
          | inl h1 => exact two_ne_zeroF h1
          | inr h2 => exact hre h2
        have hsc := W.smul_mem (twoF F * u₀.re)⁻¹ _ hmem2
        change W.mem (ComplexOver.smul (twoF F * u₀.re)⁻¹ (ComplexOver.smul (twoF F * u₀.re) ComplexOver.one)) at hsc
        rw [← cmul_smul, inv_mul_cancelF h2re, cone_smul] at hsc
        exact hsc
      · have hre0 : u₀.re = 0 := by by_cases h : u₀.re = 0; exact h; exact False.elim (hre h)
        have him : u₀.im ≠ 0 := fun him0 => hu₀ne (by ext; exact hre0; exact him0)
        have huI : u₀ = ComplexOver.smul u₀.im ComplexOver.unitI := by
          ext
          · rw [hre0]; exact (cr_mul_zero u₀.im).symm
          · exact (cr_mul_one u₀.im).symm
        have hImem : W.mem ComplexOver.unitI := by
          have hmemI_sc : W.mem (ComplexOver.smul u₀.im ComplexOver.unitI) := huI ▸ hu₀mem
          have hsc := W.smul_mem (u₀.im)⁻¹ _ hmemI_sc
          change W.mem (ComplexOver.smul (u₀.im)⁻¹ (ComplexOver.smul u₀.im ComplexOver.unitI)) at hsc
          rw [← cmul_smul, inv_mul_cancelF him, cone_smul] at hsc
          exact hsc
        -- Apply `g₀` to `unitI`: `g₀ · i = ⟨-w.im, w.re⟩` has `.re = -w.im ≠ 0`!
        have hgI : W.mem (ComplexOver.mul w ComplexOver.unitI) := by
          rw [← harmonicRep_act_g0 k ComplexOver.unitI]
          exact hinv (pinG0 F) ComplexOver.unitI hImem
        have hgI_conj : W.mem (ComplexOver.conj (ComplexOver.mul w ComplexOver.unitI)) := by
          rw [← harmonicRep_act_qi k]
          exact hinv (pinQi F) _ hgI
        have hsumI :
            ComplexOver.add (ComplexOver.mul w ComplexOver.unitI)
                            (ComplexOver.conj (ComplexOver.mul w ComplexOver.unitI)) =
            ComplexOver.smul (-(twoF F * w.im)) ComplexOver.one := by
          ext
          · exact RExpr.eq_of_norm_eq (envGet (0 : F) [w.re, w.im])
              (e₁ := .add (.sub (.mul (.var 0) .zero) (.mul (.var 1) .one))
                          (.sub (.mul (.var 0) .zero) (.mul (.var 1) .one)))
              (e₂ := .mul (.neg (.mul (.add .one .one) (.var 1))) .one) rfl
          · exact RExpr.eq_of_norm_eq (envGet (0 : F) [w.re, w.im])
              (e₁ := .add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                          (.neg (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))))
              (e₂ := .mul (.neg (.mul (.add .one .one) (.var 1))) .zero) rfl
        have hmem3 := W.add_mem _ _ hgI hgI_conj
        change W.mem (ComplexOver.add _ _) at hmem3
        rw [hsumI] at hmem3
        have hn2w : -(twoF F * w.im) ≠ 0 := fun h => by
          have h2 : twoF F * w.im = 0 := by rw [← cr_neg_neg (twoF F * w.im), h, cr_neg_zero]
          cases mul_eq_zeroF h2 with
          | inl h1 => exact two_ne_zeroF h1
          | inr h2' => exact hwim h2'
        have hsc2 := W.smul_mem (-(twoF F * w.im))⁻¹ _ hmem3
        change W.mem (ComplexOver.smul _ (ComplexOver.smul _ _)) at hsc2
        rw [← cmul_smul, inv_mul_cancelF hn2w, cone_smul] at hsc2
        exact hsc2
    -- Step 2: from `1 ∈ W`, apply `g₀` to get `w = ⟨w.re, w.im⟩ ∈ W`, subtract `w.re • 1` to get `i ∈ W`!
    have hw_mem : W.mem w := by
      have hg1 := hinv (pinG0 F) ComplexOver.one hone_mem
      rw [harmonicRep_act_g0 k ComplexOver.one, cmul_one] at hg1
      exact hg1
    have hImem : W.mem ComplexOver.unitI := by
      have hsub : ComplexOver.add w (ComplexOver.smul (-w.re) ComplexOver.one) =
          ComplexOver.smul w.im ComplexOver.unitI := by
        ext
        · exact RExpr.eq_of_norm_eq (envGet (0 : F) [w.re, w.im])
            (e₁ := .add (.var 0) (.mul (.neg (.var 0)) .one)) (e₂ := .mul (.var 1) .zero) rfl
        · exact RExpr.eq_of_norm_eq (envGet (0 : F) [w.re, w.im])
            (e₁ := .add (.var 1) (.mul (.neg (.var 0)) .zero)) (e₂ := .mul (.var 1) .one) rfl
      have hm1 := W.add_mem _ _ hw_mem (W.smul_mem (-w.re) ComplexOver.one hone_mem)
      change W.mem (ComplexOver.add w (ComplexOver.smul (-w.re) ComplexOver.one)) at hm1
      rw [hsub] at hm1
      have hsc := W.smul_mem (w.im)⁻¹ _ hm1
      change W.mem (ComplexOver.smul (w.im)⁻¹ (ComplexOver.smul w.im ComplexOver.unitI)) at hsc
      rw [← cmul_smul, inv_mul_cancelF hwim, cone_smul] at hsc
      exact hsc
    intro z
    rw [Cl01.decomp z]
    exact W.add_mem _ _ (W.smul_mem z.re _ hone_mem) (W.smul_mem z.im _ hImem)
  · left
    intro u hu
    by_cases huz : u = ComplexOver.zero
    · exact huz
    · exact False.elim (hex ⟨u, hu, huz⟩)

/-! #### 2D Trace Invariance and Pairwise Non-Isomorphism of `harmonicRep k` -/

def tr2D (L : ComplexOver F → ComplexOver F) : F :=
  (L ComplexOver.one).re + (L ComplexOver.unitI).im

theorem tr2D_comm {U V : ComplexOver F → ComplexOver F}
    (hU_add : ∀ x y, U (ComplexOver.add x y) = ComplexOver.add (U x) (U y))
    (hU_smul : ∀ c x, U (ComplexOver.smul c x) = ComplexOver.smul c (U x))
    (hV_add : ∀ x y, V (ComplexOver.add x y) = ComplexOver.add (V x) (V y))
    (hV_smul : ∀ c x, V (ComplexOver.smul c x) = ComplexOver.smul c (V x)) :
    tr2D (fun z => U (V z)) = tr2D (fun z => V (U z)) := by
  have expandU : ∀ z : ComplexOver F,
      U z = ComplexOver.add (ComplexOver.smul z.re (U ComplexOver.one))
                            (ComplexOver.smul z.im (U ComplexOver.unitI)) := by
    intro z
    conv => lhs; rw [Cl01.decomp z]
    rw [hU_add, hU_smul, hU_smul]
  have expandV : ∀ z : ComplexOver F,
      V z = ComplexOver.add (ComplexOver.smul z.re (V ComplexOver.one))
                            (ComplexOver.smul z.im (V ComplexOver.unitI)) := by
    intro z
    conv => lhs; rw [Cl01.decomp z]
    rw [hV_add, hV_smul, hV_smul]
  unfold tr2D
  dsimp only
  rw [expandU (V ComplexOver.one), expandU (V ComplexOver.unitI),
      expandV (U ComplexOver.one), expandV (U ComplexOver.unitI)]
  let u1 := U ComplexOver.one; let u2 := U ComplexOver.unitI
  let v1 := V ComplexOver.one; let v2 := V ComplexOver.unitI
  exact RExpr.eq_of_norm_eq
    (envGet (0 : F) [u1.re, u1.im, u2.re, u2.im, v1.re, v1.im, v2.re, v2.im])
    (e₁ := .add (.add (.mul (.var 4) (.var 0)) (.mul (.var 5) (.var 2)))
                (.add (.mul (.var 6) (.var 1)) (.mul (.var 7) (.var 3))))
    (e₂ := .add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6)))
                (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7)))) rfl

theorem norm_zeta345_mul_conj (n : Nat) :
    ComplexOver.mul (cpow (zeta345 F) n) (ComplexOver.conj (cpow (zeta345 F) n)) =
      ComplexOver.one := by
  rw [← cpow_conj, ← cpow_mul]
  have h1 : ComplexOver.mul (zeta345 F) (ComplexOver.conj (zeta345 F)) = ComplexOver.one := by
    ext
    · change c35 F * c35 F - s45 F * -(s45 F) = 1
      calc
        c35 F * c35 F - s45 F * -(s45 F) = c35 F * c35 F + s45 F * s45 F :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [c35 F, s45 F])
            (e₁ := .sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.neg (.var 1))))
            (e₂ := .add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) rfl
        _ = 1 := c35_sq_add_s45_sq
    · change c35 F * -(s45 F) + s45 F * c35 F = 0
      exact RExpr.eq_of_norm_eq (envGet (0 : F) [c35 F, s45 F])
        (e₁ := .add (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.var 0))) (e₂ := .zero) rfl
  rw [h1, cpow_one]

private theorem not_iso_harmonicRep_lt {j k : Nat} (hjk : j < k) :
    ¬ Nonempty (PinGroupIso (harmonicRep (F := F) j) (harmonicRep (F := F) k)) := by
  rintro ⟨e⟩
  -- Inverse `e.invFun` is also `F`-linear:
  have hinv_add : ∀ x y, e.invFun (ComplexOver.add x y) =
      ComplexOver.add (e.invFun x) (e.invFun y) := by
    intro x y
    have h : e.toFun (e.invFun (ComplexOver.add x y)) =
        e.toFun (ComplexOver.add (e.invFun x) (e.invFun y)) := by
      rw [e.right_inv]
      change _ = e.toFun ((ComplexOver.alg F).toVecSpace.add (e.invFun x) (e.invFun y))
      rw [e.map_add, e.right_inv, e.right_inv]
      rfl
    have h2 := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h2
    exact h2
  have hinv_smul : ∀ c x, e.invFun (ComplexOver.smul c x) = ComplexOver.smul c (e.invFun x) := by
    intro c x
    have h : e.toFun (e.invFun (ComplexOver.smul c x)) =
        e.toFun (ComplexOver.smul c (e.invFun x)) := by
      rw [e.right_inv]
      change _ = e.toFun ((ComplexOver.alg F).toVecSpace.smul c (e.invFun x))
      rw [e.map_smul, e.right_inv]
      rfl
    have h2 := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h2
    exact h2
  let Lj := (harmonicRep (F := F) j).act (pinG0 F)
  let Lk := (harmonicRep (F := F) k).act (pinG0 F)
  have hconj_eq : Lk = fun z => e.toFun (Lj (e.invFun z)) := by
    funext z
    calc
      Lk z = Lk (e.toFun (e.invFun z)) := by rw [e.right_inv]
      _ = e.toFun (Lj (e.invFun z)) := (e.map_act (pinG0 F) (e.invFun z)).symm
  have htr_eq : tr2D Lk = tr2D Lj := by
    rw [hconj_eq]
    have hcomm := tr2D_comm e.map_add e.map_smul
      (V := fun z => Lj (e.invFun z))
      (fun x y => by dsimp only; rw [hinv_add]; exact (harmonicRep j).act_add (pinG0 F) _ _)
      (fun c x => by dsimp only; rw [hinv_smul]; exact (harmonicRep j).act_smul (pinG0 F) c _)
    rw [hcomm]
    have hid : (fun z => Lj (e.invFun (e.toFun z))) = Lj := by
      funext z; rw [e.left_inv]
    rw [hid]
  -- Compute `tr2D Lk = twoF F * w_k.re` and `tr2D Lj = twoF F * w_j.re`:
  let wj := cpow (zeta345 F) (2 * (j + 1))
  let wk := cpow (zeta345 F) (2 * (k + 1))
  have htr_j : tr2D Lj = twoF F * wj.re := by
    unfold tr2D Lj
    rw [harmonicRep_act_g0 j ComplexOver.one, harmonicRep_act_g0 j ComplexOver.unitI]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [wj.re, wj.im])
      (e₁ := .add (.sub (.mul (.var 0) .one) (.mul (.var 1) .zero))
                  (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)))
      (e₂ := .mul (.add .one .one) (.var 0)) rfl
  have htr_k : tr2D Lk = twoF F * wk.re := by
    unfold tr2D Lk
    rw [harmonicRep_act_g0 k ComplexOver.one, harmonicRep_act_g0 k ComplexOver.unitI]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [wk.re, wk.im])
      (e₁ := .add (.sub (.mul (.var 0) .one) (.mul (.var 1) .zero))
                  (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)))
      (e₂ := .mul (.add .one .one) (.var 0)) rfl
  rw [htr_k, htr_j] at htr_eq
  -- Deduce `wj + conj wj = wk + conj wk` in `ComplexOver F`:
  have hsumC : ComplexOver.add wj (ComplexOver.conj wj) =
      ComplexOver.add wk (ComplexOver.conj wk) := by
    ext
    · change wj.re + wj.re = wk.re + wk.re
      calc
        wj.re + wj.re = twoF F * wj.re :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [wj.re])
            (e₁ := .add (.var 0) (.var 0)) (e₂ := .mul (.add .one .one) (.var 0)) rfl
        _ = twoF F * wk.re := htr_eq.symm
        _ = wk.re + wk.re :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [wk.re])
            (e₁ := .mul (.add .one .one) (.var 0)) (e₂ := .add (.var 0) (.var 0)) rfl
    · change wj.im + (-wj.im) = wk.im + (-wk.im)
      rw [cr_add_neg_cancel, cr_add_neg_cancel]
  -- Factor `(wj - wk) * (wj * wk - 1) = 0` inside `ComplexOver F`:
  let wd := cpow (zeta345 F) (2 * (k - j))
  have hwk_eq : wk = ComplexOver.mul wj wd := by
    have hexp : 2 * (k + 1) = 2 * (j + 1) + 2 * (k - j) := by omega
    unfold wk wj wd
    rw [hexp, cpow_add]
  have hprod0 :
      ComplexOver.mul (ComplexOver.sub wd ComplexOver.one)
        (ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one) = ComplexOver.zero := by
    -- Multiply `(wj + conj wj) - (wk + conj wk) = 0` by `wj * wk`!
    have hnorm_j : ComplexOver.mul wj (ComplexOver.conj wj) = ComplexOver.one :=
      norm_zeta345_mul_conj (2 * (j + 1))
    have hnorm_k : ComplexOver.mul wk (ComplexOver.conj wk) = ComplexOver.one :=
      norm_zeta345_mul_conj (2 * (k + 1))
    calc
      ComplexOver.mul (ComplexOver.sub wd ComplexOver.one)
          (ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one)
          = ComplexOver.sub
              (ComplexOver.add (ComplexOver.mul (ComplexOver.mul wd wj) wk) ComplexOver.one)
              (ComplexOver.add (ComplexOver.mul wj wk) wd) :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [wd, wj, wk])
              (e₁ := .mul (.sub (.var 0) .one) (.sub (.mul (.var 1) (.var 2)) .one))
              (e₂ := .sub (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) .one)
                          (.add (.mul (.var 1) (.var 2)) (.var 0))) rfl
      _ = ComplexOver.sub
              (ComplexOver.add (ComplexOver.mul wk wk) (ComplexOver.mul wj (ComplexOver.conj wj)))
              (ComplexOver.add (ComplexOver.mul wj wk)
                (ComplexOver.mul wd (ComplexOver.mul wj (ComplexOver.conj wj)))) := by
            rw [cmul_comm wd wj, ← hwk_eq, hnorm_j, cmul_one]
      _ = ComplexOver.sub
              (ComplexOver.add (ComplexOver.mul wk wk) (ComplexOver.mul wj (ComplexOver.conj wj)))
              (ComplexOver.add (ComplexOver.mul wj wk) (ComplexOver.mul wk (ComplexOver.conj wj))) := by
            have hwdj : ComplexOver.mul wd (ComplexOver.mul wj (ComplexOver.conj wj)) =
                ComplexOver.mul wk (ComplexOver.conj wj) := by
              rw [← cmul_assoc, cmul_comm wd wj, ← hwk_eq]
            rw [hwdj]
      _ = ComplexOver.sub
              (ComplexOver.mul wk (ComplexOver.add wk (ComplexOver.conj wk)))
              (ComplexOver.mul wk (ComplexOver.add wj (ComplexOver.conj wj))) := by
            have hwk1 : ComplexOver.mul wj (ComplexOver.conj wj) =
                ComplexOver.mul wk (ComplexOver.conj wk) := hnorm_j.trans hnorm_k.symm
            rw [hwk1]
            exact RExpr.eq_of_norm_eq
              (envGet (ComplexOver.zero (F := F)) [wj, ComplexOver.conj wj, wk, ComplexOver.conj wk])
              (e₁ := .sub (.add (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 3)))
                          (.add (.mul (.var 0) (.var 2)) (.mul (.var 2) (.var 1))))
              (e₂ := .sub (.mul (.var 2) (.add (.var 2) (.var 3)))
                          (.mul (.var 2) (.add (.var 0) (.var 1)))) rfl
      _ = ComplexOver.sub
              (ComplexOver.mul wk (ComplexOver.add wk (ComplexOver.conj wk)))
              (ComplexOver.mul wk (ComplexOver.add wk (ComplexOver.conj wk))) := by rw [hsumC]
      _ = ComplexOver.zero :=
            RExpr.eq_of_norm_eq
              (envGet (ComplexOver.zero (F := F)) [ComplexOver.mul wk (ComplexOver.add wk (ComplexOver.conj wk))])
              (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
  -- Since `ComplexOver F` is a division algebra, one of the two factors is `zero`!
  by_cases hwd1 : ComplexOver.sub wd ComplexOver.one = ComplexOver.zero
  · have him := congrArg ComplexOver.im hwd1
    change wd.im + -(0 : F) = 0 at him
    rw [cr_neg_zero, cr_add_zero] at him
    have hm : 2 * (k - j) = (2 * (k - j) - 1) + 1 := by omega
    unfold wd at him
    rw [hm] at him
    exact cpow_zeta345_im_ne_zero (2 * (k - j) - 1) him
  · obtain ⟨uinv, _, hleft⟩ := ComplexOver.isDivision.2 _ hwd1
    change ComplexOver.mul uinv (ComplexOver.sub wd ComplexOver.one) = ComplexOver.one at hleft
    have hsum1 : ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one = ComplexOver.zero := by
      calc
        ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one
            = ComplexOver.mul ComplexOver.one (ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one) :=
              ((ComplexOver.alg F).one_mul _).symm
        _ = ComplexOver.mul (ComplexOver.mul uinv (ComplexOver.sub wd ComplexOver.one))
              (ComplexOver.sub (ComplexOver.mul wj wk) ComplexOver.one) := by rw [hleft]
        _ = ComplexOver.mul uinv ComplexOver.zero := by
              rw [cmul_assoc, hprod0]
        _ = ComplexOver.zero :=
              RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [uinv])
                (e₁ := .mul (.var 0) .zero) (e₂ := .zero) rfl
    have hmul_eq : ComplexOver.mul wj wk = cpow (zeta345 F) (2 * (j + 1) + 2 * (k + 1)) :=
      (cpow_add (zeta345 F) _ _).symm
    rw [hmul_eq] at hsum1
    have him := congrArg ComplexOver.im hsum1
    change (cpow (zeta345 F) (2 * (j + 1) + 2 * (k + 1))).im + -(0 : F) = 0 at him
    rw [cr_neg_zero, cr_add_zero] at him
    have hm : 2 * (j + 1) + 2 * (k + 1) = (2 * j + 2 * k + 3) + 1 := by omega
    rw [hm] at him
    exact cpow_zeta345_im_ne_zero (2 * j + 2 * k + 3) him

/-- **Refutation of Finite Pin Group Spectrum:**
    `Pin^-(2,0)(F)` possesses an infinite sequence `k ↦ harmonicRep k` (`k ∈ ℕ`) of
    pairwise non-isomorphic 2-dimensional irreducible representations over `F`. -/
theorem pin2Minus_infinite_pairwise_noniso_irreps :
    (∀ k : Nat, PinGroupIrreducible (harmonicRep (F := F) k)) ∧
    (∀ j k : Nat, j ≠ k →
      ¬ Nonempty (PinGroupIso (harmonicRep (F := F) j) (harmonicRep (F := F) k))) := by
  refine ⟨harmonicRep_irreducible, fun j k hne => ?_⟩
  by_cases hlt : j < k
  · exact not_iso_harmonicRep_lt hlt
  · have hgt : k < j := by omega
    rintro ⟨e⟩
    apply not_iso_harmonicRep_lt (F := F) hgt
    exact ⟨{
      toFun := e.invFun
      map_add := fun x y => by
        have h : e.toFun (e.invFun (ComplexOver.add x y)) =
            e.toFun (ComplexOver.add (e.invFun x) (e.invFun y)) := by
          rw [e.right_inv]
          change _ = e.toFun ((ComplexOver.alg F).toVecSpace.add (e.invFun x) (e.invFun y))
          rw [e.map_add, e.right_inv, e.right_inv]; rfl
        have h2 := congrArg e.invFun h
        rw [e.left_inv, e.left_inv] at h2; exact h2
      map_smul := fun c x => by
        have h : e.toFun (e.invFun (ComplexOver.smul c x)) =
            e.toFun (ComplexOver.smul c (e.invFun x)) := by
          rw [e.right_inv]
          change _ = e.toFun ((ComplexOver.alg F).toVecSpace.smul c (e.invFun x))
          rw [e.map_smul, e.right_inv]; rfl
        have h2 := congrArg e.invFun h
        rw [e.left_inv, e.left_inv] at h2; exact h2
      map_act := fun g y => by
        have h : e.toFun (e.invFun ((harmonicRep k).act g y)) =
            e.toFun ((harmonicRep j).act g (e.invFun y)) := by
          rw [e.right_inv, e.map_act, e.right_inv]
        have h2 := congrArg e.invFun h
        rw [e.left_inv, e.left_inv] at h2; exact h2
      invFun := e.toFun
      left_inv := e.right_inv
      right_inv := e.left_inv
    }⟩

end Pin2Harmonics

/-! ## 3. Positive Non-Vacuity Theorem: Complexified Clifford Algebras `ℂl_2(K)` and `ℂl_3(K)` -/

namespace ComplexSalvage

abbrev K (F : Type) := ComplexOver F

/-- `2 × 2` matrices over `K = ComplexOver F`, modelling `ℂl_2 ≅ M_2(ℂ)` and `ℂl_3^0 ≅ M_2(ℂ)`. -/
@[ext]
structure Mat2K (F : Type) where
  a11 : K F
  a12 : K F
  a21 : K F
  a22 : K F

def Mat2K.zero : Mat2K F := ⟨ComplexOver.zero, ComplexOver.zero, ComplexOver.zero, ComplexOver.zero⟩
def Mat2K.one : Mat2K F := ⟨ComplexOver.one, ComplexOver.zero, ComplexOver.zero, ComplexOver.one⟩
def Mat2K.negOne : Mat2K F :=
  ⟨ComplexOver.neg ComplexOver.one, ComplexOver.zero, ComplexOver.zero, ComplexOver.neg ComplexOver.one⟩

def Mat2K.mul (A B : Mat2K F) : Mat2K F :=
  ⟨ComplexOver.add (ComplexOver.mul A.a11 B.a11) (ComplexOver.mul A.a12 B.a21),
   ComplexOver.add (ComplexOver.mul A.a11 B.a12) (ComplexOver.mul A.a12 B.a22),
   ComplexOver.add (ComplexOver.mul A.a21 B.a11) (ComplexOver.mul A.a22 B.a21),
   ComplexOver.add (ComplexOver.mul A.a21 B.a12) (ComplexOver.mul A.a22 B.a22)⟩

def Mat2K.act (A : Mat2K F) (v : K F × K F) : K F × K F :=
  (ComplexOver.add (ComplexOver.mul A.a11 v.1) (ComplexOver.mul A.a12 v.2),
   ComplexOver.add (ComplexOver.mul A.a21 v.1) (ComplexOver.mul A.a22 v.2))

/-- Pauli matrices over `K = ComplexOver F`. -/
def pauli1 : Mat2K F := ⟨ComplexOver.zero, ComplexOver.one, ComplexOver.one, ComplexOver.zero⟩
def pauli2 : Mat2K F :=
  ⟨ComplexOver.zero, ComplexOver.neg ComplexOver.unitI, ComplexOver.unitI, ComplexOver.zero⟩
def pauli3 : Mat2K F :=
  ⟨ComplexOver.one, ComplexOver.zero, ComplexOver.zero, ComplexOver.neg ComplexOver.one⟩

def Mat2K.neg (A : Mat2K F) : Mat2K F :=
  ⟨ComplexOver.neg A.a11, ComplexOver.neg A.a12, ComplexOver.neg A.a21, ComplexOver.neg A.a22⟩

/-- `K`-linear endomorphisms of `K²` commuting with a family of `Mat2K F` generators. -/
def CommutesWith (T : Mat2K F) (gens : List (Mat2K F)) : Prop :=
  ∀ G ∈ gens, Mat2K.mul T G = Mat2K.mul G T

/-- Intertwining `K`-linear map `T : K² → K²` between two generator families `(gensA, gensB)`. -/
def IntertwinesPair (T : Mat2K F) (gensA gensB : List (Mat2K F)) : Prop :=
  ∀ idx : Nat, ∀ G₁ G₂ : Mat2K F,
    gensA[idx]? = some G₁ → gensB[idx]? = some G₂ → Mat2K.mul T G₁ = Mat2K.mul G₂ T

/-- **Positive Non-Vacuity Theorem (Complexified Clifford Algebras `ℂl_2` and `ℂl_3`):**
    1. **Even Complex Case (`ℂl_2`, generated by `σ₁, σ₃`):**
       - `σ₁² = I_2`, `σ₃² = I_2`, `σ₁ σ₃ + σ₃ σ₁ = 0`,
       - Schur uniqueness of division-ring type over `K = ComplexOver F`: EVERY `K`-linear endomorphism
         of `K²` commuting with `σ₁` and `σ₃` is a scalar matrix `c · I_2` (`c ∈ K`), so
         `End_{ℂl_2}(K²) ≅ K` (complex type only) and `Z(ℂl_2) = K · I_2`.
    2. **Odd Complex Case (`ℂl_3`, Pin spinors `S_+ = (σ₁, σ₂, σ₃)` vs `S_- = (-σ₁, -σ₂, -σ₃)`):**
       - Both `S_+` and `S_-` satisfy the Clifford relations of `ℂl_3`,
       - **Non-uniqueness on `Pin(3)`:** The ONLY `K`-linear intertwiner `T : S_+ → S_-` is `T = 0`,
         distinguished by the central volume element `ω = -i e₁ e₂ e₃` (`ω|_{S_+} = +I_2`, `ω|_{S_-} = -I_2`),
       - **Restoration of uniqueness on `Spin(3)` (`ℂl_3^0`):** Restricting `S_+` and `S_-` to the
         even generators `(e₁ e₂, e₂ e₃, e₃ e₁)` makes them **identically intertwined by `I_2`**! -/
theorem complex_clifford_non_vacuity :
    -- (1) Even `ℂl_2`: Clifford relations + Schur scalar commutant `End_{ℂl_2}(K²) = K · I_2`
    (Mat2K.mul (pauli1 (F := F)) pauli1 = Mat2K.one ∧
     Mat2K.mul (pauli3 (F := F)) pauli3 = Mat2K.one ∧
     (∀ T : Mat2K F, CommutesWith T [pauli1, pauli3] ↔
        ∃ c : K F, T = ⟨c, ComplexOver.zero, ComplexOver.zero, c⟩)) ∧
    -- (2) Odd `ℂl_3`: Central volume `(-i) σ₁ σ₂ σ₃ = +I_2` on `S_+` vs `-I_2` on `S_-`
    (Mat2K.mul ⟨ComplexOver.neg ComplexOver.unitI, ComplexOver.zero,
                ComplexOver.zero, ComplexOver.neg ComplexOver.unitI⟩
       (Mat2K.mul (pauli1 (F := F)) (Mat2K.mul pauli2 pauli3)) = Mat2K.one ∧
     Mat2K.mul ⟨ComplexOver.neg ComplexOver.unitI, ComplexOver.zero,
                ComplexOver.zero, ComplexOver.neg ComplexOver.unitI⟩
       (Mat2K.mul (Mat2K.neg (pauli1 (F := F)))
                  (Mat2K.mul (Mat2K.neg pauli2) (Mat2K.neg pauli3))) = Mat2K.negOne) ∧
    -- (3) Zero `ℂl_3` / `Pin(3)` intertwiners between `S_+` and `S_-` (`Hom_{Pin(3)}(S_+, S_-) = {0}`)
    (∀ T : Mat2K F,
      IntertwinesPair T [pauli1, pauli2, pauli3]
                        [Mat2K.neg pauli1, Mat2K.neg pauli2, Mat2K.neg pauli3] →
      T = Mat2K.zero) ∧
    -- (4) Exact isomorphism (`T = I_2 ≠ 0`) upon restricting `S_+` and `S_-` to `Spin(3)` (`ℂl_3^0`)!
    (Mat2K.one (F := F) ≠ Mat2K.zero ∧
     IntertwinesPair (Mat2K.one (F := F))
       [Mat2K.mul pauli1 pauli2, Mat2K.mul pauli2 pauli3, Mat2K.mul pauli3 pauli1]
       [Mat2K.mul (Mat2K.neg pauli1) (Mat2K.neg pauli2),
        Mat2K.mul (Mat2K.neg pauli2) (Mat2K.neg pauli3),
        Mat2K.mul (Mat2K.neg pauli3) (Mat2K.neg pauli1)]) := by
  have h2K : ∀ z : K F, ComplexOver.add z z = ComplexOver.zero → z = ComplexOver.zero := by
    intro z hz
    have hre : twoF F * z.re = 0 := by
      calc
        twoF F * z.re = z.re + z.re :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [z.re])
            (e₁ := .mul (.add .one .one) (.var 0)) (e₂ := .add (.var 0) (.var 0)) rfl
        _ = 0 := congrArg ComplexOver.re hz
    have him : twoF F * z.im = 0 := by
      calc
        twoF F * z.im = z.im + z.im :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [z.im])
            (e₁ := .mul (.add .one .one) (.var 0)) (e₂ := .add (.var 0) (.var 0)) rfl
        _ = 0 := congrArg ComplexOver.im hz
    have hre0 : z.re = 0 := by
      cases mul_eq_zeroF hre with
      | inl h => exact False.elim (two_ne_zeroF h)
      | inr h => exact h
    have him0 : z.im = 0 := by
      cases mul_eq_zeroF him with
      | inl h => exact False.elim (two_ne_zeroF h)
      | inr h => exact h
    ext; exact hre0; exact him0
  have hMatOneMul : ∀ A : Mat2K F, Mat2K.mul Mat2K.one A = A := by
    intro A
    let env := envGet (ComplexOver.zero (F := F)) [A.a11, A.a12, A.a21, A.a22]
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one (.var 0)) (.mul .zero (.var 2))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one (.var 1)) (.mul .zero (.var 3))) (e₂ := .var 1) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero (.var 0)) (.mul .one (.var 2))) (e₂ := .var 2) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero (.var 1)) (.mul .one (.var 3))) (e₂ := .var 3) rfl
  have hMatMulOne : ∀ A : Mat2K F, Mat2K.mul A Mat2K.one = A := by
    intro A
    let env := envGet (ComplexOver.zero (F := F)) [A.a11, A.a12, A.a21, A.a22]
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (e₂ := .var 1) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 2) .one) (.mul (.var 3) .zero)) (e₂ := .var 2) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 2) .zero) (.mul (.var 3) .one)) (e₂ := .var 3) rfl
  have hMatNegNeg : ∀ A B : Mat2K F, Mat2K.mul (Mat2K.neg A) (Mat2K.neg B) = Mat2K.mul A B := by
    intro A B
    let env := envGet (ComplexOver.zero (F := F)) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22]
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.neg (.var 0)) (.neg (.var 4))) (.mul (.neg (.var 1)) (.neg (.var 6))))
        (e₂ := .add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.neg (.var 0)) (.neg (.var 5))) (.mul (.neg (.var 1)) (.neg (.var 7))))
        (e₂ := .add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.neg (.var 2)) (.neg (.var 4))) (.mul (.neg (.var 3)) (.neg (.var 6))))
        (e₂ := .add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.neg (.var 2)) (.neg (.var 5))) (.mul (.neg (.var 3)) (.neg (.var 7))))
        (e₂ := .add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) rfl
  have hP23 : Mat2K.mul (pauli2 (F := F)) pauli3 =
      ⟨ComplexOver.zero, ComplexOver.unitI, ComplexOver.unitI, ComplexOver.zero⟩ := by
    let env := envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI]
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .one) (.mul (.neg (.var 0)) .zero)) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul (.neg (.var 0)) (.neg .one))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .one) (.mul .zero .zero)) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .zero) (.mul .zero (.neg .one))) (e₂ := .zero) rfl
  have hP123 : Mat2K.mul (pauli1 (F := F)) (Mat2K.mul pauli2 pauli3) =
      ⟨ComplexOver.unitI, ComplexOver.zero, ComplexOver.zero, ComplexOver.unitI⟩ := by
    rw [hP23]
    let env := envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI]
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul .one (.var 0))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero (.var 0)) (.mul .one .zero)) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one .zero) (.mul .zero (.var 0))) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one (.var 0)) (.mul .zero .zero)) (e₂ := .var 0) rfl
  have hnegIsq : ComplexOver.mul (ComplexOver.neg (ComplexOver.unitI (F := F))) ComplexOver.unitI =
      ComplexOver.one := by
    calc
      ComplexOver.mul (ComplexOver.neg (ComplexOver.unitI (F := F))) ComplexOver.unitI
          = ComplexOver.neg (ComplexOver.mul ComplexOver.unitI ComplexOver.unitI) :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
              (e₁ := .mul (.neg (.var 0)) (.var 0)) (e₂ := .neg (.mul (.var 0) (.var 0))) rfl
      _ = ComplexOver.neg (ComplexOver.neg ComplexOver.one) := by rw [ComplexOver.unitI_sq]
      _ = ComplexOver.one :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
              (e₁ := .neg (.neg .one)) (e₂ := .one) rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · -- `pauli1² = I_2`
    let env := envGet (ComplexOver.zero (F := F)) []
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul .one .one)) (e₂ := .one) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .one) (.mul .one .zero)) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one .zero) (.mul .zero .one)) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl
  · -- `pauli3² = I_2`
    let env := envGet (ComplexOver.zero (F := F)) []
    apply Mat2K.ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one .zero) (.mul .zero (.neg .one))) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .one) (.mul (.neg .one) .zero)) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul (.neg .one) (.neg .one))) (e₂ := .one) rfl
  · -- Commutant of `[pauli1, pauli3]` is `K · I_2`
    intro T
    constructor
    · intro hcomm
      have hp1 := hcomm pauli1 (by simp)
      have hp3 := hcomm pauli3 (by simp)
      have ha12 : T.a12 = ComplexOver.zero := by
        apply h2K
        calc
          ComplexOver.add T.a12 T.a12 =
              ComplexOver.sub (Mat2K.mul pauli3 T).a12 (Mat2K.mul T pauli3).a12 :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a12, T.a22])
              (e₁ := .add (.var 1) (.var 1))
              (e₂ := .sub (.add (.mul .one (.var 1)) (.mul .zero (.var 2)))
                          (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg .one)))) rfl
          _ = ComplexOver.sub (Mat2K.mul pauli3 T).a12 (Mat2K.mul pauli3 T).a12 := by rw [hp3]
          _ = ComplexOver.zero :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul pauli3 T).a12])
              (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
      have ha21 : T.a21 = ComplexOver.zero := by
        apply h2K
        calc
          ComplexOver.add T.a21 T.a21 =
              ComplexOver.sub (Mat2K.mul T pauli3).a21 (Mat2K.mul pauli3 T).a21 :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a21, T.a22])
              (e₁ := .add (.var 1) (.var 1))
              (e₂ := .sub (.add (.mul (.var 1) .one) (.mul (.var 2) .zero))
                          (.add (.mul .zero (.var 0)) (.mul (.neg .one) (.var 1)))) rfl
          _ = ComplexOver.sub (Mat2K.mul pauli3 T).a21 (Mat2K.mul pauli3 T).a21 := by rw [hp3]
          _ = ComplexOver.zero :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul pauli3 T).a21])
              (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
      have ha11_22 : T.a11 = T.a22 := by
        have hdiff : ComplexOver.sub T.a11 T.a22 = ComplexOver.zero := by
          calc
            ComplexOver.sub T.a11 T.a22 =
                ComplexOver.sub (Mat2K.mul T pauli1).a12 (Mat2K.mul pauli1 T).a12 :=
              RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a12, T.a22])
                (e₁ := .sub (.var 0) (.var 2))
                (e₂ := .sub (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                            (.add (.mul .zero (.var 1)) (.mul .one (.var 2)))) rfl
            _ = ComplexOver.sub (Mat2K.mul pauli1 T).a12 (Mat2K.mul pauli1 T).a12 := by rw [hp1]
            _ = ComplexOver.zero :=
              RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul pauli1 T).a12])
                (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
        calc
          T.a11 = ComplexOver.add (ComplexOver.sub T.a11 T.a22) T.a22 :=
            RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a22])
              (e₁ := .var 0) (e₂ := .add (.sub (.var 0) (.var 1)) (.var 1)) rfl
          _ = ComplexOver.add ComplexOver.zero T.a22 := by rw [hdiff]
          _ = T.a22 := (ComplexOver.alg F).zero_add T.a22
      refine ⟨T.a11, ?_⟩
      apply Mat2K.ext
      · rfl
      · exact ha12
      · exact ha21
      · exact ha11_22.symm
    · rintro ⟨c, rfl⟩ G hG
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hG
      let env := envGet (ComplexOver.zero (F := F)) [c]
      cases hG with
      | inl h =>
        subst h
        apply Mat2K.ext
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .zero) (.mul .zero .one))
            (e₂ := .add (.mul .zero (.var 0)) (.mul .one .zero)) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .one) (.mul .zero .zero))
            (e₂ := .add (.mul .zero .zero) (.mul .one (.var 0))) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul (.var 0) .one))
            (e₂ := .add (.mul .one (.var 0)) (.mul .zero .zero)) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.zero) .one) (.mul (.var 0) .zero))
            (e₂ := .add (.mul .one .zero) (.mul .zero (.var 0))) rfl
      | inr h =>
        subst h
        apply Mat2K.ext
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .one) (.mul .zero .zero))
            (e₂ := .add (.mul .one (.var 0)) (.mul .zero .zero)) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .zero) (.mul .zero (.neg .one)))
            (e₂ := .add (.mul .one .zero) (.mul .zero (.var 0))) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .one) (.mul (.var 0) .zero))
            (e₂ := .add (.mul .zero (.var 0)) (.mul (.neg .one) .zero)) rfl
        · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul (.var 0) (.neg .one)))
            (e₂ := .add (.mul .zero .zero) (.mul (.neg .one) (.var 0))) rfl
  · -- `(-i) * σ₁ * σ₂ * σ₃ = +I_2`
    rw [hP123]
    apply Mat2K.ext
    · change ComplexOver.add (ComplexOver.mul (ComplexOver.neg ComplexOver.unitI) ComplexOver.unitI)
                             (ComplexOver.mul ComplexOver.zero ComplexOver.zero) = ComplexOver.one
      rw [hnegIsq]
      exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
        (e₁ := .add .one (.mul .zero .zero)) (e₂ := .one) rfl
    · exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
        (e₁ := .add (.mul (.neg (.var 0)) .zero) (.mul .zero (.var 0))) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
        (e₁ := .add (.mul .zero (.var 0)) (.mul (.neg (.var 0)) .zero)) (e₂ := .zero) rfl
    · change ComplexOver.add (ComplexOver.mul ComplexOver.zero ComplexOver.zero)
                             (ComplexOver.mul (ComplexOver.neg ComplexOver.unitI) ComplexOver.unitI) = ComplexOver.one
      rw [hnegIsq]
      exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
        (e₁ := .add (.mul .zero .zero) .one) (e₂ := .one) rfl
  · -- `(-i) * (-σ₁) * (-σ₂) * (-σ₃) = -I_2`
    rw [hMatNegNeg pauli2 pauli3, hP23]
    have hNP123 :
        Mat2K.mul (Mat2K.neg (pauli1 (F := F)))
          ⟨ComplexOver.zero, ComplexOver.unitI, ComplexOver.unitI, ComplexOver.zero⟩ =
        ⟨ComplexOver.neg ComplexOver.unitI, ComplexOver.zero,
         ComplexOver.zero, ComplexOver.neg ComplexOver.unitI⟩ := by
      let env := envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI]
      apply Mat2K.ext
      · exact RExpr.eq_of_norm_eq env
          (e₁ := .add (.mul (.neg .zero) .zero) (.mul (.neg .one) (.var 0))) (e₂ := .neg (.var 0)) rfl
      · exact RExpr.eq_of_norm_eq env
          (e₁ := .add (.mul (.neg .zero) (.var 0)) (.mul (.neg .one) .zero)) (e₂ := .zero) rfl
      · exact RExpr.eq_of_norm_eq env
          (e₁ := .add (.mul (.neg .one) .zero) (.mul (.neg .zero) (.var 0))) (e₂ := .zero) rfl
      · exact RExpr.eq_of_norm_eq env
          (e₁ := .add (.mul (.neg .one) (.var 0)) (.mul (.neg .zero) .zero)) (e₂ := .neg (.var 0)) rfl
    rw [hNP123]
    have hnegNegIsq :
        ComplexOver.mul (ComplexOver.neg (ComplexOver.unitI (F := F))) (ComplexOver.neg ComplexOver.unitI) =
        ComplexOver.neg ComplexOver.one := by
      calc
        ComplexOver.mul (ComplexOver.neg (ComplexOver.unitI (F := F))) (ComplexOver.neg ComplexOver.unitI)
            = ComplexOver.mul ComplexOver.unitI ComplexOver.unitI :=
              RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
                (e₁ := .mul (.neg (.var 0)) (.neg (.var 0))) (e₂ := .mul (.var 0) (.var 0)) rfl
        _ = ComplexOver.neg ComplexOver.one := ComplexOver.unitI_sq
    apply Mat2K.ext
    · change ComplexOver.add (ComplexOver.mul (ComplexOver.neg ComplexOver.unitI) (ComplexOver.neg ComplexOver.unitI))
                             (ComplexOver.mul ComplexOver.zero ComplexOver.zero) = ComplexOver.neg ComplexOver.one
      rw [hnegNegIsq]
      exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
        (e₁ := .add (.neg .one) (.mul .zero .zero)) (e₂ := .neg .one) rfl
    · exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
        (e₁ := .add (.mul (.neg (.var 0)) .zero) (.mul .zero (.neg (.var 0)))) (e₂ := .zero) rfl
    · exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI])
        (e₁ := .add (.mul .zero (.neg (.var 0))) (.mul (.neg (.var 0)) .zero)) (e₂ := .zero) rfl
    · change ComplexOver.add (ComplexOver.mul ComplexOver.zero ComplexOver.zero)
                             (ComplexOver.mul (ComplexOver.neg ComplexOver.unitI) (ComplexOver.neg ComplexOver.unitI)) =
             ComplexOver.neg ComplexOver.one
      rw [hnegNegIsq]
      exact RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
        (e₁ := .add (.mul .zero .zero) (.neg .one)) (e₂ := .neg .one) rfl
  · -- Zero `Pin(3)` intertwiners: `T * σ_r = (-σ_r) * T` (`r = 1, 2, 3`) implies `T = 0`!
    intro T hT
    have h1 := hT 0 pauli1 (Mat2K.neg pauli1) rfl rfl
    have h2 := hT 1 pauli2 (Mat2K.neg pauli2) rfl rfl
    have h3 := hT 2 pauli3 (Mat2K.neg pauli3) rfl rfl
    have ha11 : T.a11 = ComplexOver.zero := by
      apply h2K
      calc
        ComplexOver.add T.a11 T.a11 =
            ComplexOver.sub (Mat2K.mul T pauli3).a11 (Mat2K.mul (Mat2K.neg pauli3) T).a11 :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a12, T.a21])
            (e₁ := .add (.var 0) (.var 0))
            (e₂ := .sub (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                        (.add (.mul (.neg .one) (.var 0)) (.mul (.neg .zero) (.var 2)))) rfl
        _ = ComplexOver.sub (Mat2K.mul (Mat2K.neg pauli3) T).a11
                            (Mat2K.mul (Mat2K.neg pauli3) T).a11 := by rw [h3]
        _ = ComplexOver.zero :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul (Mat2K.neg pauli3) T).a11])
            (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
    have ha22 : T.a22 = ComplexOver.zero := by
      apply h2K
      calc
        ComplexOver.add T.a22 T.a22 =
            ComplexOver.sub (Mat2K.mul (Mat2K.neg pauli3) T).a22 (Mat2K.mul T pauli3).a22 :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a12, T.a21, T.a22])
            (e₁ := .add (.var 2) (.var 2))
            (e₂ := .sub (.add (.mul (.neg .zero) (.var 0)) (.mul (.neg (.neg .one)) (.var 2)))
                        (.add (.mul (.var 1) .zero) (.mul (.var 2) (.neg .one)))) rfl
        _ = ComplexOver.sub (Mat2K.mul (Mat2K.neg pauli3) T).a22
                            (Mat2K.mul (Mat2K.neg pauli3) T).a22 := by rw [h3]
        _ = ComplexOver.zero :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul (Mat2K.neg pauli3) T).a22])
            (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
    -- From `h1` (`.a11`): `T.a12 + T.a21 = 0`. From `h2` (`.a11` multiplied by `-i`): `T.a12 - T.a21 = 0`!
    have hsum12 : ComplexOver.add T.a12 T.a21 = ComplexOver.zero := by
      calc
        ComplexOver.add T.a12 T.a21 =
            ComplexOver.sub (Mat2K.mul T pauli1).a11 (Mat2K.mul (Mat2K.neg pauli1) T).a11 :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a11, T.a12, T.a21])
            (e₁ := .add (.var 1) (.var 2))
            (e₂ := .sub (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))
                        (.add (.mul (.neg .zero) (.var 0)) (.mul (.neg .one) (.var 2)))) rfl
        _ = ComplexOver.sub (Mat2K.mul (Mat2K.neg pauli1) T).a11
                            (Mat2K.mul (Mat2K.neg pauli1) T).a11 := by rw [h1]
        _ = ComplexOver.zero :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [(Mat2K.mul (Mat2K.neg pauli1) T).a11])
            (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
    have hdiff12 : ComplexOver.sub T.a12 T.a21 = ComplexOver.zero := by
      calc
        ComplexOver.sub T.a12 T.a21 =
            ComplexOver.mul (ComplexOver.mul (ComplexOver.neg ComplexOver.unitI) ComplexOver.unitI)
              (ComplexOver.sub T.a12 T.a21) := by
          rw [hnegIsq, cone_mul]
        _ = ComplexOver.mul (ComplexOver.neg ComplexOver.unitI)
              (ComplexOver.sub (Mat2K.mul T pauli2).a11 (Mat2K.mul (Mat2K.neg pauli2) T).a11) :=
          RExpr.eq_of_norm_eq
            (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI, T.a11, T.a12, T.a21])
            (e₁ := .mul (.mul (.neg (.var 0)) (.var 0)) (.sub (.var 2) (.var 3)))
            (e₂ := .mul (.neg (.var 0))
                        (.sub (.add (.mul (.var 1) .zero) (.mul (.var 2) (.var 0)))
                              (.add (.mul (.neg .zero) (.var 1)) (.mul (.neg (.neg (.var 0))) (.var 3))))) rfl
        _ = ComplexOver.mul (ComplexOver.neg ComplexOver.unitI)
              (ComplexOver.sub (Mat2K.mul (Mat2K.neg pauli2) T).a11
                               (Mat2K.mul (Mat2K.neg pauli2) T).a11) := by rw [h2]
        _ = ComplexOver.zero :=
          RExpr.eq_of_norm_eq
            (envGet (ComplexOver.zero (F := F)) [ComplexOver.unitI, (Mat2K.mul (Mat2K.neg pauli2) T).a11])
            (e₁ := .mul (.neg (.var 0)) (.sub (.var 1) (.var 1))) (e₂ := .zero) rfl
    have ha12 : T.a12 = ComplexOver.zero := by
      apply h2K
      calc
        ComplexOver.add T.a12 T.a12 =
            ComplexOver.add (ComplexOver.add T.a12 T.a21) (ComplexOver.sub T.a12 T.a21) :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a12, T.a21])
            (e₁ := .add (.var 0) (.var 0))
            (e₂ := .add (.add (.var 0) (.var 1)) (.sub (.var 0) (.var 1))) rfl
        _ = ComplexOver.add ComplexOver.zero ComplexOver.zero := by rw [hsum12, hdiff12]
        _ = ComplexOver.zero := (ComplexOver.alg F).zero_add _
    have ha21 : T.a21 = ComplexOver.zero := by
      calc
        T.a21 = ComplexOver.sub (ComplexOver.add T.a12 T.a21) T.a12 :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [T.a12, T.a21])
            (e₁ := .var 1) (e₂ := .sub (.add (.var 0) (.var 1)) (.var 0)) rfl
        _ = ComplexOver.sub ComplexOver.zero ComplexOver.zero := by rw [hsum12, ha12]
        _ = ComplexOver.zero :=
          RExpr.eq_of_norm_eq (envGet (ComplexOver.zero (F := F)) [])
            (e₁ := .sub .zero .zero) (e₂ := .zero) rfl
    apply Mat2K.ext
    · exact ha11
    · exact ha12
    · exact ha21
    · exact ha22
  · -- `Mat2K.one ≠ Mat2K.zero`
    intro h
    exact one_ne_zeroF (congrArg (fun M => M.a11.re) h)
  · -- `IntertwinesPair Mat2K.one` on the three even `Spin(3)` generators
    intro idx G₁ G₂ hG₁ hG₂
    rw [hMatNegNeg, hMatNegNeg, hMatNegNeg] at hG₂
    have heq : G₁ = G₂ := by
      rw [hG₁] at hG₂
      exact Option.some.inj hG₂
    subst heq
    rw [hMatOneMul, hMatMulOne]

end ComplexSalvage

end InfinitePinSpectrum

end Conjecture00000007605
