/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Formalization for Conjecture 00000007605:
  Complete, sorry-free formalization over any `FormallyRealField F` (in particular `ℝ` and `ℚ`) of:
  1. Universal Clifford algebras and exact Pin subgroups under BOTH `v² = +Q(v)` and
     `v² = -Q(v)` (Atiyah–Bott–Shapiro) conventions:
     - `Cl_{0,0}(F) = F` (real division-ring type `F`),
     - `Cl_{1,0}^+(F) = Cl_{0,1}^-(F) ≅ F × F` (split: TWO non-isomorphic Pin spinor irreps!),
     - `Cl_{0,1}^+(F) = Cl_{1,0}^-(F) ≅ ComplexOver F` (complex division-ring type `C(F)`),
     - `Cl_{0,2}^+(F) = Cl_{2,0}^-(F) ≅ QuatOver F` (QUATERNIONIC division-ring type `H(F)`!),
     - `Cl_{1,1}^+(F) ≅ M_2(F)` and `Cl_{2,0}^+(F) = Cl_{0,2}^-(F) ≅ M_2(F)` (faithful spinor rep),
     - `Cl_{0,3}^+(F) = Cl_{3,0}^-(F) ≅ QuatOver F × QuatOver F` (TWO non-isomorphic quaternionic irreps!).
  2. Refutation of Claim B ("the spectrum is finite with count two (real and complex)"):
     - Explicit proof that `End_{Pin}(S_H) ≅ QuatOver F` is a non-commutative division
       `F`-algebra isomorphic neither to `F` nor to `ComplexOver F`, and that NO two-element
       family of `F`-algebras can exhaust the spinor endomorphism algebras across `(p, q)`
       (nor even across Euclidean signatures `(0,0), (1,0), (2,0)` under `-Q`).
  3. Refutation of Claim A ("unique type of irreducible representations"):
     - Complete classification of irreducible `Pin(1,0)` / `Cl_{1,0}^+(F)` spinor modules,
       proving there are EXACTLY TWO non-isomorphic irreducible spinor modules `S_+` and `S_-`
       (and likewise TWO non-isomorphic quaternionic Pin spinor modules in `Cl_{0,3}^+(F) = Cl_{3,0}^-(F)`).
  4. Refutation of Claim C ("the kernel of uniqueness is the Clifford center"):
     - On `Cl_{1,1}^+(F) ≅ M_2(F)` (where the irreducible spinor module IS unique),
       `ker(ρ) = {0} ≠ Z(M_2(F)) = F · I_2`, and `ker(ρ|_{Pin(1,1)}) = {+I_2} ≠ {±I_2} = Z(M_2(F)) ∩ Pin(1,1)`.
     - On `Cl_{0,1}^+(F) ≅ ComplexOver F`, the irreducible spinor module IS unique even though
       `Z(Cl_{0,1}^+(F)) = ComplexOver F` is strictly larger than `F · 1`, with `ker(ρ) = {0}`.
-/

import Conjecture00000007605.ModulesAndPin

namespace Conjecture00000007605

section RealCliffordCounterexamples

variable {F : Type} [FormallyRealField F]

/-- Scalar-multiplication injectivity on any nonzero vector in an `F`-vector space. -/
theorem vs_smul_neg_left {S : Type} (V : VecSpace F S) (c : F) (v : S) :
    V.smul (-c) v = V.neg (V.smul c v) := by
  apply vs_add_left_cancel V (x := V.smul c v)
  rw [← V.add_smul, cr_add_neg_cancel, vs_zero_smul, vs_add_neg_cancel]

theorem vs_smul_inj {S : Type} (V : VecSpace F S) {v : S} (hv : v ≠ V.zero)
    {c₁ c₂ : F} (h : V.smul c₁ v = V.smul c₂ v) : c₁ = c₂ := by
  by_cases hdiff : c₁ + (-c₂) = 0
  · have h1 : (c₁ + (-c₂)) + c₂ = 0 + c₂ := congrArg (fun t => t + c₂) hdiff
    rw [CommRingOps.add_assoc, CommRingOps.neg_add_cancel, cr_add_zero,
        CommRingOps.zero_add] at h1
    exact h1
  · exfalso
    have hsm0 : V.smul (c₁ + (-c₂)) v = V.zero := by
      rw [V.add_smul, h, vs_smul_neg_left, vs_add_neg_cancel]
    have hv0 : v = V.zero := by
      calc
        v = V.smul 1 v := (V.one_smul v).symm
        _ = V.smul ((c₁ + (-c₂))⁻¹ * (c₁ + (-c₂))) v := by rw [inv_mul_cancelF hdiff]
        _ = V.smul (c₁ + (-c₂))⁻¹ (V.smul (c₁ + (-c₂)) v) := V.mul_smul _ _ _
        _ = V.smul (c₁ + (-c₂))⁻¹ V.zero := by rw [hsm0]
        _ = V.zero := vs_smul_zero V _
    exact hv hv0

/-- Universal property of a Clifford algebra `(algA, ι)` for `(vecV, Q)` with sign `ε ∈ {+1, -1}`. -/
def IsUniversalClifford {V A : Type} (vecV : VecSpace F V) (Q : V → F) (ε : F)
    (algA : Alg F A) (ι : V → A) : Prop :=
  (∀ u v : V, ι (vecV.add u v) = algA.add (ι u) (ι v)) ∧
  (∀ c : F, ∀ v : V, ι (vecV.smul c v) = algA.smul c (ι v)) ∧
  (∀ v : V, algA.mul (ι v) (ι v) = algA.smul (ε * Q v) algA.one) ∧
  (∀ {B : Type} (algB : Alg F B) (f : V → B),
    (∀ u v : V, f (vecV.add u v) = algB.add (f u) (f v)) →
    (∀ c : F, ∀ v : V, f (vecV.smul c v) = algB.smul c (f v)) →
    (∀ v : V, algB.mul (f v) (f v) = algB.smul (ε * Q v) algB.one) →
    ∃ φ : AlgHom F algA algB, (∀ v : V, φ.toFun (ι v) = f v) ∧
      ∀ ψ : AlgHom F algA algB, (∀ v : V, ψ.toFun (ι v) = f v) →
        ∀ x : A, ψ.toFun x = φ.toFun x)

/-! ### 1. `Cl_{0,0}(F) = F` (Signature `(0,0)`, Real Type `F`) -/

def vecUnit (F : Type) [FormallyRealField F] : VecSpace F Unit where
  zero := ()
  add _ _ := ()
  neg _ := ()
  smul _ _ := ()
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  zero_add _ := rfl
  neg_add_cancel _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_add _ _ _ := rfl
  add_smul _ _ _ := rfl

def ι00 : Unit → F := fun _ => 0
def Q00 : Unit → F := fun _ => 0

theorem span00 (a : F) : InPinSpan (realAlg F) ι00 Q00 a := by
  have ha : a = (realAlg F).smul a (realAlg F).one := (cr_mul_one a).symm
  rw [ha]
  exact InPinSpan.smul a (InPinSpan.pin InPin.one)

def spinor00 (F : Type) [FormallyRealField F] : AlgRep F (realAlg F) (realAlg F).toVecSpace :=
  leftRegRep (realAlg F)

theorem spinor00_pinIrreducible : PinIrreducible ι00 Q00 (spinor00 F) :=
  (pinIrreducible_iff_irreducible span00 (spinor00 F)).mpr
    (leftRegRep_irreducible_of_division realAlg_isDivision)

theorem spinor00_unique_pinIrreducible {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (realAlg F) V) (hirr : PinIrreducible ι00 Q00 ρ) :
    Nonempty (PinIso ι00 Q00 (spinor00 F) ρ) := by
  rw [pinIso_iff_repIso span00]
  exact unique_irreducible_of_division realAlg_isDivision ρ
    ((pinIrreducible_iff_irreducible span00 ρ).mp hirr)

def endSpinor00IsoReal : AlgIso F (pinEndAlg ι00 Q00 (spinor00 F)) (realAlg F) :=
  (pinEndAlgIsoEndAlg span00 (spinor00 F)).trans {
    toFun := fun T => T.toFun 1
    map_one := rfl
    map_add := fun _ _ => rfl
    map_mul := fun T₁ T₂ => by
      change T₁.toFun (T₂.toFun 1) = T₁.toFun 1 * T₂.toFun 1
      have h : T₂.toFun 1 = (spinor00 F).act (T₂.toFun 1) 1 := (cr_mul_one _).symm
      conv => lhs; rw [h]
      rw [T₁.map_act]
      exact CommRingOps.mul_comm (T₂.toFun 1) (T₁.toFun 1)
    map_smul := fun _ _ => rfl
    invFun := fun c => {
      toFun := fun x => x * c
      map_add := fun x y => cr_right_distrib x y c
      map_smul := fun d x => CommRingOps.mul_assoc d x c
      map_act := fun a x => CommRingOps.mul_assoc a x c
    }
    left_inv := fun T => by
      apply Intertwiner.ext
      funext x
      dsimp only
      have hact := T.map_act x 1
      change T.toFun (x * 1) = x * T.toFun 1 at hact
      rw [cr_mul_one] at hact
      exact hact.symm
    right_inv := fun c => CommRingOps.one_mul c
  }

/-! ### 2. `Cl_{1,0}^+(F) = Cl_{0,1}^-(F)` (Split 1D: Non-Uniqueness of Irreducible Spinors!) -/

@[ext]
structure Cl10 (F : Type) where
  a : F
  b : F

namespace Cl10

def zero : Cl10 F := ⟨0, 0⟩
def one : Cl10 F := ⟨1, 0⟩
def e1 : Cl10 F := ⟨0, 1⟩
def add (x y : Cl10 F) : Cl10 F := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : Cl10 F) : Cl10 F := ⟨-x.a, -x.b⟩
def smul (c : F) (x : Cl10 F) : Cl10 F := ⟨c * x.a, c * x.b⟩
def mul (x y : Cl10 F) : Cl10 F := ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a⟩

def alg (F : Type) [FormallyRealField F] : Alg F (Cl10 F) where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  smul := smul
  add_assoc x y z := by ext <;> exact CommRingOps.add_assoc _ _ _
  add_comm x y := by ext <;> exact CommRingOps.add_comm _ _
  zero_add x := by ext <;> exact CommRingOps.zero_add _
  neg_add_cancel x := by ext <;> exact CommRingOps.neg_add_cancel _
  mul_assoc x y z := by
    let env := envGet (0 : F) [x.a, x.b, y.a, y.b, z.a, z.b]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 4))
                    (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.var 5)))
        (e₂ := .add (.mul (.var 0) (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))))
                    (.mul (.var 1) (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4))))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 5))
                    (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.var 4)))
        (e₂ := .add (.mul (.var 0) (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4))))
                    (.mul (.var 1) (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))))) rfl
  one_mul x := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
        (e₁ := .add (.mul .one (.var 0)) (.mul .zero (.var 1))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
        (e₁ := .add (.mul .one (.var 1)) (.mul .zero (.var 0))) (e₂ := .var 1) rfl
  mul_one x := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
        (e₁ := .add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
        (e₁ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (e₂ := .var 1) rfl
  left_distrib x y z := by
    let env := envGet (0 : F) [x.a, x.b, y.a, y.b, z.a, z.b]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 0) (.add (.var 2) (.var 4))) (.mul (.var 1) (.add (.var 3) (.var 5))))
        (e₂ := .add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                    (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 0) (.add (.var 3) (.var 5))) (.mul (.var 1) (.add (.var 2) (.var 4))))
        (e₂ := .add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                    (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))) rfl
  right_distrib x y z := by
    let env := envGet (0 : F) [x.a, x.b, y.a, y.b, z.a, z.b]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.var 0) (.var 2)) (.var 4)) (.mul (.add (.var 1) (.var 3)) (.var 5)))
        (e₂ := .add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
                    (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.var 0) (.var 2)) (.var 5)) (.mul (.add (.var 1) (.var 3)) (.var 4)))
        (e₂ := .add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))
                    (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4)))) rfl
  one_smul x := by ext <;> exact CommRingOps.one_mul _
  mul_smul c d x := by ext <;> exact CommRingOps.mul_assoc _ _ _
  smul_add c x y := by ext <;> exact CommRingOps.left_distrib _ _ _
  add_smul c d x := by ext <;> exact cr_right_distrib _ _ _
  smul_mul_left c x y := by
    let env := envGet (0 : F) [c, x.a, x.b, y.a, y.b]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 4)) (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) rfl
  smul_mul_right c x y := by
    let env := envGet (0 : F) [c, x.a, x.b, y.a, y.b]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 3))) (.mul (.var 2) (.mul (.var 0) (.var 4))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 4))) (.mul (.var 2) (.mul (.var 0) (.var 3))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) rfl

def ι (v : F) : Cl10 F := ⟨0, v⟩
def Qpos (v : F) : F := v * v

theorem decomp (x : Cl10 F) : x = add (smul x.a one) (smul x.b e1) := by
  ext
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
      (e₁ := .var 0) (e₂ := .add (.mul (.var 0) .one) (.mul (.var 1) .zero)) rfl
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b])
      (e₁ := .var 1) (e₂ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) rfl

theorem universal_cl10 :
    IsUniversalClifford (realAlg F).toVecSpace Qpos 1 (alg F) ι := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v; ext; exact (CommRingOps.zero_add 0).symm; rfl
  · intro c v; ext; exact (cr_mul_zero c).symm; rfl
  · intro v
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [v])
        (e₁ := .add (.mul .zero .zero) (.mul (.var 0) (.var 0)))
        (e₂ := .mul (.mul .one (.mul (.var 0) (.var 0))) .one) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [v])
        (e₁ := .add (.mul .zero (.var 0)) (.mul (.var 0) .zero))
        (e₂ := .mul (.mul .one (.mul (.var 0) (.var 0))) .zero) rfl
  · intro B algB f _ hf_smul hf_sq
    have hf1_sq : algB.mul (f 1) (f 1) = algB.one := by
      have h := hf_sq 1
      unfold Qpos at h
      rw [cr_mul_one, cr_mul_one, algB.one_smul] at h
      exact h
    let φ : AlgHom F (alg F) algB := {
      toFun := fun x => algB.add (algB.smul x.a algB.one) (algB.smul x.b (f 1))
      map_one := by
        change algB.add (algB.smul 1 algB.one) (algB.smul 0 (f 1)) = algB.one
        rw [algB.one_smul, alg_zero_smul, alg_add_zero]
      map_add := fun x y => by
        change algB.add (algB.smul (x.a + y.a) algB.one) (algB.smul (x.b + y.b) (f 1)) = _
        rw [algB.add_smul, algB.add_smul, algB.add_assoc, algB.add_assoc]
        congr 1
        rw [← algB.add_assoc, algB.add_comm (algB.smul y.a algB.one), algB.add_assoc]
      map_mul := fun x y => by
        change algB.add (algB.smul (x.a * y.a + x.b * y.b) algB.one)
                        (algB.smul (x.a * y.b + x.b * y.a) (f 1)) = _
        rw [algB.left_distrib, algB.right_distrib, algB.right_distrib]
        simp only [algB.smul_mul_left, algB.smul_mul_right, algB.one_mul, algB.mul_one,
          hf1_sq, ← algB.mul_smul, algB.add_smul]
        rw [algB.add_assoc, algB.add_assoc]
        congr 1
        rw [← algB.add_assoc, algB.add_comm (algB.smul (x.b * y.b) algB.one),
            algB.add_assoc, algB.add_comm (algB.smul (x.b * y.b) algB.one), ← algB.add_assoc,
            algB.add_comm (algB.smul (x.a * y.b) (f 1)), algB.add_assoc]
      map_smul := fun c x => by
        change algB.add (algB.smul (c * x.a) algB.one) (algB.smul (c * x.b) (f 1)) = _
        rw [algB.mul_smul, algB.mul_smul, algB.smul_add]
    }
    refine ⟨φ, ?_, ?_⟩
    · intro v
      change algB.add (algB.smul 0 algB.one) (algB.smul v (f 1)) = f v
      rw [alg_zero_smul, algB.zero_add, ← hf_smul v 1]
      congr 1
      exact cr_mul_one v
    · intro ψ hψ x
      conv => lhs; rw [decomp x]
      change ψ.toFun ((alg F).add ((alg F).smul x.a (alg F).one) ((alg F).smul x.b e1)) = φ.toFun x
      rw [ψ.map_add, ψ.map_smul, ψ.map_smul, ψ.map_one]
      have he1 : e1 (F := F) = ι 1 := rfl
      rw [he1, hψ 1]

theorem e1_inPin : InPin (alg F) ι Qpos e1 :=
  InPin.gen 1 (Or.inl (cr_mul_one 1))

theorem span10 (x : Cl10 F) : InPinSpan (alg F) ι Qpos x := by
  rw [decomp x]
  exact InPinSpan.add
    (InPinSpan.smul x.a (InPinSpan.pin InPin.one))
    (InPinSpan.smul x.b (InPinSpan.pin e1_inPin))

def spinorPlus (F : Type) [FormallyRealField F] : AlgRep F (alg F) (realAlg F).toVecSpace where
  act x s := (x.a + x.b) * s
  act_one s := by
    change ((1 : F) + 0) * s = s
    rw [cr_add_zero, CommRingOps.one_mul]
  act_mul x y s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b, s])
      (e₁ := .mul (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                        (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))) (.var 4))
      (e₂ := .mul (.add (.var 0) (.var 1)) (.mul (.add (.var 2) (.var 3)) (.var 4))) rfl
  act_add_left x y s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b, s])
      (e₁ := .mul (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (.var 4))
      (e₂ := .add (.mul (.add (.var 0) (.var 1)) (.var 4))
                  (.mul (.add (.var 2) (.var 3)) (.var 4))) rfl
  act_smul_left c x s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.a, x.b, s])
      (e₁ := .mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))) (.var 3))
      (e₂ := .mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.var 3))) rfl
  act_add_right _ s t := CommRingOps.left_distrib _ s t
  act_smul_right x c s := cr_mul_left_comm (x.a + x.b) c s

def spinorMinus (F : Type) [FormallyRealField F] : AlgRep F (alg F) (realAlg F).toVecSpace where
  act x s := (x.a - x.b) * s
  act_one s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [s])
      (e₁ := .mul (.sub .one .zero) (.var 0)) (e₂ := .var 0) rfl
  act_mul x y s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b, s])
      (e₁ := .mul (.sub (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                        (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))) (.var 4))
      (e₂ := .mul (.sub (.var 0) (.var 1)) (.mul (.sub (.var 2) (.var 3)) (.var 4))) rfl
  act_add_left x y s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [x.a, x.b, y.a, y.b, s])
      (e₁ := .mul (.sub (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (.var 4))
      (e₂ := .add (.mul (.sub (.var 0) (.var 1)) (.var 4))
                  (.mul (.sub (.var 2) (.var 3)) (.var 4))) rfl
  act_smul_left c x s :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.a, x.b, s])
      (e₁ := .mul (.sub (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))) (.var 3))
      (e₂ := .mul (.var 0) (.mul (.sub (.var 1) (.var 2)) (.var 3))) rfl
  act_add_right _ s t := CommRingOps.left_distrib _ s t
  act_smul_right x c s := cr_mul_left_comm (x.a - x.b) c s

theorem spinorPlus_pinIrreducible : PinIrreducible ι Qpos (spinorPlus F) := by
  rw [pinIrreducible_iff_irreducible span10]
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

theorem spinorMinus_pinIrreducible : PinIrreducible ι Qpos (spinorMinus F) := by
  rw [pinIrreducible_iff_irreducible span10]
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

theorem not_pinIso_spinorPlus_spinorMinus :
    ¬ Nonempty (PinIso ι Qpos (spinorPlus F) (spinorMinus F)) := by
  rintro ⟨e⟩
  have heq := e.map_pin e1 e1_inPin 1
  have hplus : (spinorPlus F).act e1 1 = 1 :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .mul (.add .zero .one) .one) (e₂ := .one) rfl
  have hminus : (spinorMinus F).act e1 (e.toFun 1) = -(e.toFun 1) :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [e.toFun 1])
      (e₁ := .mul (.sub .zero .one) (.var 0)) (e₂ := .neg (.var 0)) rfl
  rw [hplus, hminus] at heq
  have htwo : twoF F * e.toFun 1 = 0 := by
    calc
      twoF F * e.toFun 1 = e.toFun 1 + e.toFun 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [e.toFun 1])
          (e₁ := .mul (.add .one .one) (.var 0)) (e₂ := .add (.var 0) (.var 0)) rfl
      _ = -(e.toFun 1) + e.toFun 1 := by conv => lhs; lhs; rw [heq]
      _ = 0 := CommRingOps.neg_add_cancel _
  cases mul_eq_zeroF htwo with
  | inl h2 => exact two_ne_zeroF h2
  | inr ht0 =>
    have h0 : e.toFun 0 = 0 := by
      have hsm := e.map_smul 0 0
      change e.toFun (0 * 0) = 0 * e.toFun 0 at hsm
      rw [cr_zero_mul, cr_zero_mul] at hsm
      exact hsm
    have h10 : (1 : F) = 0 := by
      calc
        (1 : F) = e.invFun (e.toFun 1) := (e.left_inv 1).symm
        _ = e.invFun (e.toFun 0) := by rw [ht0, h0]
        _ = 0 := e.left_inv 0
    exact one_ne_zeroF h10

private theorem eigenLineIso {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (alg F) V) (hirr : Irreducible ρ)
    (τ : AlgRep F (alg F) (realAlg F).toVecSpace)
    (charF : Cl10 F → F)
    (hτ : ∀ x : Cl10 F, ∀ c : F, τ.act x c = charF x * c)
    {v : S} (hv : v ≠ V.zero)
    (hv_act : ∀ x : Cl10 F, ρ.act x v = V.smul (charF x) v) :
    Nonempty (RepIso τ ρ) := by
  let W : Subspace F V := {
    mem := fun s => ∃ c : F, V.smul c v = s
    zero_mem := ⟨0, vs_zero_smul V v⟩
    add_mem := by
      rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, V.add_smul c₁ c₂ v⟩
    smul_mem := by
      rintro c _ ⟨d, rfl⟩
      exact ⟨c * d, V.mul_smul c d v⟩
  }
  have hWinv : AlgInvariant ρ W := by
    rintro x _ ⟨c, rfl⟩
    refine ⟨charF x * c, ?_⟩
    rw [ρ.act_smul_right, hv_act x, ← V.mul_smul, CommRingOps.mul_comm]
  have hWsurj : ∀ s : S, W.mem s := by
    cases hirr.2 W hWinv with
    | inl hz => exact False.elim (hv (hz v ⟨1, V.one_smul v⟩))
    | inr hall => exact hall
  let invF : S → F := fun s => Classical.choose (hWsurj s)
  have hinvF : ∀ s : S, V.smul (invF s) v = s := fun s => Classical.choose_spec (hWsurj s)
  refine ⟨{
    toFun := fun c => V.smul c v
    map_add := fun c₁ c₂ => V.add_smul c₁ c₂ v
    map_smul := fun c d => V.mul_smul c d v
    map_act := fun x c => by
      rw [hτ x c, ρ.act_smul_right, hv_act x, ← V.mul_smul, CommRingOps.mul_comm]
    invFun := invF
    left_inv := fun c => vs_smul_inj V hv (hinvF (V.smul c v))
    right_inv := hinvF
  }⟩

/-- Complete classification of irreducible `Pin(1,0)` spinor modules:
    every `Pin(1,0)`-irreducible spinor module is isomorphic to `S_+` or `S_-`. -/
theorem classify_pin10_irreducible {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (alg F) V) (hirr : PinIrreducible ι Qpos ρ) :
    Nonempty (PinIso ι Qpos (spinorPlus F) ρ) ∨
    Nonempty (PinIso ι Qpos (spinorMinus F) ρ) := by
  have hirrA : Irreducible ρ := (pinIrreducible_iff_irreducible span10 ρ).mp hirr
  obtain ⟨m₀, hm₀ne⟩ := hirrA.1
  let vPlus : S := V.add m₀ (ρ.act e1 m₀)
  let vMinus : S := V.add m₀ (V.neg (ρ.act e1 m₀))
  have he1_sq : (alg F).mul e1 e1 = (alg F).one := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul .zero .zero) (.mul .one .one)) (e₂ := .one) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul .zero .one) (.mul .one .zero)) (e₂ := .zero) rfl
  by_cases hvp : vPlus ≠ V.zero
  · left
    rw [pinIso_iff_repIso span10]
    have he1_vp : ρ.act e1 vPlus = vPlus := by
      unfold vPlus
      rw [ρ.act_add_right, ← ρ.act_mul, he1_sq, ρ.act_one, V.add_comm]
    have hact_vp : ∀ x : Cl10 F, ρ.act x vPlus = V.smul (x.a + x.b) vPlus := by
      intro x
      conv => lhs; rw [decomp x]
      change ρ.act ((alg F).add ((alg F).smul x.a (alg F).one) ((alg F).smul x.b e1)) vPlus = _
      rw [ρ.act_add_left, ρ.act_smul_left, ρ.act_smul_left, ρ.act_one, he1_vp, ← V.add_smul]
    exact eigenLineIso ρ hirrA (spinorPlus F) (fun x => x.a + x.b) (fun _ _ => rfl) hvp hact_vp
  · right
    rw [pinIso_iff_repIso span10]
    have hvp0 : vPlus = V.zero := by
      by_cases h : vPlus = V.zero
      · exact h
      · exact False.elim (hvp h)
    have hvm : vMinus ≠ V.zero := by
      intro hvm0
      have h2m : V.add vPlus vMinus = V.smul (twoF F) m₀ := by
        unfold vPlus vMinus twoF
        rw [V.add_smul, V.one_smul, V.add_assoc, ← V.add_assoc (ρ.act e1 m₀),
            V.add_comm (ρ.act e1 m₀) m₀, V.add_assoc m₀, vs_add_neg_cancel, vs_add_zero]
      rw [hvp0, hvm0, V.zero_add] at h2m
      have h0 : V.smul (twoF F) m₀ = V.smul 0 m₀ := by
        rw [← h2m, vs_zero_smul]
      exact two_ne_zeroF (vs_smul_inj V hm₀ne h0)
    have he1_vm : ρ.act e1 vMinus = V.neg vMinus := by
      apply vs_add_left_cancel V (x := vMinus)
      rw [vs_add_neg_cancel]
      unfold vMinus
      rw [ρ.act_add_right, ← vs_neg_one_smul V (ρ.act e1 m₀), ρ.act_smul_right,
          ← ρ.act_mul, he1_sq, ρ.act_one, vs_neg_one_smul V, vs_neg_one_smul V,
          V.add_assoc, ← V.add_assoc (V.neg (ρ.act e1 m₀)), V.neg_add_cancel,
          V.zero_add, vs_add_neg_cancel]
    have hact_vm : ∀ x : Cl10 F, ρ.act x vMinus = V.smul (x.a - x.b) vMinus := by
      intro x
      conv => lhs; rw [decomp x]
      change ρ.act ((alg F).add ((alg F).smul x.a (alg F).one) ((alg F).smul x.b e1)) vMinus = _
      rw [ρ.act_add_left, ρ.act_smul_left, ρ.act_smul_left, ρ.act_one, he1_vm,
          ← vs_neg_one_smul V vMinus, ← V.mul_smul, cr_mul_neg, cr_mul_one,
          ← V.add_smul, ← CommRingOps.sub_eq_add_neg]
    exact eigenLineIso ρ hirrA (spinorMinus F) (fun x => x.a - x.b) (fun _ _ => rfl) hvm hact_vm

end Cl10

/-! ### 3. `Cl_{0,1}^+(F) = Cl_{1,0}^-(F) ≅ ComplexOver F` (Complex Type & Kernel vs. Center) -/

namespace Cl01

def ι (v : F) : ComplexOver F := ⟨0, v⟩
def Q01 (v : F) : F := -(v * v)   -- Signature `(0,1)` under `+Q`: `ι(v)² = +Q01(v) • 1`
def Q10 (v : F) : F := v * v      -- Signature `(1,0)` under `-Q` (ABS): `ι(v)² = -Q10(v) • 1`

theorem decomp (z : ComplexOver F) :
    z = ComplexOver.add (ComplexOver.smul z.re ComplexOver.one)
                        (ComplexOver.smul z.im ComplexOver.unitI) := by
  ext
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [z.re, z.im])
      (e₁ := .var 0) (e₂ := .add (.mul (.var 0) .one) (.mul (.var 1) .zero)) rfl
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [z.re, z.im])
      (e₁ := .var 1) (e₂ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) rfl

theorem unitI_inPin_plus : InPin (ComplexOver.alg F) ι Q01 ComplexOver.unitI :=
  InPin.gen 1 (Or.inr (by unfold Q01; rw [cr_mul_one]))

theorem unitI_inPin_minus : InPin (ComplexOver.alg F) ι Q10 ComplexOver.unitI :=
  InPin.gen 1 (Or.inl (by unfold Q10; rw [cr_mul_one]))

theorem span_plus (z : ComplexOver F) : InPinSpan (ComplexOver.alg F) ι Q01 z := by
  rw [decomp z]
  exact InPinSpan.add
    (InPinSpan.smul z.re (InPinSpan.pin InPin.one))
    (InPinSpan.smul z.im (InPinSpan.pin unitI_inPin_plus))

theorem span_minus (z : ComplexOver F) : InPinSpan (ComplexOver.alg F) ι Q10 z := by
  rw [decomp z]
  exact InPinSpan.add
    (InPinSpan.smul z.re (InPinSpan.pin InPin.one))
    (InPinSpan.smul z.im (InPinSpan.pin unitI_inPin_minus))

def spinorC (F : Type) [FormallyRealField F] :
    AlgRep F (ComplexOver.alg F) (ComplexOver.alg F).toVecSpace :=
  leftRegRep (ComplexOver.alg F)

theorem spinorC_pinIrreducible_plus : PinIrreducible ι Q01 (spinorC F) :=
  (pinIrreducible_iff_irreducible span_plus (spinorC F)).mpr
    (leftRegRep_irreducible_of_division ComplexOver.isDivision)

theorem spinorC_pinIrreducible_minus : PinIrreducible ι Q10 (spinorC F) :=
  (pinIrreducible_iff_irreducible span_minus (spinorC F)).mpr
    (leftRegRep_irreducible_of_division ComplexOver.isDivision)

theorem spinorC_unique_plus {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (ComplexOver.alg F) V) (hirr : PinIrreducible ι Q01 ρ) :
    Nonempty (PinIso ι Q01 (spinorC F) ρ) := by
  rw [pinIso_iff_repIso span_plus]
  exact unique_irreducible_of_division ComplexOver.isDivision ρ
    ((pinIrreducible_iff_irreducible span_plus ρ).mp hirr)

def endSpinorCIsoComplex_plus :
    AlgIso F (pinEndAlg ι Q01 (spinorC F)) (ComplexOver.alg F) :=
  (pinEndAlgIsoEndAlg span_plus (spinorC F)).trans {
    toFun := fun T => T.toFun ComplexOver.one
    map_one := rfl
    map_add := fun _ _ => rfl
    map_mul := fun T₁ T₂ => by
      change T₁.toFun (T₂.toFun ComplexOver.one) =
        ComplexOver.mul (T₁.toFun ComplexOver.one) (T₂.toFun ComplexOver.one)
      have h : T₂.toFun ComplexOver.one =
          (spinorC F).act (T₂.toFun ComplexOver.one) ComplexOver.one :=
        ((ComplexOver.alg F).mul_one _).symm
      conv => lhs; rw [h]
      rw [T₁.map_act]
      exact ComplexOver.isComm (T₂.toFun ComplexOver.one) (T₁.toFun ComplexOver.one)
    map_smul := fun _ _ => rfl
    invFun := fun w => {
      toFun := fun z => ComplexOver.mul z w
      map_add := fun x y => (ComplexOver.alg F).right_distrib x y w
      map_smul := fun c x => (ComplexOver.alg F).smul_mul_left c x w
      map_act := fun a x => (ComplexOver.alg F).mul_assoc a x w
    }
    left_inv := fun T => by
      apply Intertwiner.ext
      funext z
      dsimp only
      have hact := T.map_act z ComplexOver.one
      change T.toFun ((ComplexOver.alg F).mul z (ComplexOver.alg F).one) =
        ComplexOver.mul z (T.toFun ComplexOver.one) at hact
      rw [(ComplexOver.alg F).mul_one] at hact
      exact hact.symm
    right_inv := fun w => (ComplexOver.alg F).one_mul w
  }

def endSpinorCIsoComplex_minus :
    AlgIso F (pinEndAlg ι Q10 (spinorC F)) (ComplexOver.alg F) :=
  (pinEndAlgIsoEndAlg span_minus (spinorC F)).trans
    ((pinEndAlgIsoEndAlg span_plus (spinorC F)).symm.trans endSpinorCIsoComplex_plus)

/-- Refutation of Claim C on `Cl_{0,1}^+(F) ≅ ComplexOver F`:
    the irreducible spinor representation IS unique, yet the non-scalar volume generator `i`
    lies in the Clifford center `Z(Cl_{0,1}^+)` while NOT lying in `ker(spinorC)`. -/
theorem center_vs_kernel_cl01 :
    InCenter (ComplexOver.alg F) ComplexOver.unitI ∧
    (∀ c : F, ComplexOver.unitI ≠ ComplexOver.smul c ComplexOver.one) ∧
    ¬ InRepKernel (spinorC F) ComplexOver.unitI := by
  refine ⟨fun z => ComplexOver.isComm _ z, ?_, ?_⟩
  · intro c hc
    have him : (1 : F) = c * 0 := congrArg ComplexOver.im hc
    rw [cr_mul_zero] at him
    exact one_ne_zeroF him
  · intro hker
    have h := hker ComplexOver.one
    change (ComplexOver.alg F).mul ComplexOver.unitI (ComplexOver.alg F).one = ComplexOver.zero at h
    rw [(ComplexOver.alg F).mul_one] at h
    exact one_ne_zeroF (congrArg ComplexOver.im h)

end Cl01

/-! ### 4. `Cl_{0,2}^+(F) = Cl_{2,0}^-(F) ≅ QuatOver F` (Quaternionic Type `H(F)`!) -/

def vecPair (F : Type) [FormallyRealField F] : VecSpace F (F × F) where
  zero := (0, 0)
  add u v := (u.1 + v.1, u.2 + v.2)
  neg u := (-u.1, -u.2)
  smul c u := (c * u.1, c * u.2)
  add_assoc u v w := by ext <;> exact CommRingOps.add_assoc _ _ _
  add_comm u v := by ext <;> exact CommRingOps.add_comm _ _
  zero_add u := by ext <;> exact CommRingOps.zero_add _
  neg_add_cancel u := by ext <;> exact CommRingOps.neg_add_cancel _
  one_smul u := by ext <;> exact CommRingOps.one_mul _
  mul_smul c d u := by ext <;> exact CommRingOps.mul_assoc _ _ _
  smul_add c u v := by ext <;> exact CommRingOps.left_distrib _ _ _
  add_smul c d u := by ext <;> exact cr_right_distrib _ _ _

namespace ClQuat

def ι (v : F × F) : QuatOver F := ⟨0, v.1, v.2, 0⟩
def Q02 (v : F × F) : F := -(v.1 * v.1 + v.2 * v.2)  -- `(0,2)` under `v² = +Q(v)`
def Q20 (v : F × F) : F := v.1 * v.1 + v.2 * v.2     -- `(2,0)` under `v² = -Q(v)` (ABS)

theorem decomp (q : QuatOver F) :
    q = QuatOver.add
          (QuatOver.add (QuatOver.smul q.w QuatOver.one) (QuatOver.smul q.x QuatOver.qi))
          (QuatOver.add (QuatOver.smul q.y QuatOver.qj) (QuatOver.smul q.z QuatOver.qk)) := by
  let env := envGet (0 : F) [q.w, q.x, q.y, q.z]
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := .var 0)
      (e₂ := .add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                  (.add (.mul (.var 2) .zero) (.mul (.var 3) .zero))) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := .var 1)
      (e₂ := .add (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))
                  (.add (.mul (.var 2) .zero) (.mul (.var 3) .zero))) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := .var 2)
      (e₂ := .add (.add (.mul (.var 0) .zero) (.mul (.var 1) .zero))
                  (.add (.mul (.var 2) .one) (.mul (.var 3) .zero))) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := .var 3)
      (e₂ := .add (.add (.mul (.var 0) .zero) (.mul (.var 1) .zero))
                  (.add (.mul (.var 2) .zero) (.mul (.var 3) .one))) rfl

theorem qi_mul_qj_eq_qk : QuatOver.mul (QuatOver.qi (F := F)) QuatOver.qj = QuatOver.qk := by
  let env := envGet (0 : F) []
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := QuatOver.qMulW .zero .one .zero .zero .zero .zero .one .zero) (e₂ := .zero) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := QuatOver.qMulX .zero .one .zero .zero .zero .zero .one .zero) (e₂ := .zero) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := QuatOver.qMulY .zero .one .zero .zero .zero .zero .one .zero) (e₂ := .zero) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := QuatOver.qMulZ .zero .one .zero .zero .zero .zero .one .zero) (e₂ := .one) rfl

theorem cliff_sq_02 (v : F × F) :
    QuatOver.mul (ι v) (ι v) = QuatOver.smul (1 * Q02 v) QuatOver.one := by
  let env := envGet (0 : F) [v.1, v.2]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulW .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul .one (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))) .one) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulX .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul .one (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulY .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul .one (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulZ .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul .one (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))) .zero) rfl

theorem cliff_sq_20 (v : F × F) :
    QuatOver.mul (ι v) (ι v) = QuatOver.smul (-(1 : F) * Q20 v) QuatOver.one := by
  let env := envGet (0 : F) [v.1, v.2]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulW .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul (.neg .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) .one) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulX .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul (.neg .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulY .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul (.neg .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := QuatOver.qMulZ .zero (.var 0) (.var 1) .zero .zero (.var 0) (.var 1) .zero)
      (e₂ := .mul (.mul (.neg .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) .zero) rfl

theorem qi_inPin_02 : InPin (QuatOver.alg F) ι Q02 QuatOver.qi :=
  InPin.gen (1, 0) (Or.inr (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .neg (.add (.mul .one .one) (.mul .zero .zero))) (e₂ := .neg .one) rfl))

theorem qj_inPin_02 : InPin (QuatOver.alg F) ι Q02 QuatOver.qj :=
  InPin.gen (0, 1) (Or.inr (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .neg (.add (.mul .zero .zero) (.mul .one .one))) (e₂ := .neg .one) rfl))

theorem qk_inPin_02 : InPin (QuatOver.alg F) ι Q02 QuatOver.qk := by
  rw [← qi_mul_qj_eq_qk]
  exact InPin.mul qi_inPin_02 qj_inPin_02

theorem span_02 (q : QuatOver F) : InPinSpan (QuatOver.alg F) ι Q02 q := by
  rw [decomp q]
  exact InPinSpan.add
    (InPinSpan.add (InPinSpan.smul q.w (InPinSpan.pin InPin.one))
                   (InPinSpan.smul q.x (InPinSpan.pin qi_inPin_02)))
    (InPinSpan.add (InPinSpan.smul q.y (InPinSpan.pin qj_inPin_02))
                   (InPinSpan.smul q.z (InPinSpan.pin qk_inPin_02)))

theorem qi_inPin_20 : InPin (QuatOver.alg F) ι Q20 QuatOver.qi :=
  InPin.gen (1, 0) (Or.inl (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .add (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl))

theorem qj_inPin_20 : InPin (QuatOver.alg F) ι Q20 QuatOver.qj :=
  InPin.gen (0, 1) (Or.inl (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .add (.mul .zero .zero) (.mul .one .one)) (e₂ := .one) rfl))

theorem qk_inPin_20 : InPin (QuatOver.alg F) ι Q20 QuatOver.qk := by
  rw [← qi_mul_qj_eq_qk]
  exact InPin.mul qi_inPin_20 qj_inPin_20

theorem span_20 (q : QuatOver F) : InPinSpan (QuatOver.alg F) ι Q20 q := by
  rw [decomp q]
  exact InPinSpan.add
    (InPinSpan.add (InPinSpan.smul q.w (InPinSpan.pin InPin.one))
                   (InPinSpan.smul q.x (InPinSpan.pin qi_inPin_20)))
    (InPinSpan.add (InPinSpan.smul q.y (InPinSpan.pin qj_inPin_20))
                   (InPinSpan.smul q.z (InPinSpan.pin qk_inPin_20)))

/-- The unique irreducible real/F-spinor module `S_H = QuatOver F` of `Pin^+(0,2)` and `Pin^-(2,0)`. -/
def spinorH (F : Type) [FormallyRealField F] :
    AlgRep F (QuatOver.alg F) (QuatOver.alg F).toVecSpace :=
  leftRegRep (QuatOver.alg F)

theorem spinorH_pinIrreducible_02 : PinIrreducible ι Q02 (spinorH F) :=
  (pinIrreducible_iff_irreducible span_02 (spinorH F)).mpr
    (leftRegRep_irreducible_of_division QuatOver.isDivision)

theorem spinorH_pinIrreducible_20 : PinIrreducible ι Q20 (spinorH F) :=
  (pinIrreducible_iff_irreducible span_20 (spinorH F)).mpr
    (leftRegRep_irreducible_of_division QuatOver.isDivision)

theorem spinorH_unique_02 {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (QuatOver.alg F) V) (hirr : PinIrreducible ι Q02 ρ) :
    Nonempty (PinIso ι Q02 (spinorH F) ρ) := by
  rw [pinIso_iff_repIso span_02]
  exact unique_irreducible_of_division QuatOver.isDivision ρ
    ((pinIrreducible_iff_irreducible span_02 ρ).mp hirr)

theorem spinorH_unique_20 {S : Type} {V : VecSpace F S}
    (ρ : AlgRep F (QuatOver.alg F) V) (hirr : PinIrreducible ι Q20 ρ) :
    Nonempty (PinIso ι Q20 (spinorH F) ρ) := by
  rw [pinIso_iff_repIso span_20]
  exact unique_irreducible_of_division QuatOver.isDivision ρ
    ((pinIrreducible_iff_irreducible span_20 ρ).mp hirr)

private theorem quat_conj_add (p q : QuatOver F) :
    QuatOver.conj (QuatOver.add p q) = QuatOver.add (QuatOver.conj p) (QuatOver.conj q) := by
  ext
  · rfl
  · exact cr_neg_add_distrib p.x q.x
  · exact cr_neg_add_distrib p.y q.y
  · exact cr_neg_add_distrib p.z q.z

private theorem quat_conj_smul (c : F) (p : QuatOver F) :
    QuatOver.conj (QuatOver.smul c p) = QuatOver.smul c (QuatOver.conj p) := by
  ext
  · rfl
  · exact (cr_mul_neg c p.x).symm
  · exact (cr_mul_neg c p.y).symm
  · exact (cr_mul_neg c p.z).symm

/-- Explicit `F`-algebra isomorphism `End_{QuatOver F}(S_H) ≅ QuatOver F` via
    `T ↦ conj(T(1))` with inverse `q ↦ (x ↦ x * conj(q))`. -/
def endAlgSpinorHIsoQuat : AlgIso F (endAlg (spinorH F)) (QuatOver.alg F) where
  toFun := fun T => QuatOver.conj (T.toFun QuatOver.one)
  map_one := by
    ext
    · rfl
    · exact cr_neg_zero
    · exact cr_neg_zero
    · exact cr_neg_zero
  map_add := fun T₁ T₂ => quat_conj_add (T₁.toFun QuatOver.one) (T₂.toFun QuatOver.one)
  map_mul := fun T₁ T₂ => by
    change QuatOver.conj (T₁.toFun (T₂.toFun QuatOver.one)) =
      QuatOver.mul (QuatOver.conj (T₁.toFun QuatOver.one)) (QuatOver.conj (T₂.toFun QuatOver.one))
    have h : T₂.toFun QuatOver.one = (spinorH F).act (T₂.toFun QuatOver.one) QuatOver.one :=
      ((QuatOver.alg F).mul_one _).symm
    conv => lhs; rw [h]
    rw [T₁.map_act]
    exact QuatOver.conj_mul (T₂.toFun QuatOver.one) (T₁.toFun QuatOver.one)
  map_smul := fun c T => quat_conj_smul c (T.toFun QuatOver.one)
  invFun := fun q => {
    toFun := fun x => QuatOver.mul x (QuatOver.conj q)
    map_add := fun x y => (QuatOver.alg F).right_distrib x y (QuatOver.conj q)
    map_smul := fun c x => (QuatOver.alg F).smul_mul_left c x (QuatOver.conj q)
    map_act := fun a x => (QuatOver.alg F).mul_assoc a x (QuatOver.conj q)
  }
  left_inv := fun T => by
    apply Intertwiner.ext
    funext x
    dsimp only
    rw [QuatOver.conj_conj]
    have hact := T.map_act x QuatOver.one
    change T.toFun ((QuatOver.alg F).mul x (QuatOver.alg F).one) =
      QuatOver.mul x (T.toFun QuatOver.one) at hact
    rw [(QuatOver.alg F).mul_one] at hact
    exact hact.symm
  right_inv := fun q => by
    change QuatOver.conj ((QuatOver.alg F).mul (QuatOver.alg F).one (QuatOver.conj q)) = q
    rw [(QuatOver.alg F).one_mul, QuatOver.conj_conj]

def endSpinorHIsoQuat_02 : AlgIso F (pinEndAlg ι Q02 (spinorH F)) (QuatOver.alg F) :=
  (pinEndAlgIsoEndAlg span_02 (spinorH F)).trans endAlgSpinorHIsoQuat

def endSpinorHIsoQuat_20 : AlgIso F (pinEndAlg ι Q20 (spinorH F)) (QuatOver.alg F) :=
  (pinEndAlgIsoEndAlg span_20 (spinorH F)).trans endAlgSpinorHIsoQuat

/-- **Decisive Refutation of Claim B ("the spectrum is finite with count two (real and complex)"):**
    The endomorphism algebra `End_{Pin}(S_H)` of the unique irreducible Pin spinor representation
    of `Cl_{0,2}^+(F)` (and of Euclidean `Pin^-(2,0)` under Atiyah–Bott–Shapiro's `-Q` convention)
    is a division `F`-algebra isomorphic NEITHER to `F` (real) NOR to `ComplexOver F` (complex). -/
theorem quat_spinor_endAlg_neither_real_nor_complex :
    IsDivisionAlg (pinEndAlg ι Q02 (spinorH F)) ∧
    ¬ IsCommAlg (pinEndAlg ι Q02 (spinorH F)) ∧
    ¬ Nonempty (AlgIso F (pinEndAlg ι Q02 (spinorH F)) (realAlg F)) ∧
    ¬ Nonempty (AlgIso F (pinEndAlg ι Q02 (spinorH F)) (ComplexOver.alg F)) ∧
    ¬ Nonempty (AlgIso F (pinEndAlg ι Q20 (spinorH F)) (realAlg F)) ∧
    ¬ Nonempty (AlgIso F (pinEndAlg ι Q20 (spinorH F)) (ComplexOver.alg F)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let e := endSpinorHIsoQuat_02 (F := F).symm
    refine ⟨fun h10 => ?_, fun T hT => ?_⟩
    · have := congrArg endSpinorHIsoQuat_02.toFun h10
      rw [endSpinorHIsoQuat_02.map_one, algHom_map_zero endSpinorHIsoQuat_02.toAlgHom] at this
      exact QuatOver.isDivision.1 this
    · have hq0 : endSpinorHIsoQuat_02.toFun T ≠ QuatOver.zero := by
        intro hq
        apply hT
        calc
          T = e.toFun (endSpinorHIsoQuat_02.toFun T) := (endSpinorHIsoQuat_02.left_inv T).symm
          _ = e.toFun QuatOver.zero := by rw [hq]
          _ = _ := algHom_map_zero e.toAlgHom
      obtain ⟨qinv, hmul1, hmul2⟩ := QuatOver.isDivision.2 _ hq0
      refine ⟨e.toFun qinv, ?_, ?_⟩
      · calc
          (pinEndAlg ι Q02 (spinorH F)).mul T (e.toFun qinv)
              = (pinEndAlg ι Q02 (spinorH F)).mul
                  (e.toFun (endSpinorHIsoQuat_02.toFun T)) (e.toFun qinv) := by
                  congr 1
                  exact (endSpinorHIsoQuat_02.left_inv T).symm
          _ = e.toFun ((QuatOver.alg F).mul (endSpinorHIsoQuat_02.toFun T) qinv) :=
                (e.map_mul _ _).symm
          _ = e.toFun (QuatOver.alg F).one := by rw [hmul1]
          _ = _ := e.map_one
      · calc
          (pinEndAlg ι Q02 (spinorH F)).mul (e.toFun qinv) T
              = (pinEndAlg ι Q02 (spinorH F)).mul (e.toFun qinv)
                  (e.toFun (endSpinorHIsoQuat_02.toFun T)) := by
                  congr 1
                  exact (endSpinorHIsoQuat_02.left_inv T).symm
          _ = e.toFun ((QuatOver.alg F).mul qinv (endSpinorHIsoQuat_02.toFun T)) :=
                (e.map_mul _ _).symm
          _ = e.toFun (QuatOver.alg F).one := by rw [hmul2]
          _ = _ := e.map_one
  · intro hcomm
    exact QuatOver.not_isComm (isCommAlg_of_algIso endSpinorHIsoQuat_02 hcomm)
  · rintro ⟨e⟩
    exact not_algIso_real_quat ⟨e.symm.trans endSpinorHIsoQuat_02⟩
  · rintro ⟨e⟩
    exact not_algIso_complex_quat ⟨e.symm.trans endSpinorHIsoQuat_02⟩
  · rintro ⟨e⟩
    exact not_algIso_real_quat ⟨e.symm.trans endSpinorHIsoQuat_20⟩
  · rintro ⟨e⟩
    exact not_algIso_complex_quat ⟨e.symm.trans endSpinorHIsoQuat_20⟩

/-- **Pigeonhole Impossibility of ANY Count-Two Type Classification:**
    No two `F`-algebras `T₁, T₂` whatsoever can cover (up to `F`-algebra isomorphism)
    the spinor endomorphism algebras of `Pin(0,0)`, `Pin(0,1)`, and `Pin(0,2)`
    (nor of Euclidean `Pin^-(0,0)`, `Pin^-(1,0)`, and `Pin^-(2,0)`). -/
theorem no_two_types_cover_pin_spinor_endAlgs {B₁ B₂ : Type}
    (alg₁ : Alg F B₁) (alg₂ : Alg F B₂) :
    ¬ ((Nonempty (AlgIso F (pinEndAlg ι00 Q00 (spinor00 F)) alg₁) ∨
        Nonempty (AlgIso F (pinEndAlg ι00 Q00 (spinor00 F)) alg₂)) ∧
       (Nonempty (AlgIso F (pinEndAlg Cl01.ι Cl01.Q01 (Cl01.spinorC F)) alg₁) ∨
        Nonempty (AlgIso F (pinEndAlg Cl01.ι Cl01.Q01 (Cl01.spinorC F)) alg₂)) ∧
       (Nonempty (AlgIso F (pinEndAlg ι Q02 (spinorH F)) alg₁) ∨
        Nonempty (AlgIso F (pinEndAlg ι Q02 (spinorH F)) alg₂))) := by
  rintro ⟨hR, hC, hH⟩
  cases hR with
  | inl hR1 =>
    obtain ⟨eR1⟩ := hR1
    cases hC with
    | inl hC1 =>
      obtain ⟨eC1⟩ := hC1
      exact not_algIso_real_complex
        ⟨endSpinor00IsoReal.symm.trans (eR1.trans (eC1.symm.trans Cl01.endSpinorCIsoComplex_plus))⟩
    | inr hC2 =>
      obtain ⟨eC2⟩ := hC2
      cases hH with
      | inl hH1 =>
        obtain ⟨eH1⟩ := hH1
        exact not_algIso_real_quat
          ⟨endSpinor00IsoReal.symm.trans (eR1.trans (eH1.symm.trans endSpinorHIsoQuat_02))⟩
      | inr hH2 =>
        obtain ⟨eH2⟩ := hH2
        exact not_algIso_complex_quat
          ⟨Cl01.endSpinorCIsoComplex_plus.symm.trans (eC2.trans (eH2.symm.trans endSpinorHIsoQuat_02))⟩
  | inr hR2 =>
    obtain ⟨eR2⟩ := hR2
    cases hC with
    | inl hC1 =>
      obtain ⟨eC1⟩ := hC1
      cases hH with
      | inl hH1 =>
        obtain ⟨eH1⟩ := hH1
        exact not_algIso_complex_quat
          ⟨Cl01.endSpinorCIsoComplex_plus.symm.trans (eC1.trans (eH1.symm.trans endSpinorHIsoQuat_02))⟩
      | inr hH2 =>
        obtain ⟨eH2⟩ := hH2
        exact not_algIso_real_quat
          ⟨endSpinor00IsoReal.symm.trans (eR2.trans (eH2.symm.trans endSpinorHIsoQuat_02))⟩
    | inr hC2 =>
      obtain ⟨eC2⟩ := hC2
      exact not_algIso_real_complex
        ⟨endSpinor00IsoReal.symm.trans (eR2.trans (eC2.symm.trans Cl01.endSpinorCIsoComplex_plus))⟩

end ClQuat

/-! ### 5. `Cl_{1,1}^+(F) ≅ M_2(F)` and `Cl_{2,0}^+(F) ≅ M_2(F)` (Faithful Spinor Rep vs. Center) -/

@[ext]
structure Mat2 (F : Type) where
  a11 : F
  a12 : F
  a21 : F
  a22 : F

namespace Mat2

def zero : Mat2 F := ⟨0, 0, 0, 0⟩
def one : Mat2 F := ⟨1, 0, 0, 1⟩
def e11 : Mat2 F := ⟨1, 0, 0, 0⟩
def e12 : Mat2 F := ⟨0, 1, 0, 0⟩
def e21 : Mat2 F := ⟨0, 0, 1, 0⟩
def e22 : Mat2 F := ⟨0, 0, 0, 1⟩

def gamma1 : Mat2 F := ⟨1, 0, 0, -(1 : F)⟩
def gamma2Minus : Mat2 F := ⟨0, 1, -(1 : F), 0⟩   -- `gamma2Minus² = -I_2` (`Cl_{1,1}^+`)
def gamma2Plus : Mat2 F := ⟨0, 1, 1, 0⟩            -- `gamma2Plus² = +I_2` (`Cl_{2,0}^+ = Cl_{0,2}^-`)

def add (A B : Mat2 F) : Mat2 F :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩
def neg (A : Mat2 F) : Mat2 F :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩
def smul (c : F) (A : Mat2 F) : Mat2 F :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩
def mul (A B : Mat2 F) : Mat2 F :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩

theorem mul_assocM (A B C : Mat2 F) : mul (mul A B) C = mul A (mul B C) := by
  let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22, C.a11, C.a12, C.a21, C.a22]
  let a11 := RExpr.var 0; let a12 := RExpr.var 1; let a21 := RExpr.var 2; let a22 := RExpr.var 3
  let b11 := RExpr.var 4; let b12 := RExpr.var 5; let b21 := RExpr.var 6; let b22 := RExpr.var 7
  let c11 := RExpr.var 8; let c12 := RExpr.var 9; let c21 := RExpr.var 10; let c22 := RExpr.var 11
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul a11 b11) (.mul a12 b21)) c11) (.mul (.add (.mul a11 b12) (.mul a12 b22)) c21))
      (e₂ := .add (.mul a11 (.add (.mul b11 c11) (.mul b12 c21))) (.mul a12 (.add (.mul b21 c11) (.mul b22 c21)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul a11 b11) (.mul a12 b21)) c12) (.mul (.add (.mul a11 b12) (.mul a12 b22)) c22))
      (e₂ := .add (.mul a11 (.add (.mul b11 c12) (.mul b12 c22))) (.mul a12 (.add (.mul b21 c12) (.mul b22 c22)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul a21 b11) (.mul a22 b21)) c11) (.mul (.add (.mul a21 b12) (.mul a22 b22)) c21))
      (e₂ := .add (.mul a21 (.add (.mul b11 c11) (.mul b12 c21))) (.mul a22 (.add (.mul b21 c11) (.mul b22 c21)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul a21 b11) (.mul a22 b21)) c12) (.mul (.add (.mul a21 b12) (.mul a22 b22)) c22))
      (e₂ := .add (.mul a21 (.add (.mul b11 c12) (.mul b12 c22))) (.mul a22 (.add (.mul b21 c12) (.mul b22 c22)))) rfl

theorem left_distribM (A B C : Mat2 F) : mul A (add B C) = add (mul A B) (mul A C) := by
  let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22, C.a11, C.a12, C.a21, C.a22]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 0) (.add (.var 4) (.var 8))) (.mul (.var 1) (.add (.var 6) (.var 10))))
      (e₂ := .add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 10)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 0) (.add (.var 5) (.var 9))) (.mul (.var 1) (.add (.var 7) (.var 11))))
      (e₂ := .add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 11)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 2) (.add (.var 4) (.var 8))) (.mul (.var 3) (.add (.var 6) (.var 10))))
      (e₂ := .add (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 10)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 2) (.add (.var 5) (.var 9))) (.mul (.var 3) (.add (.var 7) (.var 11))))
      (e₂ := .add (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.add (.mul (.var 2) (.var 9)) (.mul (.var 3) (.var 11)))) rfl

theorem right_distribM (A B C : Mat2 F) : mul (add A B) C = add (mul A C) (mul B C) := by
  let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22, C.a11, C.a12, C.a21, C.a22]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.var 0) (.var 4)) (.var 8)) (.mul (.add (.var 1) (.var 5)) (.var 10)))
      (e₂ := .add (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 10))) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.var 0) (.var 4)) (.var 9)) (.mul (.add (.var 1) (.var 5)) (.var 11)))
      (e₂ := .add (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 11))) (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.var 2) (.var 6)) (.var 8)) (.mul (.add (.var 3) (.var 7)) (.var 10)))
      (e₂ := .add (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 10))) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.var 2) (.var 6)) (.var 9)) (.mul (.add (.var 3) (.var 7)) (.var 11)))
      (e₂ := .add (.add (.mul (.var 2) (.var 9)) (.mul (.var 3) (.var 11))) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11)))) rfl

def alg (F : Type) [FormallyRealField F] : Alg F (Mat2 F) where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  smul := smul
  add_assoc A B C := by ext <;> exact CommRingOps.add_assoc _ _ _
  add_comm A B := by ext <;> exact CommRingOps.add_comm _ _
  zero_add A := by ext <;> exact CommRingOps.zero_add _
  neg_add_cancel A := by ext <;> exact CommRingOps.neg_add_cancel _
  mul_assoc := mul_assocM
  one_mul A := by
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22]
    ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one (.var 0)) (.mul .zero (.var 2))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .one (.var 1)) (.mul .zero (.var 3))) (e₂ := .var 1) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero (.var 0)) (.mul .one (.var 2))) (e₂ := .var 2) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero (.var 1)) (.mul .one (.var 3))) (e₂ := .var 3) rfl
  mul_one A := by
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22]
    ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (e₂ := .var 1) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 2) .one) (.mul (.var 3) .zero)) (e₂ := .var 2) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 2) .zero) (.mul (.var 3) .one)) (e₂ := .var 3) rfl
  left_distrib := left_distribM
  right_distrib := right_distribM
  one_smul A := by ext <;> exact CommRingOps.one_mul _
  mul_smul c d A := by ext <;> exact CommRingOps.mul_assoc _ _ _
  smul_add c A B := by ext <;> exact CommRingOps.left_distrib _ _ _
  add_smul c d A := by ext <;> exact cr_right_distrib _ _ _
  smul_mul_left c A B := by
    let env := envGet (0 : F) [c, A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22]
    ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 7)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 7)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 6)) (.mul (.mul (.var 0) (.var 2)) (.var 8)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 8)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 7)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 7)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.mul (.var 0) (.var 3)) (.var 6)) (.mul (.mul (.var 0) (.var 4)) (.var 8)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 8)))) rfl
  smul_mul_right c A B := by
    let env := envGet (0 : F) [c, A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22]
    ext
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 5))) (.mul (.var 2) (.mul (.var 0) (.var 7))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 7)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 6))) (.mul (.var 2) (.mul (.var 0) (.var 8))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 8)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 3) (.mul (.var 0) (.var 5))) (.mul (.var 4) (.mul (.var 0) (.var 7))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 7)))) rfl
    · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.var 3) (.mul (.var 0) (.var 6))) (.mul (.var 4) (.mul (.var 0) (.var 8))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 8)))) rfl

def ι11 (v : F × F) : Mat2 F := ⟨v.1, v.2, -v.2, -v.1⟩
def Q11 (v : F × F) : F := v.1 * v.1 - v.2 * v.2

theorem gamma1_inPin11 : InPin (alg F) ι11 Q11 gamma1 := by
  have hg : gamma1 (F := F) = ι11 (1, 0) := by
    ext
    · rfl
    · rfl
    · exact cr_neg_zero.symm
    · rfl
  rw [hg]
  exact InPin.gen (1, 0) (Or.inl (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .sub (.mul .one .one) (.mul .zero .zero)) (e₂ := .one) rfl))

theorem gamma2_inPin11 : InPin (alg F) ι11 Q11 gamma2Minus := by
  have hg : gamma2Minus (F := F) = ι11 (0, 1) := by
    ext
    · rfl
    · rfl
    · rfl
    · exact cr_neg_zero.symm
  rw [hg]
  exact InPin.gen (0, 1) (Or.inr (RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .sub (.mul .zero .zero) (.mul .one .one)) (e₂ := .neg .one) rfl))

theorem span11 (A : Mat2 F) : InPinSpan (alg F) ι11 Q11 A := by
  have hdecomp :
      A = add (add (smul (halfF F * (A.a11 + A.a22)) one)
                   (smul (halfF F * (A.a11 - A.a22)) gamma1))
              (add (smul (halfF F * (A.a12 - A.a21)) gamma2Minus)
                   (smul (halfF F * (A.a12 + A.a21)) (mul gamma1 gamma2Minus))) := by
    have h2h : twoF F * halfF F = 1 := two_mul_halfF
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, halfF F]
    ext
    · calc
        A.a11 = A.a11 * (twoF F * halfF F) := by rw [h2h, cr_mul_one]
        _ = _ := RExpr.eq_of_norm_eq env
            (e₁ := .mul (.var 0) (.mul (.add .one .one) (.var 4)))
            (e₂ := .add (.add (.mul (.mul (.var 4) (.add (.var 0) (.var 3))) .one)
                              (.mul (.mul (.var 4) (.sub (.var 0) (.var 3))) .one))
                        (.add (.mul (.mul (.var 4) (.sub (.var 1) (.var 2))) .zero)
                              (.mul (.mul (.var 4) (.add (.var 1) (.var 2)))
                                    (.add (.mul .one .zero) (.mul .zero (.neg .one)))))) rfl
    · calc
        A.a12 = A.a12 * (twoF F * halfF F) := by rw [h2h, cr_mul_one]
        _ = _ := RExpr.eq_of_norm_eq env
            (e₁ := .mul (.var 1) (.mul (.add .one .one) (.var 4)))
            (e₂ := .add (.add (.mul (.mul (.var 4) (.add (.var 0) (.var 3))) .zero)
                              (.mul (.mul (.var 4) (.sub (.var 0) (.var 3))) .zero))
                        (.add (.mul (.mul (.var 4) (.sub (.var 1) (.var 2))) .one)
                              (.mul (.mul (.var 4) (.add (.var 1) (.var 2)))
                                    (.add (.mul .one .one) (.mul .zero .zero))))) rfl
    · calc
        A.a21 = A.a21 * (twoF F * halfF F) := by rw [h2h, cr_mul_one]
        _ = _ := RExpr.eq_of_norm_eq env
            (e₁ := .mul (.var 2) (.mul (.add .one .one) (.var 4)))
            (e₂ := .add (.add (.mul (.mul (.var 4) (.add (.var 0) (.var 3))) .zero)
                              (.mul (.mul (.var 4) (.sub (.var 0) (.var 3))) .zero))
                        (.add (.mul (.mul (.var 4) (.sub (.var 1) (.var 2))) (.neg .one))
                              (.mul (.mul (.var 4) (.add (.var 1) (.var 2)))
                                    (.add (.mul .zero .zero) (.mul (.neg .one) (.neg .one)))))) rfl
    · calc
        A.a22 = A.a22 * (twoF F * halfF F) := by rw [h2h, cr_mul_one]
        _ = _ := RExpr.eq_of_norm_eq env
            (e₁ := .mul (.var 3) (.mul (.add .one .one) (.var 4)))
            (e₂ := .add (.add (.mul (.mul (.var 4) (.add (.var 0) (.var 3))) .one)
                              (.mul (.mul (.var 4) (.sub (.var 0) (.var 3))) (.neg .one)))
                        (.add (.mul (.mul (.var 4) (.sub (.var 1) (.var 2))) .zero)
                              (.mul (.mul (.var 4) (.add (.var 1) (.var 2)))
                                    (.add (.mul .zero .one) (.mul (.neg .one) .zero))))) rfl
  rw [hdecomp]
  exact InPinSpan.add
    (InPinSpan.add (InPinSpan.smul _ (InPinSpan.pin InPin.one))
                   (InPinSpan.smul _ (InPinSpan.pin gamma1_inPin11)))
    (InPinSpan.add (InPinSpan.smul _ (InPinSpan.pin gamma2_inPin11))
                   (InPinSpan.smul _ (InPinSpan.pin (InPin.mul gamma1_inPin11 gamma2_inPin11))))

/-- Standard 2-component real spinor representation of `Cl_{1,1}^+(F) ≅ M_2(F)` on `F × F`. -/
def spinor11 (F : Type) [FormallyRealField F] : AlgRep F (alg F) (vecPair F) where
  act A v := (A.a11 * v.1 + A.a12 * v.2, A.a21 * v.1 + A.a22 * v.2)
  act_one v := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [v.1, v.2])
        (e₁ := .add (.mul .one (.var 0)) (.mul .zero (.var 1))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [v.1, v.2])
        (e₁ := .add (.mul .zero (.var 0)) (.mul .one (.var 1))) (e₂ := .var 1) rfl
  act_mul A B v := by
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22, v.1, v.2]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 8))
                    (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 9)))
        (e₂ := .add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 9))))
                    (.mul (.var 1) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 9))))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 8))
                    (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 9)))
        (e₂ := .add (.mul (.var 2) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 9))))
                    (.mul (.var 3) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 9))))) rfl
  act_add_left A B v := by
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, B.a11, B.a12, B.a21, B.a22, v.1, v.2]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.var 0) (.var 4)) (.var 8)) (.mul (.add (.var 1) (.var 5)) (.var 9)))
        (e₂ := .add (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 9)))
                    (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 9)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.add (.var 2) (.var 6)) (.var 8)) (.mul (.add (.var 3) (.var 7)) (.var 9)))
        (e₂ := .add (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 9)))
                    (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 9)))) rfl
  act_smul_left c A v := by
    let env := envGet (0 : F) [c, A.a11, A.a12, A.a21, A.a22, v.1, v.2]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 6)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 6)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 6)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 6)))) rfl
  act_add_right A u v := by
    let env := envGet (0 : F) [A.a11, A.a12, A.a21, A.a22, u.1, u.2, v.1, v.2]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 0) (.add (.var 4) (.var 6))) (.mul (.var 1) (.add (.var 5) (.var 7))))
        (e₂ := .add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
                    (.add (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 7)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 2) (.add (.var 4) (.var 6))) (.mul (.var 3) (.add (.var 5) (.var 7))))
        (e₂ := .add (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5)))
                    (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7)))) rfl
  act_smul_right A c v := by
    let env := envGet (0 : F) [c, A.a11, A.a12, A.a21, A.a22, v.1, v.2]
    ext
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 5))) (.mul (.var 2) (.mul (.var 0) (.var 6))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 6)))) rfl
    · exact RExpr.eq_of_norm_eq env
        (e₁ := .add (.mul (.var 3) (.mul (.var 0) (.var 5))) (.mul (.var 4) (.mul (.var 0) (.var 6))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 6)))) rfl

theorem spinor11_pinIrreducible : PinIrreducible ι11 Q11 (spinor11 F) := by
  rw [pinIrreducible_iff_irreducible span11]
  refine ⟨⟨(1, 0), fun h => one_ne_zeroF (congrArg Prod.fst h)⟩, fun W hinv => ?_⟩
  by_cases hex : ∃ v : F × F, W.mem v ∧ v ≠ (0, 0)
  · right
    obtain ⟨⟨a, b⟩, hvmem, hvne⟩ := hex
    intro ⟨x, y⟩
    by_cases ha : a ≠ 0
    · have hmat : (spinor11 F).act ⟨x * a⁻¹, 0, y * a⁻¹, 0⟩ (a, b) = (x, y) := by
        ext
        · change (x * a⁻¹) * a + 0 * b = x
          rw [CommRingOps.mul_assoc, inv_mul_cancelF ha, cr_mul_one, cr_zero_mul, cr_add_zero]
        · change (y * a⁻¹) * a + 0 * b = y
          rw [CommRingOps.mul_assoc, inv_mul_cancelF ha, cr_mul_one, cr_zero_mul, cr_add_zero]
      rw [← hmat]
      exact hinv _ _ hvmem
    · have ha0 : a = 0 := by by_cases h : a = 0; exact h; exact False.elim (ha h)
      have hb : b ≠ 0 := fun hb0 => hvne (by ext; exact ha0; exact hb0)
      have hmat : (spinor11 F).act ⟨0, x * b⁻¹, 0, y * b⁻¹⟩ (a, b) = (x, y) := by
        ext
        · change 0 * a + (x * b⁻¹) * b = x
          rw [cr_zero_mul, CommRingOps.zero_add, CommRingOps.mul_assoc, inv_mul_cancelF hb, cr_mul_one]
        · change 0 * a + (y * b⁻¹) * b = y
          rw [cr_zero_mul, CommRingOps.zero_add, CommRingOps.mul_assoc, inv_mul_cancelF hb, cr_mul_one]
      rw [← hmat]
      exact hinv _ _ hvmem
  · left
    intro v hv
    by_cases hvz : v = (0, 0)
    · exact hvz
    · exact False.elim (hex ⟨v, hv, hvz⟩)

/-- **Refutation of Claim C on `Cl_{1,1}^+(F) ≅ M_2(F)`:**
    1. Every scalar multiple `c • I_2` lies in the Clifford center `Z(M_2(F))` (in particular `I_2 ≠ 0`),
    2. Yet the algebra representation `spinor11` is faithful (`InRepKernel spinor11 A ↔ A = 0`),
       so `ker(spinor11) ≠ Z(Cl_{1,1}^+)`,
    3. And on `Pin(1,1)`, `-I_2 = gamma2Minus²` lies in `Z(Cl_{1,1}^+) ∩ Pin(1,1)` while
       NOT lying in `InPinKernel ι11 Q11 spinor11` (`ker(spinor11|_{Pin}) = {+I_2} ≠ {±I_2}`). -/
theorem center_vs_kernel_cl11 :
    InCenter (alg F) one ∧
    (one (F := F) ≠ zero) ∧
    (∀ A : Mat2 F, InRepKernel (spinor11 F) A ↔ A = zero) ∧
    InPin (alg F) ι11 Q11 (neg one) ∧
    InCenter (alg F) (neg one) ∧
    ¬ InPinKernel ι11 Q11 (spinor11 F) (neg one) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    change (alg F).mul (alg F).one X = (alg F).mul X (alg F).one
    rw [(alg F).one_mul, (alg F).mul_one]
  · exact fun h => one_ne_zeroF (congrArg Mat2.a11 h)
  · intro A
    constructor
    · intro hker
      have h10 := hker (1, 0)
      have h01 := hker (0, 1)
      have ha11 : A.a11 = 0 := by
        have := congrArg Prod.fst h10
        change A.a11 * 1 + A.a12 * 0 = 0 at this
        rw [cr_mul_one, cr_mul_zero, cr_add_zero] at this
        exact this
      have ha21 : A.a21 = 0 := by
        have := congrArg Prod.snd h10
        change A.a21 * 1 + A.a22 * 0 = 0 at this
        rw [cr_mul_one, cr_mul_zero, cr_add_zero] at this
        exact this
      have ha12 : A.a12 = 0 := by
        have := congrArg Prod.fst h01
        change A.a11 * 0 + A.a12 * 1 = 0 at this
        rw [cr_mul_zero, cr_mul_one, CommRingOps.zero_add] at this
        exact this
      have ha22 : A.a22 = 0 := by
        have := congrArg Prod.snd h01
        change A.a21 * 0 + A.a22 * 1 = 0 at this
        rw [cr_mul_zero, cr_mul_one, CommRingOps.zero_add] at this
        exact this
      ext <;> assumption
    · rintro rfl v
      exact algRep_act_zero_left (spinor11 F) v
  · have hsq : mul (gamma2Minus (F := F)) gamma2Minus = neg one := by
      let env := envGet (0 : F) []
      ext
      · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .zero) (.mul .one (.neg .one))) (e₂ := .neg .one) rfl
      · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul .zero .one) (.mul .one .zero)) (e₂ := .neg .zero) rfl
      · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.neg .one) .zero) (.mul .zero (.neg .one))) (e₂ := .neg .zero) rfl
      · exact RExpr.eq_of_norm_eq env (e₁ := .add (.mul (.neg .one) .one) (.mul .zero .zero)) (e₂ := .neg .one) rfl
    rw [← hsq]
    exact InPin.mul gamma2_inPin11 gamma2_inPin11
  · intro X
    change (alg F).mul ((alg F).neg (alg F).one) X = (alg F).mul X ((alg F).neg (alg F).one)
    rw [← alg_neg_one_smul (alg F) (alg F).one, (alg F).smul_mul_left, (alg F).smul_mul_right,
        (alg F).one_mul, (alg F).mul_one]
  · rintro ⟨_, hact⟩
    have h10 := congrArg Prod.fst (hact (1, 0))
    change -(1 : F) * 1 + -0 * 0 = 1 at h10
    have htwo : twoF F = 0 := by
      calc
        twoF F = (1 : F) - (-(1 : F) * 1 + -0 * 0) :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [])
            (e₁ := .add .one .one)
            (e₂ := .sub .one (.add (.mul (.neg .one) .one) (.mul (.neg .zero) .zero))) rfl
        _ = (1 : F) - 1 := by rw [h10]
        _ = 0 := RExpr.eq_of_norm_eq (envGet (0 : F) []) (e₁ := .sub .one .one) (e₂ := .zero) rfl
    exact two_ne_zeroF htwo

end Mat2

end RealCliffordCounterexamples

end Conjecture00000007605
