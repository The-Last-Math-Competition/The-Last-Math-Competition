/-
  SpinorMinimalIdeals/AlgebraicFramework.lean
  Abstract unital associative `ℚ`-algebras, left and two-sided ideals,
  minimal nonzero left ideals (algebraic spinor spaces in the sense of Cartan–Chevalley),
  exact `ℚ`-vector space dimension via `ℚ`-linear isomorphism with `Fin d → RatQ`,
  and unconditional dimension-invariance theorems (`dim 1 ≠ dim 2`, `dim 4 ≠ dim 2`).
-/

import SpinorMinimalIdeals.RatField

namespace SpinorMinimalIdeals

/-- Unital associative algebra over `ℚ` (`RatQ`). -/
structure QAlgebra (A : Type) where
  zero : A
  one  : A
  add  : A → A → A
  neg  : A → A
  mul  : A → A → A
  smul : RatQ → A → A
  add_assoc    : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm     : ∀ x y, add x y = add y x
  zero_add     : ∀ x, add zero x = x
  add_zero     : ∀ x, add x zero = x
  neg_add      : ∀ x, add (neg x) x = zero
  mul_assoc    : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul      : ∀ x, mul one x = x
  mul_one      : ∀ x, mul x one = x
  left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib: ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  one_smul     : ∀ x, smul 1 x = x
  mul_smul     : ∀ r s x, smul (r * s) x = smul r (smul s x)
  smul_add     : ∀ r x y, smul r (add x y) = add (smul r x) (smul r y)
  add_smul     : ∀ r s x, smul (r + s) x = add (smul r x) (smul s x)
  zero_smul    : ∀ x, smul 0 x = zero
  smul_mul_left: ∀ r x y, mul (smul r x) y = smul r (mul x y)

namespace QAlgebra

variable {A : Type} (alg : QAlgebra A)

theorem smul_zero (r : RatQ) : alg.smul r alg.zero = alg.zero := by
  have h1 : alg.smul r alg.zero = alg.smul r (alg.smul 0 alg.zero) := by rw [alg.zero_smul]
  rw [h1, ← alg.mul_smul, RatQ.mul_zero, alg.zero_smul]

theorem mul_zero (x : A) : alg.mul x alg.zero = alg.zero := by
  have h : alg.add (alg.mul x alg.zero) (alg.mul x alg.zero) =
           alg.add (alg.mul x alg.zero) alg.zero := by
    rw [← alg.left_distrib, alg.add_zero, alg.add_zero]
  have h2 : alg.add (alg.neg (alg.mul x alg.zero)) (alg.add (alg.mul x alg.zero) (alg.mul x alg.zero)) =
            alg.add (alg.neg (alg.mul x alg.zero)) (alg.add (alg.mul x alg.zero) alg.zero) := by
    rw [h]
  rw [← alg.add_assoc, alg.neg_add, alg.zero_add, ← alg.add_assoc, alg.neg_add, alg.zero_add] at h2
  exact h2

theorem zero_mul (x : A) : alg.mul alg.zero x = alg.zero := by
  rw [← alg.zero_smul x, alg.smul_mul_left, alg.zero_smul, alg.zero_smul]

/-- Left ideal of a `ℚ`-algebra `A`. -/
def IsLeftIdeal (I : A → Prop) : Prop :=
  I alg.zero ∧
  (∀ x y, I x → I y → I (alg.add x y)) ∧
  (∀ r x, I x → I (alg.smul r x)) ∧
  (∀ a x, I x → I (alg.mul a x))

/-- Two-sided ideal of a `ℚ`-algebra `A`. -/
def IsTwoSidedIdeal (J : A → Prop) : Prop :=
  IsLeftIdeal alg J ∧ (∀ x b, J x → J (alg.mul x b))

/-- A subset contains at least one nonzero element. -/
def IsNonzero (S : A → Prop) : Prop :=
  ∃ x, S x ∧ x ≠ alg.zero

/-- Minimal nonzero left ideal (algebraic spinor carrier in the sense of `SOURCE.md`). -/
def IsMinimalLeftIdeal (S : A → Prop) : Prop :=
  IsLeftIdeal alg S ∧
  IsNonzero alg S ∧
  (∀ I : A → Prop, IsLeftIdeal alg I → (∀ x, I x → S x) →
    (∀ x, I x → x = alg.zero) ∨ (∀ x, S x → I x))

/-- Minimal nonzero two-sided ideal. -/
def IsMinimalTwoSidedIdeal (J : A → Prop) : Prop :=
  IsTwoSidedIdeal alg J ∧
  IsNonzero alg J ∧
  (∀ K : A → Prop, IsTwoSidedIdeal alg K → (∀ x, K x → J x) →
    (∀ x, K x → x = alg.zero) ∨ (∀ x, J x → K x))

/-- Nonzero idempotent `e^2 = e ≠ 0`. -/
def IsIdempotent (e : A) : Prop :=
  alg.mul e e = e ∧ e ≠ alg.zero

/-- Nilpotent ideal `S^2 = 0` (`x * y = 0` for all `x, y ∈ S`). -/
def IsNilpotentIdeal (S : A → Prop) : Prop :=
  ∀ x y, S x → S y → alg.mul x y = alg.zero

/-- Faithful left module action: only `0 ∈ A` annihilates every element of `S`. -/
def IsFaithfulLeftIdeal (S : A → Prop) : Prop :=
  ∀ a : A, (∀ x, S x → alg.mul a x = alg.zero) → a = alg.zero

end QAlgebra

/-! ### Standard Coordinate Space `ℚ^d` and Exact Linear Dimension `HasQDim` -/

abbrev QVec (d : Nat) := Fin d → RatQ

namespace QVec

def zero (d : Nat) : QVec d := fun _ => 0
def add {d : Nat} (u v : QVec d) : QVec d := fun i => u i + v i
def neg {d : Nat} (u : QVec d) : QVec d := fun i => - u i
def sub {d : Nat} (u v : QVec d) : QVec d := fun i => u i - v i
def smul {d : Nat} (r : RatQ) (u : QVec d) : QVec d := fun i => r * u i

def basis {d : Nat} (j : Fin d) : QVec d :=
  fun i => if i = j then 1 else 0

theorem sub_eq_zero_iff {d : Nat} {u v : QVec d} :
    (∀ i, (sub u v) i = 0) ↔ u = v := by
  constructor
  · intro h
    funext i
    exact RatQ.sub_eq_zero_iff.mp (h i)
  · intro h i
    subst h
    exact RatQ.add_neg_cancel (u i)

end QVec

/-- Exact `ℚ`-vector space dimension of a subspace `S ⊆ A` via `ℚ`-linear bijection with `ℚ^d`. -/
structure LinearIsoQVec {A : Type} (alg : QAlgebra A) (S : A → Prop) (d : Nat) where
  toVec     : (x : A) → S x → QVec d
  ofVec     : QVec d → A
  ofVec_mem : ∀ v, S (ofVec v)
  left_inv  : ∀ x (hx : S x), ofVec (toVec x hx) = x
  right_inv : ∀ v, toVec (ofVec v) (ofVec_mem v) = v
  ofVec_add : ∀ u v, ofVec (QVec.add u v) = alg.add (ofVec u) (ofVec v)
  ofVec_smul: ∀ r v, ofVec (QVec.smul r v) = alg.smul r (ofVec v)

def HasQDim {A : Type} (alg : QAlgebra A) (S : A → Prop) (d : Nat) : Prop :=
  Nonempty (LinearIsoQVec alg S d)

/-- Unital `ℚ`-algebra isomorphism between `A` and `B`. -/
structure QAlgebraIso {A B : Type} (algA : QAlgebra A) (algB : QAlgebra B) where
  toFun    : A → B
  invFun   : B → A
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv: ∀ y, toFun (invFun y) = y
  map_one  : toFun algA.one = algB.one
  map_add  : ∀ x y, toFun (algA.add x y) = algB.add (toFun x) (toFun y)
  map_mul  : ∀ x y, toFun (algA.mul x y) = algB.mul (toFun x) (toFun y)
  map_smul : ∀ r x, toFun (algA.smul r x) = algB.smul r (toFun x)

/-! ### Unconditional Dimension-Invariance Lemmas (`1 ≠ 2` and `4 ≠ 2`) -/

/-- No `ℚ`-linear map `T : ℚ^2 → ℚ^1` can be injective. -/
theorem no_linear_inj_2_to_1 (T : QVec 2 → QVec 1)
    (hadd : ∀ u v, T (QVec.add u v) = QVec.add (T u) (T v))
    (hsmul : ∀ r u, T (QVec.smul r u) = QVec.smul r (T u))
    (hinj : ∀ u v, T u = T v → u = v) : False := by
  let e0 : QVec 2 := QVec.basis ⟨0, by decide⟩
  let e1 : QVec 2 := QVec.basis ⟨1, by decide⟩
  let z0 : Fin 1 := ⟨0, by decide⟩
  have hT0 : T (QVec.zero 2) = QVec.zero 1 := by
    have h := hsmul 0 (QVec.zero 2)
    have hz2 : QVec.smul 0 (QVec.zero 2) = QVec.zero 2 := by
      funext i; exact RatQ.zero_mul 0
    have hz1 : QVec.smul 0 (T (QVec.zero 2)) = QVec.zero 1 := by
      funext i; exact RatQ.zero_mul _
    rw [hz2, hz1] at h
    exact h
  let a := T e0 z0
  let b := T e1 z0
  by_cases ha : a = 0
  · have he0_eq : T e0 = T (QVec.zero 2) := by
      rw [hT0]
      funext ⟨i, hi⟩
      have hi0 : i = 0 := by omega
      subst hi0
      exact ha
    have hbad := hinj e0 (QVec.zero 2) he0_eq
    have h10 : e0 ⟨0, by decide⟩ = (QVec.zero 2) ⟨0, by decide⟩ := congrFun hbad ⟨0, by decide⟩
    exact RatQ.one_ne_zero h10
  · -- Construct nonzero `w = b • e0 + (-a) • e1` in `ker T`
    let w := QVec.add (QVec.smul b e0) (QVec.smul (-a) e1)
    have hTw : T w = T (QVec.zero 2) := by
      rw [hT0, hadd, hsmul, hsmul]
      funext ⟨i, hi⟩
      have hi0 : i = 0 := by omega
      subst hi0
      show b * a + (-a) * b = 0
      exact RatQ.eqQ_of_norm_eq [a, b]
        (.add (.mul (.var 1) (.var 0)) (.mul (.neg (.var 0)) (.var 1))) (.const 0) (by decide)
    have hw0 := hinj w (QVec.zero 2) hTw
    have hw_at_1 : w ⟨1, by decide⟩ = 0 := congrFun hw0 ⟨1, by decide⟩
    have hw_calc : w ⟨1, by decide⟩ = -a := by
      show b * 0 + (-a) * 1 = -a
      rw [RatQ.mul_zero, RatQ.zero_add, RatQ.mul_one]
    rw [hw_calc] at hw_at_1
    have hneg : -(-a) = -0 := by rw [hw_at_1]
    have hnn : -(-a) = a :=
      RatQ.eqQ_of_norm_eq [a] (.neg (.neg (.var 0))) (.var 0) (by decide)
    have hz0 : (-0 : RatQ) = 0 := by decide
    rw [hnn, hz0] at hneg
    exact ha hneg

/-- No `ℚ`-linear map `T : ℚ^3 → ℚ^2` can be injective. -/
theorem no_linear_inj_3_to_2 (T : QVec 3 → QVec 2)
    (hadd : ∀ u v, T (QVec.add u v) = QVec.add (T u) (T v))
    (hsmul : ∀ r u, T (QVec.smul r u) = QVec.smul r (T u))
    (hinj : ∀ u v, T u = T v → u = v) : False := by
  let f0 : QVec 3 := QVec.basis ⟨0, by decide⟩
  let f1 : QVec 3 := QVec.basis ⟨1, by decide⟩
  let f2 : QVec 3 := QVec.basis ⟨2, by decide⟩
  let i0 : Fin 2 := ⟨0, by decide⟩
  let i1 : Fin 2 := ⟨1, by decide⟩
  have hT0 : T (QVec.zero 3) = QVec.zero 2 := by
    have h := hsmul 0 (QVec.zero 3)
    have hz3 : QVec.smul 0 (QVec.zero 3) = QVec.zero 3 := by funext _; exact RatQ.zero_mul 0
    have hz2 : QVec.smul 0 (T (QVec.zero 3)) = QVec.zero 2 := by funext _; exact RatQ.zero_mul _
    rw [hz3, hz2] at h
    exact h
  by_cases ha0 : T f0 i0 = 0
  · by_cases ha1 : T f0 i1 = 0
    · -- `T f0 = 0`, contradicting `f0 ≠ 0`
      have hf0 : T f0 = T (QVec.zero 3) := by
        rw [hT0]
        funext ⟨k, hk⟩
        match k, hk with
        | 0, _ => exact ha0
        | 1, _ => exact ha1
      have hbad := hinj f0 (QVec.zero 3) hf0
      exact RatQ.one_ne_zero (congrFun hbad ⟨0, by decide⟩)
    · -- Eliminate `i1` from `f1` and `f2` using `f0`, then project onto `i0 : QVec 1`!
      let c := T f0 i1
      let g1 := QVec.add (QVec.smul c f1) (QVec.smul (-(T f1 i1)) f0)
      let g2 := QVec.add (QVec.smul c f2) (QVec.smul (-(T f2 i1)) f0)
      let emb : QVec 2 → QVec 3 := fun u => QVec.add (QVec.smul (u i0) g1) (QVec.smul (u i1) g2)
      let proj : QVec 2 → QVec 1 := fun v _ => v i0
      let S : QVec 2 → QVec 1 := fun u => proj (T (emb u))
      have hTg1_1 : T g1 i1 = 0 := by
        show (T (QVec.add (QVec.smul c f1) (QVec.smul (-(T f1 i1)) f0))) i1 = 0
        rw [hadd, hsmul, hsmul]
        show c * T f1 i1 + (-(T f1 i1)) * c = 0
        exact RatQ.eqQ_of_norm_eq [c, T f1 i1]
          (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0))) (.const 0) (by decide)
      have hTg2_1 : T g2 i1 = 0 := by
        show (T (QVec.add (QVec.smul c f2) (QVec.smul (-(T f2 i1)) f0))) i1 = 0
        rw [hadd, hsmul, hsmul]
        show c * T f2 i1 + (-(T f2 i1)) * c = 0
        exact RatQ.eqQ_of_norm_eq [c, T f2 i1]
          (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0))) (.const 0) (by decide)
      have hS_add : ∀ u v, S (QVec.add u v) = QVec.add (S u) (S v) := by
        intro u v
        funext _
        have hemb : emb (QVec.add u v) = QVec.add (emb u) (emb v) := by
          funext j
          exact RatQ.eqQ_of_norm_eq [u i0, v i0, u i1, v i1, g1 j, g2 j]
            (.add (.mul (.add (.var 0) (.var 1)) (.var 4))
                  (.mul (.add (.var 2) (.var 3)) (.var 5)))
            (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 5)))
                  (.add (.mul (.var 1) (.var 4)) (.mul (.var 3) (.var 5)))) (by decide)
        show (T (emb (QVec.add u v))) i0 = (T (emb u)) i0 + (T (emb v)) i0
        rw [hemb, hadd]
        rfl
      have hS_smul : ∀ r u, S (QVec.smul r u) = QVec.smul r (S u) := by
        intro r u
        funext _
        have hemb : emb (QVec.smul r u) = QVec.smul r (emb u) := by
          funext j
          exact RatQ.eqQ_of_norm_eq [r, u i0, u i1, g1 j, g2 j]
            (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
                  (.mul (.mul (.var 0) (.var 2)) (.var 4)))
            (.mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) (by decide)
        show (T (emb (QVec.smul r u))) i0 = r * (T (emb u)) i0
        rw [hemb, hsmul]
        rfl
      have hS_inj : ∀ u v, S u = S v → u = v := by
        intro u v huv
        have hdiff_emb : T (emb u) = T (emb v) := by
          funext ⟨k, hk⟩
          match k, hk with
          | 0, _ => exact congrFun huv ⟨0, by decide⟩
          | 1, _ =>
            have hu1 : (T (emb u)) i1 = 0 := by
              show (T (QVec.add (QVec.smul (u i0) g1) (QVec.smul (u i1) g2))) i1 = 0
              rw [hadd, hsmul, hsmul]
              show u i0 * T g1 i1 + u i1 * T g2 i1 = 0
              rw [hTg1_1, hTg2_1, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
            have hv1 : (T (emb v)) i1 = 0 := by
              show (T (QVec.add (QVec.smul (v i0) g1) (QVec.smul (v i1) g2))) i1 = 0
              rw [hadd, hsmul, hsmul]
              show v i0 * T g1 i1 + v i1 * T g2 i1 = 0
              rw [hTg1_1, hTg2_1, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
            rw [hu1, hv1]
        have hemb_eq := hinj (emb u) (emb v) hdiff_emb
        have hc1 : emb u ⟨1, by decide⟩ = emb v ⟨1, by decide⟩ := congrFun hemb_eq ⟨1, by decide⟩
        have hc2 : emb u ⟨2, by decide⟩ = emb v ⟨2, by decide⟩ := congrFun hemb_eq ⟨2, by decide⟩
        -- Note `g1` at coord 1 is `c`, `g2` at coord 1 is `0`; `g1` at coord 2 is `0`, `g2` at coord 2 is `c`!
        have hg1_1 : g1 ⟨1, by decide⟩ = c := by
          show c * 1 + (-(T f1 i1)) * 0 = c
          rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
        have hg2_1 : g2 ⟨1, by decide⟩ = 0 := by
          show c * 0 + (-(T f2 i1)) * 0 = 0
          rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
        have hg1_2 : g1 ⟨2, by decide⟩ = 0 := by
          show c * 0 + (-(T f1 i1)) * 0 = 0
          rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
        have hg2_2 : g2 ⟨2, by decide⟩ = c := by
          show c * 1 + (-(T f2 i1)) * 0 = c
          rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
        change u i0 * g1 ⟨1, by decide⟩ + u i1 * g2 ⟨1, by decide⟩ =
               v i0 * g1 ⟨1, by decide⟩ + v i1 * g2 ⟨1, by decide⟩ at hc1
        rw [hg1_1, hg2_1, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero, RatQ.add_zero] at hc1
        change u i0 * g1 ⟨2, by decide⟩ + u i1 * g2 ⟨2, by decide⟩ =
               v i0 * g1 ⟨2, by decide⟩ + v i1 * g2 ⟨2, by decide⟩ at hc2
        rw [hg1_2, hg2_2, RatQ.mul_zero, RatQ.mul_zero, RatQ.zero_add, RatQ.zero_add] at hc2
        have hu0_eq : u i0 = v i0 := by
          have hmul : (u i0) * c * c⁻¹ = (v i0) * c * c⁻¹ := by rw [hc1]
          rw [RatQ.mul_assoc, RatQ.mul_inv_cancel ha1, RatQ.mul_one,
              RatQ.mul_assoc, RatQ.mul_inv_cancel ha1, RatQ.mul_one] at hmul
          exact hmul
        have hu1_eq : u i1 = v i1 := by
          have hmul : (u i1) * c * c⁻¹ = (v i1) * c * c⁻¹ := by rw [hc2]
          rw [RatQ.mul_assoc, RatQ.mul_inv_cancel ha1, RatQ.mul_one,
              RatQ.mul_assoc, RatQ.mul_inv_cancel ha1, RatQ.mul_one] at hmul
          exact hmul
        funext ⟨k, hk⟩
        match k, hk with
        | 0, _ => exact hu0_eq
        | 1, _ => exact hu1_eq
      exact no_linear_inj_2_to_1 S hS_add hS_smul hS_inj
  · -- Eliminate `i0` from `f1` and `f2` using `f0`, then project onto `i1 : QVec 1`!
    let c := T f0 i0
    let g1 := QVec.add (QVec.smul c f1) (QVec.smul (-(T f1 i0)) f0)
    let g2 := QVec.add (QVec.smul c f2) (QVec.smul (-(T f2 i0)) f0)
    let emb : QVec 2 → QVec 3 := fun u => QVec.add (QVec.smul (u i0) g1) (QVec.smul (u i1) g2)
    let proj : QVec 2 → QVec 1 := fun v _ => v i1
    let S : QVec 2 → QVec 1 := fun u => proj (T (emb u))
    have hTg1_0 : T g1 i0 = 0 := by
      show (T (QVec.add (QVec.smul c f1) (QVec.smul (-(T f1 i0)) f0))) i0 = 0
      rw [hadd, hsmul, hsmul]
      show c * T f1 i0 + (-(T f1 i0)) * c = 0
      exact RatQ.eqQ_of_norm_eq [c, T f1 i0]
        (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0))) (.const 0) (by decide)
    have hTg2_0 : T g2 i0 = 0 := by
      show (T (QVec.add (QVec.smul c f2) (QVec.smul (-(T f2 i0)) f0))) i0 = 0
      rw [hadd, hsmul, hsmul]
      show c * T f2 i0 + (-(T f2 i0)) * c = 0
      exact RatQ.eqQ_of_norm_eq [c, T f2 i0]
        (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0))) (.const 0) (by decide)
    have hS_add : ∀ u v, S (QVec.add u v) = QVec.add (S u) (S v) := by
      intro u v
      funext _
      have hemb : emb (QVec.add u v) = QVec.add (emb u) (emb v) := by
        funext j
        exact RatQ.eqQ_of_norm_eq [u i0, v i0, u i1, v i1, g1 j, g2 j]
          (.add (.mul (.add (.var 0) (.var 1)) (.var 4))
                (.mul (.add (.var 2) (.var 3)) (.var 5)))
          (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 5)))
                (.add (.mul (.var 1) (.var 4)) (.mul (.var 3) (.var 5)))) (by decide)
      show (T (emb (QVec.add u v))) i1 = (T (emb u)) i1 + (T (emb v)) i1
      rw [hemb, hadd]
      rfl
    have hS_smul : ∀ r u, S (QVec.smul r u) = QVec.smul r (S u) := by
      intro r u
      funext _
      have hemb : emb (QVec.smul r u) = QVec.smul r (emb u) := by
        funext j
        exact RatQ.eqQ_of_norm_eq [r, u i0, u i1, g1 j, g2 j]
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
                (.mul (.mul (.var 0) (.var 2)) (.var 4)))
          (.mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) (by decide)
      show (T (emb (QVec.smul r u))) i1 = r * (T (emb u)) i1
      rw [hemb, hsmul]
      rfl
    have hS_inj : ∀ u v, S u = S v → u = v := by
      intro u v huv
      have hdiff_emb : T (emb u) = T (emb v) := by
        funext ⟨k, hk⟩
        match k, hk with
        | 1, _ => exact congrFun huv ⟨0, by decide⟩
        | 0, _ =>
          have hu0 : (T (emb u)) i0 = 0 := by
            show (T (QVec.add (QVec.smul (u i0) g1) (QVec.smul (u i1) g2))) i0 = 0
            rw [hadd, hsmul, hsmul]
            show u i0 * T g1 i0 + u i1 * T g2 i0 = 0
            rw [hTg1_0, hTg2_0, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
          have hv0 : (T (emb v)) i0 = 0 := by
            show (T (QVec.add (QVec.smul (v i0) g1) (QVec.smul (v i1) g2))) i0 = 0
            rw [hadd, hsmul, hsmul]
            show v i0 * T g1 i0 + v i1 * T g2 i0 = 0
            rw [hTg1_0, hTg2_0, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
          rw [hu0, hv0]
      have hemb_eq := hinj (emb u) (emb v) hdiff_emb
      have hc1 : emb u ⟨1, by decide⟩ = emb v ⟨1, by decide⟩ := congrFun hemb_eq ⟨1, by decide⟩
      have hc2 : emb u ⟨2, by decide⟩ = emb v ⟨2, by decide⟩ := congrFun hemb_eq ⟨2, by decide⟩
      have hg1_1 : g1 ⟨1, by decide⟩ = c := by
        show c * 1 + (-(T f1 i0)) * 0 = c
        rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
      have hg2_1 : g2 ⟨1, by decide⟩ = 0 := by
        show c * 0 + (-(T f2 i0)) * 0 = 0
        rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
      have hg1_2 : g1 ⟨2, by decide⟩ = 0 := by
        show c * 0 + (-(T f1 i0)) * 0 = 0
        rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
      have hg2_2 : g2 ⟨2, by decide⟩ = c := by
        show c * 1 + (-(T f2 i0)) * 0 = c
        rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
      change u i0 * g1 ⟨1, by decide⟩ + u i1 * g2 ⟨1, by decide⟩ =
             v i0 * g1 ⟨1, by decide⟩ + v i1 * g2 ⟨1, by decide⟩ at hc1
      rw [hg1_1, hg2_1, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero, RatQ.add_zero] at hc1
      change u i0 * g1 ⟨2, by decide⟩ + u i1 * g2 ⟨2, by decide⟩ =
             v i0 * g1 ⟨2, by decide⟩ + v i1 * g2 ⟨2, by decide⟩ at hc2
      rw [hg1_2, hg2_2, RatQ.mul_zero, RatQ.mul_zero, RatQ.zero_add, RatQ.zero_add] at hc2
      have hu0_eq : u i0 = v i0 := by
        have hmul : (u i0) * c * c⁻¹ = (v i0) * c * c⁻¹ := by rw [hc1]
        rw [RatQ.mul_assoc, RatQ.mul_inv_cancel ha0, RatQ.mul_one,
            RatQ.mul_assoc, RatQ.mul_inv_cancel ha0, RatQ.mul_one] at hmul
        exact hmul
      have hu1_eq : u i1 = v i1 := by
        have hmul : (u i1) * c * c⁻¹ = (v i1) * c * c⁻¹ := by rw [hc2]
        rw [RatQ.mul_assoc, RatQ.mul_inv_cancel ha0, RatQ.mul_one,
            RatQ.mul_assoc, RatQ.mul_inv_cancel ha0, RatQ.mul_one] at hmul
        exact hmul
      funext ⟨k, hk⟩
      match k, hk with
      | 0, _ => exact hu0_eq
      | 1, _ => exact hu1_eq
    exact no_linear_inj_2_to_1 S hS_add hS_smul hS_inj

/-- Helper: `toVec` in a `LinearIsoQVec` is automatically `ℚ`-linear! -/
theorem LinearIsoQVec.toVec_add {A : Type} {alg : QAlgebra A} {S : A → Prop} {d : Nat}
    (iso : LinearIsoQVec alg S d) (x y : A) (hx : S x) (hy : S y)
    (hxy : S (alg.add x y)) :
    iso.toVec (alg.add x y) hxy = QVec.add (iso.toVec x hx) (iso.toVec y hy) := by
  have h1 : iso.ofVec (QVec.add (iso.toVec x hx) (iso.toVec y hy)) = alg.add x y := by
    rw [iso.ofVec_add, iso.left_inv x hx, iso.left_inv y hy]
  have h2 := iso.right_inv (QVec.add (iso.toVec x hx) (iso.toVec y hy))
  -- Since `ofVec` is injective via `right_inv` and `left_inv`, substitute `h1`:
  have h3 : iso.toVec (iso.ofVec (QVec.add (iso.toVec x hx) (iso.toVec y hy)))
      (iso.ofVec_mem _) = iso.toVec (alg.add x y) hxy := by
    generalize iso.ofVec_mem (QVec.add (iso.toVec x hx) (iso.toVec y hy)) = hmem
    revert hmem
    rw [h1]
    intro _
    rfl
  rw [← h3, h2]

theorem LinearIsoQVec.toVec_smul {A : Type} {alg : QAlgebra A} {S : A → Prop} {d : Nat}
    (iso : LinearIsoQVec alg S d) (r : RatQ) (x : A) (hx : S x)
    (hrx : S (alg.smul r x)) :
    iso.toVec (alg.smul r x) hrx = QVec.smul r (iso.toVec x hx) := by
  have h1 : iso.ofVec (QVec.smul r (iso.toVec x hx)) = alg.smul r x := by
    rw [iso.ofVec_smul, iso.left_inv x hx]
  have h2 := iso.right_inv (QVec.smul r (iso.toVec x hx))
  have h3 : iso.toVec (iso.ofVec (QVec.smul r (iso.toVec x hx)))
      (iso.ofVec_mem _) = iso.toVec (alg.smul r x) hrx := by
    generalize iso.ofVec_mem (QVec.smul r (iso.toVec x hx)) = hmem
    revert hmem
    rw [h1]
    intro _
    rfl
  rw [← h3, h2]

/-- A 1-dimensional subspace over `ℚ` cannot be 2-dimensional. -/
theorem dim_one_not_dim_two {A : Type} {alg : QAlgebra A} {S : A → Prop}
    (h1 : HasQDim alg S 1) (h2 : HasQDim alg S 2) : False := by
  rcases h1 with ⟨iso1⟩
  rcases h2 with ⟨iso2⟩
  let T : QVec 2 → QVec 1 := fun u => iso1.toVec (iso2.ofVec u) (iso2.ofVec_mem u)
  have hadd : ∀ u v, T (QVec.add u v) = QVec.add (T u) (T v) := by
    intro u v
    show iso1.toVec (iso2.ofVec (QVec.add u v)) _ = _
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso1.toVec a ha = iso1.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    rw [hmem_eq _ _ (iso2.ofVec_add u v) _
        (by rw [← iso2.ofVec_add]; exact iso2.ofVec_mem _)]
    exact iso1.toVec_add _ _ (iso2.ofVec_mem u) (iso2.ofVec_mem v) _
  have hsmul : ∀ r u, T (QVec.smul r u) = QVec.smul r (T u) := by
    intro r u
    dsimp only [T]
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso1.toVec a ha = iso1.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    rw [hmem_eq _ _ (iso2.ofVec_smul r u) _
        (by rw [← iso2.ofVec_smul]; exact iso2.ofVec_mem _)]
    exact iso1.toVec_smul r _ (iso2.ofVec_mem u) _
  have hinj : ∀ u v, T u = T v → u = v := by
    intro u v huv
    have hof : iso1.ofVec (T u) = iso1.ofVec (T v) := by rw [huv]
    rw [iso1.left_inv, iso1.left_inv] at hof
    have h2u := iso2.right_inv u
    have h2v := iso2.right_inv v
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso2.toVec a ha = iso2.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    rw [← h2u, ← h2v]
    exact hmem_eq _ _ hof _ _
  exact no_linear_inj_2_to_1 T hadd hsmul hinj

/-- A 4-dimensional subspace over `ℚ` cannot be 2-dimensional. -/
theorem dim_four_not_dim_two {A : Type} {alg : QAlgebra A} {S : A → Prop}
    (h4 : HasQDim alg S 4) (h2 : HasQDim alg S 2) : False := by
  rcases h4 with ⟨iso4⟩
  rcases h2 with ⟨iso2⟩
  let pad : QVec 3 → QVec 4 := fun u ⟨k, hk⟩ =>
    if hk3 : k < 3 then u ⟨k, hk3⟩ else 0
  let T : QVec 3 → QVec 2 := fun u => iso2.toVec (iso4.ofVec (pad u)) (iso4.ofVec_mem (pad u))
  have hpad_add : ∀ u v, pad (QVec.add u v) = QVec.add (pad u) (pad v) := by
    intro u v; funext ⟨k, hk⟩
    by_cases hk3 : k < 3
    · simp [pad, hk3, QVec.add]
    · simp [pad, hk3, QVec.add, RatQ.add_zero]
  have hpad_smul : ∀ r u, pad (QVec.smul r u) = QVec.smul r (pad u) := by
    intro r u; funext ⟨k, hk⟩
    by_cases hk3 : k < 3
    · simp [pad, hk3, QVec.smul]
    · simp [pad, hk3, QVec.smul, RatQ.mul_zero]
  have hadd : ∀ u v, T (QVec.add u v) = QVec.add (T u) (T v) := by
    intro u v
    dsimp only [T]
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso2.toVec a ha = iso2.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    have heq : iso4.ofVec (pad (QVec.add u v)) = alg.add (iso4.ofVec (pad u)) (iso4.ofVec (pad v)) := by
      rw [hpad_add, iso4.ofVec_add]
    rw [hmem_eq _ _ heq _ (by rw [← heq]; exact iso4.ofVec_mem _)]
    exact iso2.toVec_add _ _ (iso4.ofVec_mem _) (iso4.ofVec_mem _) _
  have hsmul : ∀ r u, T (QVec.smul r u) = QVec.smul r (T u) := by
    intro r u
    dsimp only [T]
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso2.toVec a ha = iso2.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    have heq : iso4.ofVec (pad (QVec.smul r u)) = alg.smul r (iso4.ofVec (pad u)) := by
      rw [hpad_smul, iso4.ofVec_smul]
    rw [hmem_eq _ _ heq _ (by rw [← heq]; exact iso4.ofVec_mem _)]
    exact iso2.toVec_smul r _ (iso4.ofVec_mem _) _
  have hinj : ∀ u v, T u = T v → u = v := by
    intro u v huv
    have hof2 : iso2.ofVec (T u) = iso2.ofVec (T v) := by rw [huv]
    rw [iso2.left_inv, iso2.left_inv] at hof2
    have hmem_eq : ∀ (a b : A) (hab : a = b) (ha : S a) (hb : S b),
        iso4.toVec a ha = iso4.toVec b hb := by
      intro a b hab ha hb; subst hab; rfl
    have hpad_eq : pad u = pad v := by
      rw [← iso4.right_inv (pad u), ← iso4.right_inv (pad v)]
      exact hmem_eq _ _ hof2 _ _
    funext ⟨k, hk⟩
    have h_at := congrFun hpad_eq ⟨k, by omega⟩
    simpa [pad, hk] using h_at
  exact no_linear_inj_3_to_2 T hadd hsmul hinj

end SpinorMinimalIdeals
