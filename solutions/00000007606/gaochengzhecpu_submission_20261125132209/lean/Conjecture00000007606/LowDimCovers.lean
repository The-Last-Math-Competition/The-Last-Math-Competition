/-
  Conjecture 00000007606 — Low-Dimensional Double Covers & Signature/Characteristic Defects

  Formalizes:
    1. Characteristic 2 degeneracy on `Cl_{1,0}(F2)`: `+1 = -1` and the even rotor
       group has cardinality `1 ≠ 2`.
    2. Positive double cover `Spin(1, K) ↠ SO(1, K)` (kernel `{+1, -1}` of size 2)
       vs non-surjectivity onto `O(1, K)` and twisted-adjoint realization by `Pin(1, K)`.
    3. Positive double cover `Spin(2, E) ↠ SO(2, E)` over any `EuclideanFieldK E`
       (group homomorphism, global surjectivity onto `SO(2, E)`, exact kernel `{+1, -1}`
       of size 2, exact 2-element fibers `{x, -x}`), concrete rational Pythagorean
       fibers, rational spinor-norm non-surjectivity on the 90° rotation + lift in `ℚ(√2)`,
       non-surjectivity onto `O(2, E)` (`det = +1 ≠ -1`), infinite scalar kernel in
       `(Cl_{2,0}(ℚ)⁺)ˣ`, and twisted-adjoint reflection realization by `Pin(2, K)`.
    4. Indefinite Lorentzian signature `Cl_{1,1}(K)`: unit-norm even rotors
       `Spin⁺(1, 1; K) = {x ∈ Cl_{1,1}⁺ : x x̃ = 1}` satisfy `M_{11} = a^2 + b^2 ≥ 1 > 0`
       over any ordered field, missing `-I_2 ∈ SO(1, 1; K)` as well as `O(1, 1) \ SO(1, 1)`.
-/

import Conjecture00000007606.Clifford

namespace Conjecture00000007606

instance (p q : RawRat) : Decidable (RawRat.Rel p q) :=
  inferInstanceAs (Decidable (p.num * q.den = q.num * p.den))

/-! ### 1. Characteristic 2 Degeneracy (`F2`) -/

section CharTwoDegeneracy

abbrev sig10_F2 : List F2 := [F2.one]

/-- Over `𝔽₂` (characteristic 2), `+1 = -1` in `Cl_{1,0}(𝔽₂)` and every invertible
    element `(a, 0)` of the even subalgebra `Cl_{1,0}(𝔽₂)⁺ = 𝔽₂ · 1` equals `1`,
    so the kernel of the adjoint map has cardinality `1 ≠ 2`. -/
theorem char_two_kernel_size_one :
    (Cl.one sig10_F2 : Cl F2 sig10_F2) = Cl.neg sig10_F2 (Cl.one sig10_F2) ∧
    ∀ a : F2,
      (∃ y : Cl F2 sig10_F2, Cl.mul sig10_F2 (Cl.scalar a sig10_F2) y = Cl.one sig10_F2) →
      Cl.scalar a sig10_F2 = Cl.one sig10_F2 := by
  refine ⟨rfl, ?_⟩
  intro a ⟨y, hy⟩
  cases a with
  | zero =>
      cases y with
      | mk y0 y1 =>
          have h0 : F2.zero = F2.one := congrArg Prod.fst hy
          exact absurd h0 (by decide)
  | one => rfl

end CharTwoDegeneracy

/-! ### 2. Dimension `n = 1`: `Spin(1) ↠ SO(1)` vs `O(1)` and Twisted Adjoint -/

section DimOne
variable {K : Type} [FC : FieldCharNeTwo K]

abbrev sig10 (K : Type) [FieldK K] : List K := [FieldK.one]

/-- Positive `n = 1` theorem: `Spin_1(K) = {+1, -1}` (`+1 ≠ -1`), and every `x ∈ Spin_1(K)`
    acts as `+id_V` (surjecting onto `SO_1(K) = {+id_V}` with kernel of size 2), while
    missing `-id_V = reflTop ∈ O_1(K)`; meanwhile `e_1 ∈ Pin_1(K)` realizes `reflTop`
    ONLY via the twisted adjoint `α(e_1) v e_1⁻¹`, whereas ordinary `Ad_{e_1}(v) = +v`. -/
theorem spin1_double_cover_and_pin1_twisted_adjoint :
    let s := sig10 K
    let e1 : Cl K s := Cl.eTop FieldK.one []
    Cl.IsSpin s (Cl.one s) ∧
    Cl.IsSpin s (Cl.neg s (Cl.one s)) ∧
    (Cl.one s : Cl K s) ≠ Cl.neg s (Cl.one s) ∧
    (∀ x : Cl K s, Cl.IsSpin s x ↔ (x = Cl.one s ∨ x = Cl.neg s (Cl.one s))) ∧
    (∀ v : Vec K s,
      Cl.mul s (Cl.mul s (Cl.invol s e1) (Cl.embedVec s v)) e1 =
        Cl.embedVec s (Cl.reflTop FieldK.one [] v)) ∧
    (∀ v : Vec K s,
      Cl.mul s (Cl.mul s e1 (Cl.embedVec s v)) e1 = Cl.embedVec s v) := by
  intro s e1
  have hsig : ∀ c ∈ s, c ≠ FieldK.zero := by
    intro c hc
    dsimp [s, sig10] at hc
    cases hc with
    | head => exact FieldK.zero_ne_one.symm
    | tail _ h => cases h
  obtain ⟨h1, hn1, hne, hker⟩ := Cl.spin_adjoint_kernel_eq_pm_one s hsig
  refine ⟨h1, hn1, hne, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      apply (hker x hx).mp
      intro v
      have hx_even := hx.1
      have hx2_neg : FieldK.neg x.2 = x.2 := congrArg Prod.snd hx_even
      have hx2_0 : x.2 = FieldK.zero := FieldK.eq_zero_of_eq_neg hx2_neg.symm
      have hx_sc : x = Cl.scalar x.1 s := Prod.ext rfl hx2_0
      have hnorm : FieldK.mul x.1 x.1 = FieldK.one := by
        have hr := hx.2.1
        rw [hx_sc, Cl.rev_scalar, Cl.scalar_mul_scalar] at hr
        exact Cl.scalar_inj hr
      rw [hx_sc, Cl.rev_scalar, Cl.scalar_mul, Cl.mul_scalar, Cl.smul_smul,
          FieldK.mul_comm x.1 x.1, hnorm, Cl.one_smul]
    · intro hpm
      cases hpm with
      | inl h => exact h ▸ h1
      | inr h => exact h ▸ hn1
  · intro v
    apply Prod.ext <;> dsimp [s, sig10, e1, Cl.eTop, Cl.mul, Cl.invol, Cl.embedVec,
                              Cl.reflTop, Cl.scalar, Cl.zero, Cl.one, Cl.add, Cl.neg, Cl.smul] <;>
      simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
                 FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
                 FieldK.mul_neg, FieldK.neg_mul]
  · intro v
    apply Prod.ext <;> dsimp [s, sig10, e1, Cl.eTop, Cl.mul, Cl.invol, Cl.embedVec,
                              Cl.scalar, Cl.zero, Cl.one, Cl.add, Cl.neg, Cl.smul] <;>
      simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
                 FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
                 FieldK.mul_neg, FieldK.neg_mul]

end DimOne

/-! ### 3. Dimension `n = 2`: `Spin(2) ↠ SO(2)`, Matrices, Spinor Norm, & Refutations -/

/-- `2 × 2` matrices over `K`. -/
structure Mat2 (K : Type) where
  m11 : K
  m12 : K
  m21 : K
  m22 : K

namespace Mat2

@[ext]
theorem ext {K : Type} {A B : Mat2 K}
    (h11 : A.m11 = B.m11) (h12 : A.m12 = B.m12)
    (h21 : A.m21 = B.m21) (h22 : A.m22 = B.m22) : A = B := by
  cases A; cases B
  dsimp only at h11 h12 h21 h22
  subst h11; subst h12; subst h21; subst h22
  rfl

section MatrixOps
variable {K : Type} [F : FieldK K]

def idMat : Mat2 K := ⟨F.one, F.zero, F.zero, F.one⟩

def mul (A B : Mat2 K) : Mat2 K where
  m11 := F.add (F.mul A.m11 B.m11) (F.mul A.m12 B.m21)
  m12 := F.add (F.mul A.m11 B.m12) (F.mul A.m12 B.m22)
  m21 := F.add (F.mul A.m21 B.m11) (F.mul A.m22 B.m21)
  m22 := F.add (F.mul A.m21 B.m12) (F.mul A.m22 B.m22)

def tr (A : Mat2 K) : Mat2 K := ⟨A.m11, A.m21, A.m12, A.m22⟩

def det (A : Mat2 K) : K :=
  FieldK.sub (F.mul A.m11 A.m22) (F.mul A.m12 A.m21)

def rotMat (c s : K) : Mat2 K := ⟨c, s, F.neg s, c⟩

def reflMat1 : Mat2 K := ⟨F.neg F.one, F.zero, F.zero, F.one⟩

/-- `A ∈ O(2, K)` iff `Aᵀ A = I_2`. -/
def IsO2 (A : Mat2 K) : Prop := mul (tr A) A = idMat

/-- `A ∈ SO(2, K)` iff `A ∈ O(2, K)` and `det A = 1`. -/
def IsSO2 (A : Mat2 K) : Prop := IsO2 A ∧ det A = F.one

theorem reflMat1_isO2 : IsO2 (reflMat1 : Mat2 K) := by
  unfold IsO2 reflMat1 mul tr idMat
  apply ext <;> dsimp
  · rw [FieldK.neg_mul_neg, F.one_mul, FieldK.zero_mul, FieldK.add_zero]
  · rw [FieldK.neg_mul, F.mul_comm, FieldK.zero_mul, FieldK.neg_zero, FieldK.add_zero]
  · rw [FieldK.zero_mul, FieldK.mul_zero, FieldK.add_zero]
  · rw [FieldK.zero_mul, F.one_mul, F.zero_add]

theorem reflMat1_det : det (reflMat1 : Mat2 K) = F.neg F.one := by
  unfold det reflMat1 FieldK.sub
  rw [FieldK.neg_mul, F.one_mul, FieldK.zero_mul, FieldK.neg_zero, FieldK.add_zero]

theorem rotMat_isSO2 {c s : K} (hcs : F.add (F.mul c c) (F.mul s s) = F.one) :
    IsSO2 (rotMat c s) := by
  refine ⟨?_, ?_⟩
  · unfold IsO2 rotMat mul tr idMat
    apply ext <;> dsimp
    · rw [FieldK.neg_mul_neg]; exact hcs
    · rw [FieldK.neg_mul, F.mul_comm s c, FieldK.add_right_neg]
    · rw [FieldK.mul_neg, F.mul_comm s c, FieldK.add_right_neg]
    · rw [F.add_comm]; exact hcs
  · unfold det rotMat FieldK.sub
    rw [FieldK.mul_neg, FieldK.neg_neg]
    exact hcs

theorem rotMat_mul (c1 s1 c2 s2 : K) :
    mul (rotMat c1 s1) (rotMat c2 s2) =
    rotMat (FieldK.sub (F.mul c1 c2) (F.mul s1 s2))
           (F.add (F.mul c1 s2) (F.mul s1 c2)) := by
  unfold mul rotMat FieldK.sub
  apply ext
  · dsimp; rw [FieldK.mul_neg]
  · rfl
  · dsimp; rw [FieldK.neg_mul, FieldK.mul_neg, ← FieldK.neg_add, F.add_comm]
  · dsimp; rw [FieldK.neg_mul, F.add_comm]

/-- Every matrix `A ∈ SO(2, K)` has the canonical form `rotMat c s` with `c^2 + s^2 = 1`. -/
theorem eq_rotMat_of_isSO2 {A : Mat2 K} (hA : IsSO2 A) :
    F.add (F.mul A.m11 A.m11) (F.mul A.m12 A.m12) = F.one ∧
    A = rotMat A.m11 A.m12 := by
  obtain ⟨ho, hdet⟩ := hA
  have col1 : F.add (F.mul A.m11 A.m11) (F.mul A.m21 A.m21) = F.one :=
    congrArg Mat2.m11 ho
  have col2 : F.add (F.mul A.m12 A.m12) (F.mul A.m22 A.m22) = F.one :=
    congrArg Mat2.m22 ho
  have orth : F.add (F.mul A.m11 A.m12) (F.mul A.m21 A.m22) = F.zero :=
    congrArg Mat2.m12 ho
  unfold det FieldK.sub at hdet
  have hm22 : A.m22 = A.m11 := by
    calc
      A.m22 = F.mul F.one A.m22 := (F.one_mul _).symm
      _ = F.mul (F.add (F.mul A.m11 A.m11) (F.mul A.m21 A.m21)) A.m22 := by rw [col1]
      _ = F.add (F.mul A.m11 (F.add (F.mul A.m11 A.m22) (F.neg (F.mul A.m12 A.m21))))
                (F.mul A.m21 (F.add (F.mul A.m11 A.m12) (F.mul A.m21 A.m22))) := by
            rw [FieldK.right_distrib, F.left_distrib A.m11, F.left_distrib A.m21,
                F.mul_assoc A.m11 A.m11 A.m22, F.mul_assoc A.m21 A.m21 A.m22,
                FieldK.mul_neg,
                ← F.mul_assoc A.m21 A.m11 A.m12, F.mul_comm A.m21 A.m11,
                F.mul_assoc A.m11 A.m21 A.m12, F.mul_comm A.m21 A.m12]
            let P := F.mul A.m11 (F.mul A.m11 A.m22)
            let Q := F.mul A.m11 (F.mul A.m12 A.m21)
            let R := F.mul A.m21 (F.mul A.m21 A.m22)
            change F.add P R = F.add (F.add P (F.neg Q)) (F.add Q R)
            rw [F.add_assoc P (F.neg Q) (F.add Q R),
                ← F.add_assoc (F.neg Q) Q R, F.add_left_neg, F.zero_add]
      _ = F.add (F.mul A.m11 F.one) (F.mul A.m21 F.zero) := by rw [hdet, orth]
      _ = A.m11 := by rw [FieldK.mul_one, FieldK.mul_zero, FieldK.add_zero]
  have hm21 : A.m21 = F.neg A.m12 := by
    calc
      A.m21 = F.mul F.one A.m21 := (F.one_mul _).symm
      _ = F.mul (F.add (F.mul A.m12 A.m12) (F.mul A.m22 A.m22)) A.m21 := by rw [col2]
      _ = F.add (F.mul (F.neg A.m12) (F.add (F.mul A.m11 A.m22) (F.neg (F.mul A.m12 A.m21))))
                (F.mul A.m22 (F.add (F.mul A.m11 A.m12) (F.mul A.m21 A.m22))) := by
            let P := F.mul A.m12 (F.mul A.m12 A.m21)
            let Q := F.mul A.m22 (F.mul A.m11 A.m12)
            let R := F.mul A.m22 (F.mul A.m22 A.m21)
            have hL : F.mul (F.add (F.mul A.m12 A.m12) (F.mul A.m22 A.m22)) A.m21 =
                      F.add P R := by
              dsimp [P, R]
              rw [FieldK.right_distrib, F.mul_assoc, F.mul_assoc]
            have hR1 : F.mul (F.neg A.m12) (F.add (F.mul A.m11 A.m22) (F.neg (F.mul A.m12 A.m21))) =
                       F.add (F.neg Q) P := by
              dsimp [P, Q]
              rw [F.left_distrib (F.neg A.m12), FieldK.neg_mul, FieldK.neg_mul_neg,
                  ← F.mul_assoc A.m12 A.m11 A.m22, F.mul_comm A.m12 A.m11,
                  F.mul_comm (F.mul A.m11 A.m12) A.m22]
            have hR2 : F.mul A.m22 (F.add (F.mul A.m11 A.m12) (F.mul A.m21 A.m22)) =
                       F.add Q R := by
              dsimp [Q, R]
              rw [F.left_distrib A.m22, F.mul_comm A.m21 A.m22]
            rw [hL, hR1, hR2, F.add_comm (F.neg Q) P, F.add_assoc P (F.neg Q) (F.add Q R),
                ← F.add_assoc (F.neg Q) Q R, F.add_left_neg, F.zero_add]
      _ = F.add (F.mul (F.neg A.m12) F.one) (F.mul A.m22 F.zero) := by rw [hdet, orth]
      _ = F.neg A.m12 := by rw [FieldK.mul_one, FieldK.mul_zero, FieldK.add_zero]
  refine ⟨?_, ext rfl rfl hm21 hm22⟩
  rw [hm21, FieldK.neg_mul_neg] at col1
  exact col1

end MatrixOps

end Mat2

section DimTwoSpinCover

abbrev sig20 (K : Type) [FieldK K] : List K := [FieldK.one, FieldK.one]

/-- Even element `a + b e_{12}` in `Cl_{2,0}(K)`. -/
def rotor2 {K : Type} [F : FieldK K] (a b : K) : Cl K (sig20 K) :=
  ((a, F.zero), (F.zero, b))

def vec2 {K : Type} [FieldK K] (v1 v2 : K) : Vec K (sig20 K) := (((), v1), v2)

def applyMat2 {K : Type} [F : FieldK K] (M : Mat2 K) (v : Vec K (sig20 K)) : Vec K (sig20 K) :=
  vec2 (F.add (F.mul M.m11 v.1.2) (F.mul M.m12 v.2))
       (F.add (F.mul M.m21 v.1.2) (F.mul M.m22 v.2))

/-- `2 × 2` rotation matrix induced on `V = K^2` by `x ∈ Spin_2(K)`. -/
def spin2ToMat {K : Type} [F : FieldK K] (x : Cl K (sig20 K)) : Mat2 K :=
  let a := x.1.1
  let b := x.2.2
  Mat2.rotMat (FieldK.sub (F.mul a a) (F.mul b b))
              (F.mul FieldK.two (F.mul a b))

section RotorAlgebra
variable {K : Type} [F : FieldK K]

theorem rotor2_invol (a b : K) : Cl.invol (sig20 K) (rotor2 a b) = rotor2 a b := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, rotor2, Cl.invol, Cl.neg] <;>
    simp [FieldK.neg_zero, FieldK.neg_neg]

theorem rotor2_eq_add_omega (a b : K) :
    rotor2 a b = Cl.add (sig20 K) (Cl.scalar a (sig20 K))
                        (Cl.smul b (sig20 K) (Cl.omega (sig20 K))) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, rotor2, Cl.add, Cl.scalar, Cl.smul, Cl.omega, Cl.zero, Cl.one]
  · rw [FieldK.mul_zero, FieldK.add_zero]
  · rw [FieldK.mul_zero, FieldK.add_zero]
  · rw [FieldK.mul_zero, FieldK.add_zero]
  · rw [FieldK.mul_one, F.zero_add]

theorem rev_rotor2 (a b : K) :
    Cl.rev (sig20 K) (rotor2 a b) = rotor2 a (F.neg b) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, rotor2, Cl.rev, Cl.invol, Cl.neg] <;>
    simp only [FieldK.neg_zero, FieldK.neg_neg]

theorem rotor2_mul (a1 b1 a2 b2 : K) :
    Cl.mul (sig20 K) (rotor2 a1 b1) (rotor2 a2 b2) =
    rotor2 (FieldK.sub (F.mul a1 a2) (F.mul b1 b2))
           (F.add (F.mul a1 b2) (F.mul b1 a2)) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, rotor2, Cl.mul, Cl.invol, Cl.add, Cl.neg, Cl.smul, FieldK.sub] <;>
    simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
               FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
               FieldK.mul_neg, FieldK.neg_mul]

theorem rotor2_mul_rev (a b : K) :
    Cl.mul (sig20 K) (rotor2 a b) (Cl.rev (sig20 K) (rotor2 a b)) =
    Cl.scalar (F.add (F.mul a a) (F.mul b b)) (sig20 K) := by
  rw [rev_rotor2, rotor2_mul]
  unfold FieldK.sub
  rw [FieldK.mul_neg, FieldK.neg_neg, FieldK.mul_neg, F.mul_comm b a, F.add_left_neg]
  rfl

theorem rev_mul_rotor2 (a b : K) :
    Cl.mul (sig20 K) (Cl.rev (sig20 K) (rotor2 a b)) (rotor2 a b) =
    Cl.scalar (F.add (F.mul a a) (F.mul b b)) (sig20 K) := by
  rw [rev_rotor2, rotor2_mul]
  unfold FieldK.sub
  rw [FieldK.neg_mul, FieldK.neg_neg, FieldK.neg_mul, F.mul_comm b a, FieldK.add_right_neg]
  rfl

def e1_20 (K : Type) [F : FieldK K] : Cl K (sig20 K) :=
  ((F.zero, F.one), (F.zero, F.zero))

def e2_20 (K : Type) [F : FieldK K] : Cl K (sig20 K) :=
  ((F.zero, F.zero), (F.one, F.zero))

private theorem embedVec_vec2_decomp (v : Vec K (sig20 K)) :
    Cl.embedVec (sig20 K) v =
    Cl.add (sig20 K) (Cl.smul v.1.2 (sig20 K) (e1_20 K)) (Cl.smul v.2 (sig20 K) (e2_20 K)) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, e1_20, e2_20, Cl.embedVec, Cl.add, Cl.smul, Cl.scalar, Cl.zero, Cl.one] <;>
    simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
               FieldK.add_zero, FieldK.zero_add]

private theorem e1_mul_omega2 :
    Cl.mul (sig20 K) (e1_20 K) (Cl.omega (sig20 K)) = e2_20 K := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, e1_20, e2_20, Cl.mul, Cl.omega, Cl.invol, Cl.zero, Cl.one, Cl.add, Cl.neg, Cl.smul] <;>
    simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
               FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
               FieldK.mul_neg, FieldK.neg_mul]

private theorem e2_mul_omega2 :
    Cl.mul (sig20 K) (e2_20 K) (Cl.omega (sig20 K)) = Cl.neg (sig20 K) (e1_20 K) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [sig20, e1_20, e2_20, Cl.mul, Cl.omega, Cl.invol, Cl.zero, Cl.one, Cl.add, Cl.neg, Cl.smul] <;>
    simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
               FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
               FieldK.mul_neg, FieldK.neg_mul]

/-- Explicit adjoint action formula in `Cl_{2,0}(K)`:
    `(a + b e_{12}) v (a - b e_{12}) = embedVec (spin2ToMat (rotor2 a b) · v)`. -/
theorem rotor2_adjoint_vec (a b : K) (v : Vec K (sig20 K)) :
    Cl.mul (sig20 K)
      (Cl.mul (sig20 K) (rotor2 a b) (Cl.embedVec (sig20 K) v))
      (Cl.rev (sig20 K) (rotor2 a b)) =
    Cl.embedVec (sig20 K) (applyMat2 (spin2ToMat (rotor2 a b)) v) := by
  let s2 := sig20 K
  let ω := Cl.omega s2
  let u := Cl.embedVec s2 v
  have hu_odd : Cl.invol s2 u = Cl.neg s2 u := Cl.invol_embedVec s2 v
  have h_anticomm : Cl.mul s2 u ω = Cl.neg s2 (Cl.mul s2 ω u) := by
    have ho := (Cl.even_and_odd_omega_comm s2).2 u hu_odd
    have hne : ¬ (s2.length = 0) := by dsimp [s2, sig20, List.length]; omega
    have hlen : ¬ (s2.length % 2 = 1) := by dsimp [s2, sig20, List.length]; omega
    simp only [hne, hlen, or_self, ite_false] at ho
    exact ho
  have h_omega_u : Cl.mul s2 ω u = Cl.mul s2 u (Cl.neg s2 ω) := by
    rw [Cl.mul_neg, h_anticomm, Cl.neg_neg]
  have h_comm_rev : Cl.mul s2 (rotor2 a b) u = Cl.mul s2 u (rotor2 a (F.neg b)) := by
    rw [rotor2_eq_add_omega a b, rotor2_eq_add_omega a (F.neg b),
        Cl.right_distrib, Cl.left_distrib,
        Cl.scalar_mul, Cl.mul_scalar,
        Cl.smul_mul_left, Cl.smul_mul_right, h_omega_u,
        Cl.mul_neg, Cl.smul_neg]
    congr 1
    rw [← Cl.neg_one_smul s2 (Cl.smul b s2 (Cl.mul s2 u ω)),
        Cl.smul_smul, FieldK.neg_one_mul]
  rw [h_comm_rev, rev_rotor2, Cl.mul_assoc, rotor2_mul]
  have hC : FieldK.sub (F.mul a a) (F.mul (F.neg b) (F.neg b)) =
            FieldK.sub (F.mul a a) (F.mul b b) := by
    rw [FieldK.neg_mul_neg]
  have hS : F.add (F.mul a (F.neg b)) (F.mul (F.neg b) a) =
            F.neg (F.mul FieldK.two (F.mul a b)) := by
    rw [FieldK.mul_neg, FieldK.neg_mul, F.mul_comm b a, ← FieldK.neg_add]
    congr 1
    unfold FieldK.two
    rw [FieldK.right_distrib, F.one_mul]
  rw [hC, hS]
  let C := FieldK.sub (F.mul a a) (F.mul b b)
  let S := FieldK.mul FieldK.two (F.mul a b)
  let wVec : Vec K s2 := vec2 (F.add (F.mul C v.1.2) (F.mul S v.2))
                              (F.add (F.mul (F.neg S) v.1.2) (F.mul C v.2))
  change Cl.mul s2 (Cl.embedVec s2 v) (rotor2 C (F.neg S)) = Cl.embedVec s2 wVec
  rw [embedVec_vec2_decomp v, embedVec_vec2_decomp wVec,
      rotor2_eq_add_omega C (F.neg S),
      Cl.right_distrib, Cl.left_distrib, Cl.left_distrib,
      Cl.smul_mul_left, Cl.smul_mul_left, Cl.smul_mul_left, Cl.smul_mul_left,
      Cl.mul_scalar, Cl.mul_scalar, Cl.smul_smul, Cl.smul_smul,
      Cl.smul_mul_right, Cl.smul_mul_right, e1_mul_omega2, e2_mul_omega2,
      Cl.smul_smul, Cl.smul_smul, Cl.smul_neg]
  dsimp [wVec, vec2]
  have h_neg_smul : ∀ (r : K) (z : Cl K s2),
      Cl.smul (F.neg r) s2 z = Cl.neg s2 (Cl.smul r s2 z) := fun r z => by
    rw [← FieldK.neg_one_mul r, ← Cl.smul_smul, Cl.neg_one_smul]
  rw [FieldK.mul_neg v.1.2 S, FieldK.mul_neg v.2 S, h_neg_smul (F.mul v.2 S), Cl.neg_neg,
      F.mul_comm v.1.2 C, F.mul_comm v.2 C, F.mul_comm v.2 S, F.mul_comm v.1.2 S,
      FieldK.neg_mul S v.1.2,
      Cl.add_smul, Cl.add_smul]
  let P := Cl.smul (F.mul C v.1.2) s2 (e1_20 K)
  let Q := Cl.smul (F.neg (F.mul S v.1.2)) s2 (e2_20 K)
  let R := Cl.smul (F.mul C v.2) s2 (e2_20 K)
  let T := Cl.smul (F.mul S v.2) s2 (e1_20 K)
  change Cl.add s2 (Cl.add s2 P Q) (Cl.add s2 R T) =
         Cl.add s2 (Cl.add s2 P T) (Cl.add s2 Q R)
  rw [Cl.add_assoc s2 P Q (Cl.add s2 R T),
      Cl.add_comm s2 Q (Cl.add s2 R T),
      Cl.add_assoc s2 R T Q,
      Cl.add_comm s2 R (Cl.add s2 T Q),
      Cl.add_assoc s2 T Q R,
      ← Cl.add_assoc s2 P T (Cl.add s2 Q R)]

end RotorAlgebra

section Spin2Theorems
variable {K : Type} [FC : FieldCharNeTwo K]

theorem even_cl20_eq_rotor2 {x : Cl K (sig20 K)}
    (hx : Cl.invol (sig20 K) x = x) :
    x = rotor2 x.1.1 x.2.2 := by
  have h12 : FieldK.neg x.1.2 = x.1.2 := congrArg (fun p => p.1.2) hx
  have h21 : FieldK.neg x.2.1 = x.2.1 := congrArg (fun p => p.2.1) hx
  have z12 : x.1.2 = FieldK.zero := FieldK.eq_zero_of_eq_neg h12.symm
  have z21 : x.2.1 = FieldK.zero := FieldK.eq_zero_of_eq_neg h21.symm
  exact Prod.ext (Prod.ext rfl z12) (Prod.ext z21 rfl)

theorem isSpin_sig20_iff (x : Cl K (sig20 K)) :
    Cl.IsSpin (sig20 K) x ↔
      (x = rotor2 x.1.1 x.2.2 ∧
       FieldK.add (FieldK.mul x.1.1 x.1.1) (FieldK.mul x.2.2 x.2.2) = FieldK.one) := by
  constructor
  · intro ⟨heven, hnormR, _, _⟩
    have hx := even_cl20_eq_rotor2 heven
    refine ⟨hx, ?_⟩
    have hr := hnormR
    rw [hx, rotor2_mul_rev] at hr
    have h1 : Cl.one (sig20 K) = Cl.scalar FieldK.one (sig20 K) := rfl
    rw [h1] at hr
    exact Cl.scalar_inj hr
  · intro ⟨hx, hsq⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hx]; exact rotor2_invol _ _
    · rw [hx, rotor2_mul_rev, hsq]; rfl
    · rw [hx, rev_mul_rotor2, hsq]; rfl
    · intro v
      exact ⟨applyMat2 (spin2ToMat (rotor2 x.1.1 x.2.2)) v,
             by conv => lhs; arg 2; arg 2; rw [hx]
                conv => lhs; arg 3; arg 2; rw [hx]
                exact rotor2_adjoint_vec x.1.1 x.2.2 v⟩

theorem spin2ToMat_isSO2 {x : Cl K (sig20 K)} (hx : Cl.IsSpin (sig20 K) x) :
    Mat2.IsSO2 (spin2ToMat x) := by
  obtain ⟨_, hsq⟩ := (isSpin_sig20_iff x).mp hx
  apply Mat2.rotMat_isSO2
  let a := x.1.1
  let b := x.2.2
  have hid : FieldK.add
      (FieldK.mul (FieldK.sub (FieldK.mul a a) (FieldK.mul b b))
                  (FieldK.sub (FieldK.mul a a) (FieldK.mul b b)))
      (FieldK.mul (FieldK.mul FieldK.two (FieldK.mul a b))
                  (FieldK.mul FieldK.two (FieldK.mul a b))) =
      FieldK.mul (FieldK.add (FieldK.mul a a) (FieldK.mul b b))
                 (FieldK.add (FieldK.mul a a) (FieldK.mul b b)) := by
    let A := FieldK.mul a a
    let B := FieldK.mul b b
    have h4 : FieldK.mul (FieldK.mul FieldK.two (FieldK.mul a b))
                         (FieldK.mul FieldK.two (FieldK.mul a b)) =
              FieldK.add (FieldK.add (FieldK.mul A B) (FieldK.mul A B))
                         (FieldK.add (FieldK.mul A B) (FieldK.mul A B)) := by
      have hab2 : FieldK.mul (FieldK.mul a b) (FieldK.mul a b) = FieldK.mul A B := by
        dsimp [A, B]
        rw [← FieldK.mul_assoc, FieldK.mul_assoc a b a, FieldK.mul_comm b a,
            ← FieldK.mul_assoc a a b, FieldK.mul_assoc]
      have h2x : ∀ z : K, FieldK.mul FieldK.two z = FieldK.add z z := fun z => by
        unfold FieldK.two; rw [FieldK.right_distrib, FieldK.one_mul]
      rw [h2x (FieldK.mul a b), FieldK.right_distrib, FieldK.left_distrib, hab2]
    rw [h4]
    unfold FieldK.sub
    rw [FieldK.right_distrib, FieldK.left_distrib A, FieldK.left_distrib (FieldK.neg B),
        FieldK.right_distrib, FieldK.left_distrib A, FieldK.left_distrib B,
        FieldK.mul_neg, FieldK.neg_mul, FieldK.neg_mul_neg, FieldK.mul_comm B A]
    let AA := FieldK.mul A A
    let AB := FieldK.mul A B
    let BB := FieldK.mul B B
    change FieldK.add (FieldK.add (FieldK.add AA (FieldK.neg AB)) (FieldK.add (FieldK.neg AB) BB))
                      (FieldK.add (FieldK.add AB AB) (FieldK.add AB AB)) =
           FieldK.add (FieldK.add AA AB) (FieldK.add AB BB)
    have c1 : FieldK.add (FieldK.add (FieldK.neg AB) BB) (FieldK.add AB AB) =
              FieldK.add AB BB := by
      rw [FieldK.add_comm (FieldK.neg AB) BB,
          FieldK.add_assoc BB (FieldK.neg AB) (FieldK.add AB AB),
          ← FieldK.add_assoc (FieldK.neg AB) AB AB,
          FieldK.add_left_neg, FieldK.zero_add, FieldK.add_comm BB AB]
    rw [FieldK.add_assoc (FieldK.add AA (FieldK.neg AB)) (FieldK.add (FieldK.neg AB) BB),
        ← FieldK.add_assoc (FieldK.add (FieldK.neg AB) BB) (FieldK.add AB AB) (FieldK.add AB AB),
        c1,
        FieldK.add_assoc AA (FieldK.neg AB) _,
        ← FieldK.add_assoc (FieldK.neg AB) (FieldK.add AB BB) _,
        ← FieldK.add_assoc (FieldK.neg AB) AB BB,
        FieldK.add_left_neg, FieldK.zero_add,
        FieldK.add_comm BB (FieldK.add AB AB),
        FieldK.add_assoc AB AB BB,
        ← FieldK.add_assoc AA AB (FieldK.add AB BB)]
  rw [hid, hsq, FieldK.one_mul]

/-- Even units `(Cl_{2,0}(K)⁺)ˣ` NEVER reach the reflection `reflMat1 ∈ O_2(K)`. -/
theorem spin2_never_covers_O2_reflection :
    Mat2.IsO2 (Mat2.reflMat1 : Mat2 K) ∧
    ¬ ∃ x : Cl K (sig20 K), Cl.IsSpin (sig20 K) x ∧ spin2ToMat x = Mat2.reflMat1 := by
  refine ⟨Mat2.reflMat1_isO2, ?_⟩
  intro ⟨x, hx, hmat⟩
  have hso := (spin2ToMat_isSO2 hx).2
  rw [hmat, Mat2.reflMat1_det] at hso
  exact FieldK.one_ne_neg_one hso.symm

/-- **Classical Positive Double-Cover Theorem (`Spin(2, E) ↠ SO(2, E)`):**
    Over ANY Euclidean ordered field `E` (such as `ℝ` or `ℝ_alg`):
    1. `spin2ToMat` maps `Spin_2(E)` into `SO_2(E)`,
    2. **Kernel is `{+1, -1}` of exact cardinality 2** (`+1 ≠ -1`),
    3. **Global Surjectivity onto `SO_2(E)`**: every `M ∈ SO_2(E)` has a preimage `x ∈ Spin_2(E)`
       with `x ≠ -x`,
    4. **Non-Surjectivity onto `O_2(E)`**: `reflMat1 ∈ O_2(E)` has NO preimage in `Spin_2(E)`. -/
theorem spin2_euclidean_double_cover_over_SO2 {E : Type} [EF : EuclideanFieldK E] :
    let s2 := sig20 E
    (Cl.one s2 : Cl E s2) ≠ Cl.neg s2 (Cl.one s2) ∧
    (∀ x : Cl E s2, Cl.IsSpin s2 x → Mat2.IsSO2 (spin2ToMat x)) ∧
    (∀ x : Cl E s2, Cl.IsSpin s2 x →
      (spin2ToMat x = Mat2.idMat ↔ (x = Cl.one s2 ∨ x = Cl.neg s2 (Cl.one s2)))) ∧
    (∀ M : Mat2 E, Mat2.IsSO2 M →
      ∃ x : Cl E s2, Cl.IsSpin s2 x ∧ spin2ToMat x = M ∧ x ≠ Cl.neg s2 x) ∧
    (Mat2.IsO2 (Mat2.reflMat1 : Mat2 E) ∧
      ¬ ∃ x : Cl E s2, Cl.IsSpin s2 x ∧ spin2ToMat x = Mat2.reflMat1) := by
  intro s2
  have hsig : ∀ c ∈ s2, c ≠ FieldK.zero := by
    intro c hc
    dsimp [s2, sig20] at hc
    cases hc with
    | head => exact FieldK.zero_ne_one.symm
    | tail _ h =>
        cases h with
        | head => exact FieldK.zero_ne_one.symm
        | tail _ h2 => cases h2
  obtain ⟨_, _, hne1, hker_univ⟩ := Cl.spin_adjoint_kernel_eq_pm_one s2 hsig
  refine ⟨hne1, fun x hx => spin2ToMat_isSO2 hx, ?_, ?_, spin2_never_covers_O2_reflection⟩
  · intro x hx
    obtain ⟨hx_rot, _⟩ := (isSpin_sig20_iff x).mp hx
    constructor
    · intro hid
      apply (hker_univ x hx).mp
      intro v
      have hadj := rotor2_adjoint_vec x.1.1 x.2.2 v
      conv at hadj => lhs; arg 2; arg 2; rw [← hx_rot]
      conv at hadj => lhs; arg 3; arg 2; rw [← hx_rot]
      conv at hadj => rhs; arg 2; arg 1; rw [← hx_rot]
      rw [hadj, hid]
      congr 1
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · dsimp [applyMat2, vec2, Mat2.idMat]
          rw [FieldK.one_mul, FieldK.zero_mul, FieldK.add_zero]
      · dsimp [applyMat2, vec2, Mat2.idMat]
        rw [FieldK.zero_mul, FieldK.one_mul, FieldK.zero_add]
    · intro hpm
      cases hpm with
      | inl h1 =>
          rw [h1]
          apply Mat2.ext <;>
            dsimp [spin2ToMat, s2, sig20, Cl.one, Cl.zero, Mat2.rotMat, Mat2.idMat, FieldK.sub]
          · rw [FieldK.one_mul, FieldK.mul_zero, FieldK.neg_zero, FieldK.add_zero]
          · rw [FieldK.mul_zero, FieldK.mul_zero]
          · rw [FieldK.mul_zero, FieldK.mul_zero, FieldK.neg_zero]
          · rw [FieldK.one_mul, FieldK.mul_zero, FieldK.neg_zero, FieldK.add_zero]
      | inr hn1 =>
          rw [hn1]
          apply Mat2.ext <;>
            dsimp [spin2ToMat, s2, sig20, Cl.neg, Cl.one, Cl.zero, Mat2.rotMat, Mat2.idMat, FieldK.sub]
          · rw [FieldK.neg_mul_neg, FieldK.one_mul, FieldK.neg_zero,
                FieldK.mul_zero, FieldK.neg_zero, FieldK.add_zero]
          · rw [FieldK.neg_zero, FieldK.mul_zero, FieldK.mul_zero]
          · rw [FieldK.neg_zero, FieldK.mul_zero, FieldK.mul_zero, FieldK.neg_zero]
          · rw [FieldK.neg_mul_neg, FieldK.one_mul, FieldK.neg_zero,
                FieldK.mul_zero, FieldK.neg_zero, FieldK.add_zero]
  · intro M hM
    obtain ⟨hcs, hM_eq⟩ := Mat2.eq_rotMat_of_isSO2 hM
    let c := M.m11
    let s := M.m12
    by_cases hc1 : FieldK.add FieldK.one c = FieldK.zero
    · have hc_neg1 : c = FieldK.neg FieldK.one :=
        (FieldK.neg_eq_of_add_eq_zero hc1).symm
      have hs_sq0 : FieldK.mul s s = FieldK.zero := by
        have h1 : FieldK.add (FieldK.mul c c) (FieldK.mul s s) = FieldK.one := hcs
        rw [hc_neg1, FieldK.neg_mul_neg, FieldK.one_mul] at h1
        apply FieldK.add_left_cancel (a := FieldK.one)
        rw [FieldK.add_zero]
        exact h1
      have hs0 : s = FieldK.zero := by
        cases FieldK.mul_eq_zero hs_sq0 with
        | inl h => exact h
        | inr h => exact h
      let x := rotor2 (FieldK.zero : E) FieldK.one
      have hx_spin : Cl.IsSpin s2 x := (isSpin_sig20_iff x).mpr
        ⟨rfl, by dsimp [x, rotor2]; rw [FieldK.mul_zero, FieldK.one_mul, FieldK.zero_add]⟩
      have hx_ne : x ≠ Cl.neg s2 x := fun heq =>
        FieldK.zero_ne_one (FieldK.eq_zero_of_eq_neg (congrArg (fun p => p.2.2) heq)).symm
      refine ⟨x, hx_spin, ?_, hx_ne⟩
      rw [hM_eq]
      change spin2ToMat x = Mat2.rotMat c s
      rw [hc_neg1, hs0]
      apply Mat2.ext <;> dsimp [spin2ToMat, x, rotor2, Mat2.rotMat, FieldK.sub]
      · rw [FieldK.mul_zero, FieldK.one_mul, FieldK.zero_add]
      · rw [FieldK.zero_mul, FieldK.mul_zero]
      · rw [FieldK.zero_mul, FieldK.mul_zero, FieldK.neg_zero]
      · rw [FieldK.mul_zero, FieldK.one_mul, FieldK.zero_add]
    · have h1c_nonneg : OrderedFieldK.le FieldK.zero (FieldK.add FieldK.one c) :=
        FieldK.one_add_nonneg_of_unit_circle hcs
      have hhalf_nonneg : OrderedFieldK.le FieldK.zero
          (FieldK.mul (FieldK.add FieldK.one c) (FieldK.inv FieldK.two)) :=
        OrderedFieldK.mul_nonneg _ _ h1c_nonneg FieldK.inv_two_nonneg
      obtain ⟨a, _, ha_sq⟩ := EF.sqrt_exists _ hhalf_nonneg
      have h2nz : (FieldK.two : E) ≠ FieldK.zero := FieldCharNeTwo.two_ne_zero
      have h2a2 : FieldK.mul FieldK.two (FieldK.mul a a) = FieldK.add FieldK.one c := by
        rw [ha_sq, FieldK.mul_comm (FieldK.add FieldK.one c) (FieldK.inv FieldK.two),
            ← FieldK.mul_assoc, FieldK.mul_right_inv h2nz, FieldK.one_mul]
      have ha_nz : a ≠ FieldK.zero := by
        intro ha0
        rw [ha0, FieldK.mul_zero, FieldK.mul_zero] at h2a2
        exact hc1 h2a2.symm
      have h2a_nz : FieldK.mul FieldK.two a ≠ FieldK.zero :=
        FieldK.mul_ne_zero h2nz ha_nz
      let b := FieldK.mul s (FieldK.inv (FieldK.mul FieldK.two a))
      have h2ab : FieldK.mul FieldK.two (FieldK.mul a b) = s := by
        dsimp [b]
        rw [← FieldK.mul_assoc FieldK.two a _,
            FieldK.mul_comm (FieldK.mul FieldK.two a) _,
            FieldK.mul_assoc s _ _,
            FieldK.mul_left_inv _ h2a_nz, FieldK.mul_one]
      have h2b2 : FieldK.mul FieldK.two (FieldK.mul b b) = FieldK.sub FieldK.one c := by
        apply FieldK.mul_left_cancel hc1
        have lhs_eq : FieldK.mul (FieldK.add FieldK.one c) (FieldK.mul FieldK.two (FieldK.mul b b)) =
                      FieldK.mul s s := by
          calc
            FieldK.mul (FieldK.add FieldK.one c) (FieldK.mul FieldK.two (FieldK.mul b b))
              = FieldK.mul (FieldK.mul FieldK.two (FieldK.mul a a))
                           (FieldK.mul FieldK.two (FieldK.mul b b)) := by rw [h2a2]
            _ = FieldK.mul (FieldK.mul FieldK.two (FieldK.mul a b))
                           (FieldK.mul FieldK.two (FieldK.mul a b)) := by
                  rw [FieldK.mul_assoc FieldK.two (FieldK.mul a a) _,
                      FieldK.mul_assoc FieldK.two (FieldK.mul a b) _]
                  congr 1
                  rw [FieldK.mul_comm FieldK.two (FieldK.mul b b),
                      FieldK.mul_comm FieldK.two (FieldK.mul a b),
                      ← FieldK.mul_assoc (FieldK.mul a a) (FieldK.mul b b) FieldK.two,
                      ← FieldK.mul_assoc (FieldK.mul a b) (FieldK.mul a b) FieldK.two]
                  congr 1
                  rw [FieldK.mul_assoc a a (FieldK.mul b b),
                      ← FieldK.mul_assoc a b b,
                      FieldK.mul_comm (FieldK.mul a b) b,
                      ← FieldK.mul_assoc a b (FieldK.mul a b)]
            _ = FieldK.mul s s := by rw [h2ab]
        have rhs_eq : FieldK.mul (FieldK.add FieldK.one c) (FieldK.sub FieldK.one c) =
                      FieldK.mul s s := by
          calc
            FieldK.mul (FieldK.add FieldK.one c) (FieldK.sub FieldK.one c)
              = FieldK.sub (FieldK.mul (FieldK.add FieldK.one c) FieldK.one)
                           (FieldK.mul (FieldK.add FieldK.one c) c) := FieldK.mul_sub _ _ _
            _ = FieldK.sub (FieldK.add FieldK.one c) (FieldK.add c (FieldK.mul c c)) := by
                  rw [FieldK.mul_one, FieldK.right_distrib, FieldK.one_mul]
            _ = FieldK.sub FieldK.one (FieldK.mul c c) := by
                  unfold FieldK.sub
                  rw [FieldK.neg_add, FieldK.add_assoc FieldK.one c _,
                      ← FieldK.add_assoc c (FieldK.neg c) _,
                      FieldK.add_right_neg, FieldK.zero_add]
            _ = FieldK.mul s s := by
                  unfold FieldK.sub
                  rw [← hcs, FieldK.add_comm (FieldK.mul c c) (FieldK.mul s s),
                      FieldK.add_assoc, FieldK.add_right_neg, FieldK.add_zero]
        rw [lhs_eq, rhs_eq]
      have ha2_add_b2 : FieldK.add (FieldK.mul a a) (FieldK.mul b b) = FieldK.one := by
        apply FieldK.mul_left_cancel h2nz
        rw [FieldK.left_distrib, h2a2, h2b2, FieldK.mul_one]
        unfold FieldK.sub FieldK.two
        rw [FieldK.add_assoc FieldK.one c _,
            FieldK.add_comm c (FieldK.add FieldK.one (FieldK.neg c)),
            FieldK.add_assoc FieldK.one (FieldK.neg c) c,
            FieldK.add_left_neg, FieldK.add_zero]
      have ha2_sub_b2 : FieldK.sub (FieldK.mul a a) (FieldK.mul b b) = c := by
        apply FieldK.mul_left_cancel h2nz
        rw [FieldK.mul_sub, h2a2, h2b2]
        unfold FieldK.sub FieldK.two
        rw [FieldK.right_distrib, FieldK.one_mul,
            FieldK.neg_add, FieldK.neg_neg,
            FieldK.add_comm FieldK.one c,
            FieldK.add_assoc c FieldK.one _,
            ← FieldK.add_assoc FieldK.one (FieldK.neg FieldK.one) c,
            FieldK.add_right_neg, FieldK.zero_add]
      let x := rotor2 a b
      have hx_spin : Cl.IsSpin s2 x := (isSpin_sig20_iff x).mpr ⟨rfl, ha2_add_b2⟩
      have hx_ne : x ≠ Cl.neg s2 x := fun heq =>
        ha_nz (FieldK.eq_zero_of_eq_neg (congrArg (fun p => p.1.1) heq))
      refine ⟨x, hx_spin, ?_, hx_ne⟩
      rw [hM_eq]
      change spin2ToMat x = Mat2.rotMat c s
      unfold spin2ToMat x rotor2
      dsimp
      rw [ha2_sub_b2, h2ab]

end Spin2Theorems

/-! ### Concrete Unconditional Rational & `ℚ(√2)` Theorems + Infinite Unit Kernel -/

section ConcreteRationalWitnesses

/-- Concrete rational Pythagorean rotor `x = 3/5 + (4/5) e_{12} ∈ Spin_2(ℚ)`
    inducing the nontrivial rotation `rotMat (-7/25) (24/25) ∈ SO_2(ℚ)`. -/
def ratPythagRotor : Cl RatQ (sig20 RatQ) :=
  rotor2 (RatQ.mkRat 3 5) (RatQ.mkRat 4 5)

theorem ratPythagRotor_isSpin_and_nontrivial :
    Cl.IsSpin (sig20 RatQ) ratPythagRotor ∧
    spin2ToMat ratPythagRotor = Mat2.rotMat (RatQ.mkRat (-7) 25) (RatQ.mkRat 24 25) ∧
    spin2ToMat ratPythagRotor ≠ Mat2.idMat := by
  have hsq : FieldK.add (FieldK.mul (RatQ.mkRat 3 5) (RatQ.mkRat 3 5))
                        (FieldK.mul (RatQ.mkRat 4 5) (RatQ.mkRat 4 5)) = FieldK.one :=
    Quot.sound (by decide)
  have hspin : Cl.IsSpin (sig20 RatQ) ratPythagRotor :=
    (isSpin_sig20_iff ratPythagRotor).mpr ⟨rfl, hsq⟩
  have hmat : spin2ToMat ratPythagRotor =
              Mat2.rotMat (RatQ.mkRat (-7) 25) (RatQ.mkRat 24 25) := by
    unfold spin2ToMat ratPythagRotor rotor2 Mat2.rotMat
    apply Mat2.ext <;> exact Quot.sound (by decide)
  refine ⟨hspin, hmat, ?_⟩
  rw [hmat]
  intro heq
  have h11 : RatQ.mkRat (-7) 25 = RatQ.ofInt 1 := congrArg Mat2.m11 heq
  have hr := RatQ.exact_rel h11
  unfold RawRat.Rel at hr; dsimp only at hr; omega

/-- Rational spinor-norm obstruction: the 90° rotation `rotMat 0 1 ∈ SO_2(ℚ)` has
    NO preimage in `Spin_2(ℚ)` (because `[2] ≠ [1]` in `ℚˣ / (ℚˣ)²`). -/
theorem rat_rot90_not_in_spin2_image :
    Mat2.IsSO2 (Mat2.rotMat (FieldK.zero : RatQ) FieldK.one) ∧
    ¬ ∃ x : Cl RatQ (sig20 RatQ),
        Cl.IsSpin (sig20 RatQ) x ∧
        spin2ToMat x = Mat2.rotMat FieldK.zero FieldK.one := by
  refine ⟨Mat2.rotMat_isSO2 (by rw [FieldK.mul_zero, FieldK.one_mul, FieldK.zero_add]), ?_⟩
  intro ⟨x, hx, hmat⟩
  obtain ⟨_, hsq⟩ := (isSpin_sig20_iff x).mp hx
  have hsub : FieldK.sub (FieldK.mul x.1.1 x.1.1) (FieldK.mul x.2.2 x.2.2) = FieldK.zero :=
    congrArg Mat2.m11 hmat
  have heq_sq : FieldK.mul x.1.1 x.1.1 = FieldK.mul x.2.2 x.2.2 :=
    FieldK.sub_eq_zero.mp hsub
  rw [← heq_sq] at hsq
  have h2a2 : FieldK.mul FieldK.two (FieldK.mul x.1.1 x.1.1) = FieldK.one := by
    unfold FieldK.two
    rw [FieldK.right_distrib, FieldK.one_mul]
    exact hsq
  exact RatQ.no_rat_two_sq_eq_one x.1.1 h2a2

/-- Over `ℚ(√2)`, the 90° rotation `rotMat 0 1 ∈ SO_2(ℚ(√2))` DOES lift to
    `rotor2 (√2/2) (√2/2) ∈ Spin_2(ℚ(√2))`. -/
theorem qsqrt2_rot90_lifts_to_spin2 :
    let halfSqrt2 : QSqrt2 := ⟨FieldK.zero, RatQ.mkRat 1 2⟩
    let x := rotor2 halfSqrt2 halfSqrt2
    Cl.IsSpin (sig20 QSqrt2) x ∧
    spin2ToMat x = Mat2.rotMat (FieldK.zero : QSqrt2) FieldK.one := by
  intro halfSqrt2 x
  have h_sq_half : FieldK.mul halfSqrt2 halfSqrt2 = ⟨RatQ.mkRat 1 2, FieldK.zero⟩ := by
    apply QSqrt2.ext <;> exact Quot.sound (by decide)
  have h_sum1 : FieldK.add (FieldK.mul halfSqrt2 halfSqrt2) (FieldK.mul halfSqrt2 halfSqrt2) =
                FieldK.one := by
    rw [h_sq_half]
    apply QSqrt2.ext <;> exact Quot.sound (by decide)
  refine ⟨(isSpin_sig20_iff x).mpr ⟨rfl, h_sum1⟩, ?_⟩
  unfold spin2ToMat x rotor2 Mat2.rotMat FieldK.sub
  dsimp
  rw [h_sq_half, FieldK.add_right_neg]
  apply Mat2.ext
  · rfl
  · apply QSqrt2.ext <;> exact Quot.sound (by decide)
  · apply QSqrt2.ext <;> exact Quot.sound (by decide)
  · rfl

/-- **Refutation 2A(i) — Infinite Kernel in `(Cl_{2,0}(ℚ)⁺)ˣ`:**
    Defining rotors as invertible elements of the even subalgebra `(Cl⁺)ˣ` gives an
    INFINITE kernel under `Ad`: the sequence `n ↦ (n + 1) · 1 ∈ (Cl_{2,0}(ℚ)⁺)ˣ` is
    injective and every element acts trivially on `V`. -/
theorem rat_even_units_infinite_kernel :
    let s2 := sig20 RatQ
    let seq : Nat → Cl RatQ s2 := fun n => Cl.scalar (RatQ.ofInt (Int.ofNat (n + 1))) s2
    (∀ m n : Nat, seq m = seq n → m = n) ∧
    (∀ n : Nat, ∃ x_inv : Cl RatQ s2,
      Cl.invol s2 (seq n) = seq n ∧
      Cl.mul s2 (seq n) x_inv = Cl.one s2 ∧
      Cl.mul s2 x_inv (seq n) = Cl.one s2 ∧
      ∀ v : Vec RatQ s2,
        Cl.mul s2 (Cl.mul s2 (seq n) (Cl.embedVec s2 v)) x_inv = Cl.embedVec s2 v) := by
  intro s2 seq
  refine ⟨?_, ?_⟩
  · intro m n h
    have hq := Cl.scalar_inj h
    have hi := Int.ofNat.inj (RatQ.ofInt_inj hq)
    omega
  · intro n
    let k := RatQ.ofInt (Int.ofNat (n + 1))
    have hk : k ≠ FieldK.zero := by
      intro h0
      have hi : ((n + 1 : Nat) : Int) = 0 := RatQ.ofInt_inj h0
      omega
    obtain ⟨hev, hr, hl, htriv⟩ := Cl.scalar_unit_even_and_trivial_adjoint (sig := s2) hk
    exact ⟨Cl.scalar (FieldK.inv k) s2, hev, hr, hl, fun v => htriv (Cl.embedVec s2 v)⟩

end ConcreteRationalWitnesses

end DimTwoSpinCover

/-! ### 4. Indefinite Signature `Cl_{1,1}(K)`: `Spin⁺(1, 1)` Misses `-I_2 ∈ SO(1, 1)` -/

section IndefiniteSignatureCl11

abbrev sig11 (K : Type) [F : FieldK K] : List K := [F.one, F.neg F.one]

/-- In Lorentzian signature `(1, -1)` over ANY ordered field `K` (including `ℚ` and `ℝ`),
    `-id_V : (v_1, v_2) ↦ (-v_1, -v_2)` is a proper Lorentz transformation (`det = +1`,
    preserving `Q_{1,1}(v) = v_1^2 - v_2^2`), YET NO unit-norm even element
    `x ∈ {x ∈ Cl_{1,1}(K)⁺ : x x̃ = 1} = Spin⁺(1, 1; K)` can induce `-id_V` via `Ad_x`. -/
theorem cl11_unit_norm_even_misses_neg_id_in_SO11 {K : Type} [O : OrderedFieldK K] :
    let s11 := sig11 K
    let negIdVec : Vec K s11 → Vec K s11 := fun v => (((), FieldK.neg v.1.2), FieldK.neg v.2)
    (∀ v : Vec K s11, Cl.quadForm s11 (negIdVec v) = Cl.quadForm s11 v) ∧
    ¬ ∃ x : Cl K s11,
        Cl.invol s11 x = x ∧
        Cl.mul s11 x (Cl.rev s11 x) = Cl.one s11 ∧
        ∀ v : Vec K s11,
          Cl.mul s11 (Cl.mul s11 x (Cl.embedVec s11 v)) (Cl.rev s11 x) =
            Cl.embedVec s11 (negIdVec v) := by
  intro s11 negIdVec
  refine ⟨?_, ?_⟩
  · intro v
    dsimp [s11, sig11, negIdVec, Cl.quadForm]
    rw [FieldK.neg_mul_neg, FieldK.neg_mul_neg]
  · intro ⟨x, heven, hnorm, had⟩
    have h12 : FieldK.neg x.1.2 = x.1.2 := congrArg (fun p => p.1.2) heven
    have h21 : FieldK.neg x.2.1 = x.2.1 := congrArg (fun p => p.2.1) heven
    have z12 : x.1.2 = FieldK.zero := FieldK.eq_zero_of_eq_neg h12.symm
    have z21 : x.2.1 = FieldK.zero := FieldK.eq_zero_of_eq_neg h21.symm
    let a := x.1.1
    let b := x.2.2
    have hx_eq : x = ((a, FieldK.zero), (FieldK.zero, b)) :=
      Prod.ext (Prod.ext rfl z12) (Prod.ext z21 rfl)
    have ha2_sub_b2 : FieldK.sub (FieldK.mul a a) (FieldK.mul b b) = FieldK.one := by
      have h11 := congrArg (fun p => p.1.1) hnorm
      rw [hx_eq] at h11
      dsimp [s11, sig11, Cl.mul, Cl.rev, Cl.invol, Cl.one, Cl.zero, Cl.add, Cl.neg, Cl.smul] at h11
      simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
                 FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
                 FieldK.mul_neg, FieldK.neg_mul] at h11
      exact h11
    have ha2_add_b2 : FieldK.add (FieldK.mul a a) (FieldK.mul b b) = FieldK.neg FieldK.one := by
      have he1 := congrArg (fun p => p.1.2) (had (((), FieldK.one), FieldK.zero))
      rw [hx_eq] at he1
      dsimp [s11, sig11, negIdVec, Cl.embedVec, Cl.scalar, Cl.mul, Cl.rev,
             Cl.invol, Cl.one, Cl.zero, Cl.add, Cl.neg, Cl.smul] at he1
      simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
                 FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
                 FieldK.mul_neg, FieldK.neg_mul] at he1
      exact he1
    have h2a2 : FieldK.mul FieldK.two (FieldK.mul a a) = FieldK.zero := by
      unfold FieldK.two
      rw [FieldK.right_distrib, FieldK.one_mul]
      calc
        FieldK.add (FieldK.mul a a) (FieldK.mul a a)
          = FieldK.add (FieldK.sub (FieldK.mul a a) (FieldK.mul b b))
                       (FieldK.add (FieldK.mul a a) (FieldK.mul b b)) := by
              unfold FieldK.sub
              rw [FieldK.add_assoc (FieldK.mul a a) (FieldK.neg (FieldK.mul b b)),
                  ← FieldK.add_assoc (FieldK.neg (FieldK.mul b b)) (FieldK.mul a a) (FieldK.mul b b),
                  FieldK.add_comm (FieldK.neg (FieldK.mul b b)) (FieldK.mul a a),
                  FieldK.add_assoc (FieldK.mul a a) (FieldK.neg (FieldK.mul b b)) (FieldK.mul b b),
                  FieldK.add_left_neg, FieldK.add_zero]
        _ = FieldK.add FieldK.one (FieldK.neg FieldK.one) := by rw [ha2_sub_b2, ha2_add_b2]
        _ = FieldK.zero := FieldK.add_right_neg _
    have ha2_0 : FieldK.mul a a = FieldK.zero := by
      cases FieldK.mul_eq_zero h2a2 with
      | inl h2 => exact absurd h2 O.two_ne_zero
      | inr h0 => exact h0
    rw [ha2_0, FieldK.zero_add] at ha2_add_b2
    have hb_nonneg : O.le FieldK.zero (FieldK.mul b b) := FieldK.sq_nonneg b
    rw [ha2_add_b2] at hb_nonneg
    have h1_le_0 := O.add_le_add_left FieldK.zero (FieldK.neg FieldK.one) FieldK.one hb_nonneg
    rw [FieldK.add_zero, FieldK.add_right_neg] at h1_le_0
    exact FieldK.lt_irrefl_zero_one h1_le_0

end IndefiniteSignatureCl11

end Conjecture00000007606
