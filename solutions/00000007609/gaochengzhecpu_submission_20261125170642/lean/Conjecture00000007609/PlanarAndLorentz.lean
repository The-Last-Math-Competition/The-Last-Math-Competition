/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Planar Euclidean `O(2, F) / SO(2, F)` and Lorentzian `O(1, 1; F) / SO(1, 1; F)` theory for
Conjecture 00000007609:
  1. Universal `2 × 2` reflections `refl2 Q u`, involutive isometry, and `det = -1`,
  2. Determinant parity theorem (`det g = (-1)^k`) for all reflection decompositions,
  3. Complete Euclidean `O_2(F)` Cartan–Dieudonné minimal reflection count classification (`0, 1, 2`),
  4. Refutation R1: Infinite minimal-length reflection-operator decompositions & unbounded counts,
  5. Refutation R2a: Infinite distinct-angle family in `SO_2(F)` with identical minimal count `2`,
  6. Refutation R3a: Lorentzian `-I_2 ∈ SO(1, 1; F)` has minimal reflection count `2` yet lies
     outside the square/exponential subgroup `SO^+(1, 1; F)`.
-/

import Conjecture00000007609.FieldFoundation

namespace Conjecture00000007609

structure Vec2 (F : Type) where
  x : F
  y : F

theorem Vec2.ext {F : Type} {u v : Vec2 F} (hx : u.x = v.x) (hy : u.y = v.y) : u = v := by
  cases u; cases v; cases hx; cases hy; rfl

structure Mat2 (F : Type) where
  a00 : F
  a01 : F
  a10 : F
  a11 : F

theorem Mat2.ext {F : Type} {A B : Mat2 F}
    (h00 : A.a00 = B.a00) (h01 : A.a01 = B.a01)
    (h10 : A.a10 = B.a10) (h11 : A.a11 = B.a11) : A = B := by
  cases A; cases B; cases h00; cases h01; cases h10; cases h11; rfl

section PlanarTheory

variable {F : Type} [FormallyRealField F]

namespace Mat2

def one (F : Type) [FormallyRealField F] : Mat2 F := ⟨1, 0, 0, 1⟩

def negOne (F : Type) [FormallyRealField F] : Mat2 F := ⟨-1, 0, 0, -1⟩

def rot90 (F : Type) [FormallyRealField F] : Mat2 F := ⟨0, -1, 1, 0⟩

def mul (A B : Mat2 F) : Mat2 F :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10,
   A.a00 * B.a01 + A.a01 * B.a11,
   A.a10 * B.a00 + A.a11 * B.a10,
   A.a10 * B.a01 + A.a11 * B.a11⟩

def mulVec (A : Mat2 F) (v : Vec2 F) : Vec2 F :=
  ⟨A.a00 * v.x + A.a01 * v.y,
   A.a10 * v.x + A.a11 * v.y⟩

def det (A : Mat2 F) : F :=
  A.a00 * A.a11 - A.a01 * A.a10

def tr (A : Mat2 F) : F :=
  A.a00 + A.a11

def frobDistSq (A B : Mat2 F) : F :=
  (A.a00 - B.a00) * (A.a00 - B.a00) +
  (A.a01 - B.a01) * (A.a01 - B.a01) +
  (A.a10 - B.a10) * (A.a10 - B.a10) +
  (A.a11 - B.a11) * (A.a11 - B.a11)

theorem one_mul (A : Mat2 F) : mul (one F) A = A := by
  apply Mat2.ext <;>
  · dsimp [mul, one]
    try rw [CommRingOps.one_mul, cr_zero_mul, cr_add_zero]
    try rw [cr_zero_mul, CommRingOps.one_mul, CommRingOps.zero_add]

theorem mul_one (A : Mat2 F) : mul A (one F) = A := by
  apply Mat2.ext <;>
  · dsimp [mul, one]
    try rw [cr_mul_one, cr_mul_zero, cr_add_zero]
    try rw [cr_mul_zero, cr_mul_one, CommRingOps.zero_add]

theorem mul_assoc (A B C : Mat2 F) : mul (mul A B) C = mul A (mul B C) := by
  let env := envGet (0 : F)
    [A.a00, A.a01, A.a10, A.a11, B.a00, B.a01, B.a10, B.a11, C.a00, C.a01, C.a10, C.a11]
  apply Mat2.ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 8))
                  (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 10)))
      (e₂ := .add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10))))
                  (.mul (.var 1) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10))))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 9))
                  (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 11)))
      (e₂ := .add (.mul (.var 0) (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11))))
                  (.mul (.var 1) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11))))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 8))
                  (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 10)))
      (e₂ := .add (.mul (.var 2) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10))))
                  (.mul (.var 3) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10))))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 9))
                  (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 11)))
      (e₂ := .add (.mul (.var 2) (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11))))
                  (.mul (.var 3) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11))))) rfl

theorem mulVec_mul (A B : Mat2 F) (v : Vec2 F) :
    mulVec (mul A B) v = mulVec A (mulVec B v) := by
  let env := envGet (0 : F)
    [A.a00, A.a01, A.a10, A.a11, B.a00, B.a01, B.a10, B.a11, v.x, v.y]
  apply Vec2.ext
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

theorem det_one : det (one F) = 1 :=
  RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .sub (.mul .one .one) (.mul .zero .zero))
    (e₂ := .one) rfl

theorem det_negOne : det (negOne F) = 1 :=
  RExpr.eq_of_norm_eq (envGet (0 : F) [])
    (e₁ := .sub (.mul (.neg .one) (.neg .one)) (.mul .zero .zero))
    (e₂ := .one) rfl

theorem det_mul (A B : Mat2 F) : det (mul A B) = det A * det B := by
  let env := envGet (0 : F) [A.a00, A.a01, A.a10, A.a11, B.a00, B.a01, B.a10, B.a11]
  exact RExpr.eq_of_norm_eq env
    (e₁ := .sub (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6)))
                      (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))))
                (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7)))
                      (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6)))))
    (e₂ := .mul (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                (.sub (.mul (.var 4) (.var 7)) (.mul (.var 5) (.var 6)))) rfl

theorem tr_sq_eq (B : Mat2 F) :
    tr (mul B B) = tr B * tr B - twoF F * det B := by
  have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [B.a00, B.a01, B.a10, B.a11])
    (e₁ := .add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
                (.add (.mul (.var 2) (.var 1)) (.mul (.var 3) (.var 3))))
    (e₂ := .sub (.mul (.add (.var 0) (.var 3)) (.add (.var 0) (.var 3)))
                (.mul (.add .one .one)
                      (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))) rfl
  exact hr

/-- Exact trace of `A^4` in terms of `t = tr A` and `d = det A`:
    `tr ((A^2)^2) = t^4 - 4 d t^2 + 2 d^2`. -/
theorem tr_pow4_eq (A : Mat2 F) :
    tr (mul (mul A A) (mul A A)) =
      (tr A * tr A) * (tr A * tr A) -
        ((twoF F * twoF F) * det A) * (tr A * tr A) +
        twoF F * (det A * det A) := by
  rw [tr_sq_eq (mul A A), tr_sq_eq A, det_mul A A]
  have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [tr A, det A])
    (e₁ := .sub (.mul (.sub (.mul (.var 0) (.var 0)) (.mul (.add .one .one) (.var 1)))
                      (.sub (.mul (.var 0) (.var 0)) (.mul (.add .one .one) (.var 1))))
                (.mul (.add .one .one) (.mul (.var 1) (.var 1))))
    (e₂ := .add (.sub (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
                      (.mul (.mul (.mul (.add .one .one) (.add .one .one)) (.var 1))
                            (.mul (.var 0) (.var 0))))
                (.mul (.add .one .one) (.mul (.var 1) (.var 1)))) rfl
  exact hr

end Mat2

/-! ## Diagonal Non-Degenerate Planar Quadratic Spaces `(F^2, Q)` -/

structure QuadForm2 (F : Type) [FormallyRealField F] where
  c0 : F
  c1 : F

/-- Euclidean quadratic form `Q_{2,0}(x, y) = x^2 + y^2`. -/
def Q20 (F : Type) [FormallyRealField F] : QuadForm2 F := ⟨1, 1⟩

/-- Lorentzian quadratic form `Q_{1,1}(x, y) = x^2 - y^2`. -/
def Q11 (F : Type) [FormallyRealField F] : QuadForm2 F := ⟨1, -1⟩

def QuadForm2.eval (Q : QuadForm2 F) (v : Vec2 F) : F :=
  Q.c0 * (v.x * v.x) + Q.c1 * (v.y * v.y)

/-- Exact polar symmetric bilinear form `B_Q(u, v) = Q(u + v) - Q(u) - Q(v)`. -/
def QuadForm2.polar (Q : QuadForm2 F) (u v : Vec2 F) : F :=
  Q.eval ⟨u.x + v.x, u.y + v.y⟩ - Q.eval u - Q.eval v

theorem QuadForm2.polar_eq (Q : QuadForm2 F) (u v : Vec2 F) :
    Q.polar u v = twoF F * (Q.c0 * (u.x * v.x) + Q.c1 * (u.y * v.y)) := by
  let env := envGet (0 : F) [Q.c0, Q.c1, u.x, u.y, v.x, v.y]
  exact RExpr.eq_of_norm_eq env
    (e₁ := .sub (.sub (.add (.mul (.var 0) (.mul (.add (.var 2) (.var 4)) (.add (.var 2) (.var 4))))
                            (.mul (.var 1) (.mul (.add (.var 3) (.var 5)) (.add (.var 3) (.var 5)))))
                      (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
                            (.mul (.var 1) (.mul (.var 3) (.var 3)))))
                (.add (.mul (.var 0) (.mul (.var 4) (.var 4)))
                      (.mul (.var 1) (.mul (.var 5) (.var 5)))))
    (e₂ := .mul (.add .one .one)
                (.add (.mul (.var 0) (.mul (.var 2) (.var 4)))
                      (.mul (.var 1) (.mul (.var 3) (.var 5))))) rfl

def IsOrth2 (Q : QuadForm2 F) (M : Mat2 F) : Prop :=
  ∀ v : Vec2 F, Q.eval (M.mulVec v) = Q.eval v

def InSO2 (Q : QuadForm2 F) (M : Mat2 F) : Prop :=
  IsOrth2 Q M ∧ M.det = 1

theorem isOrth2_one (Q : QuadForm2 F) : IsOrth2 Q (Mat2.one F) := by
  intro v
  have hv : (Mat2.one F).mulVec v = v := by
    apply Vec2.ext <;> dsimp [Mat2.mulVec, Mat2.one]
    · rw [CommRingOps.one_mul, cr_zero_mul, cr_add_zero]
    · rw [cr_zero_mul, CommRingOps.one_mul, CommRingOps.zero_add]
  rw [hv]

theorem isOrth2_mul {Q : QuadForm2 F} {A B : Mat2 F}
    (hA : IsOrth2 Q A) (hB : IsOrth2 Q B) : IsOrth2 Q (Mat2.mul A B) := by
  intro v
  rw [Mat2.mulVec_mul, hA, hB]

theorem inSO2_one (Q : QuadForm2 F) : InSO2 Q (Mat2.one F) :=
  ⟨isOrth2_one Q, Mat2.det_one⟩

theorem inSO2_mul {Q : QuadForm2 F} {A B : Mat2 F}
    (hA : InSO2 Q A) (hB : InSO2 Q B) : InSO2 Q (Mat2.mul A B) := by
  refine ⟨isOrth2_mul hA.1 hB.1, ?_⟩
  rw [Mat2.det_mul, hA.2, hB.2, cr_mul_one]

/-- Orthogonal reflection matrix along an anisotropic vector `u` (`Q(u) ≠ 0`):
    represents `v mapsto v - Q(u)⁻¹ B_Q(u, v) u`. -/
def refl2 (Q : QuadForm2 F) (u : Vec2 F) : Mat2 F :=
  let iq := (Q.eval u)⁻¹
  ⟨1 - iq * (twoF F * Q.c0 * u.x) * u.x,
   -(iq * (twoF F * Q.c1 * u.y) * u.x),
   -(iq * (twoF F * Q.c0 * u.x) * u.y),
   1 - iq * (twoF F * Q.c1 * u.y) * u.y⟩

/-- `refl2 Q u` implements the exact coordinate-free reflection formula
    `r_u(v) = v - Q(u)⁻¹ B_Q(u, v) u`. -/
theorem refl2_mulVec (Q : QuadForm2 F) (u v : Vec2 F) :
    (refl2 Q u).mulVec v =
      ⟨v.x - (Q.eval u)⁻¹ * Q.polar u v * u.x,
       v.y - (Q.eval u)⁻¹ * Q.polar u v * u.y⟩ := by
  rw [QuadForm2.polar_eq]
  let env := envGet (0 : F) [Q.c0, Q.c1, u.x, u.y, v.x, v.y, (Q.eval u)⁻¹]
  let twoe : RExpr := .add .one .one
  apply Vec2.ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.sub .one (.mul (.mul (.var 6) (.mul (.mul twoe (.var 0)) (.var 2))) (.var 2))) (.var 4))
                  (.mul (.neg (.mul (.mul (.var 6) (.mul (.mul twoe (.var 1)) (.var 3))) (.var 2))) (.var 5)))
      (e₂ := .sub (.var 4)
                  (.mul (.mul (.var 6)
                              (.mul twoe (.add (.mul (.var 0) (.mul (.var 2) (.var 4)))
                                               (.mul (.var 1) (.mul (.var 3) (.var 5))))))
                        (.var 2))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.neg (.mul (.mul (.var 6) (.mul (.mul twoe (.var 0)) (.var 2))) (.var 3))) (.var 4))
                  (.mul (.sub .one (.mul (.mul (.var 6) (.mul (.mul twoe (.var 1)) (.var 3))) (.var 3))) (.var 5)))
      (e₂ := .sub (.var 5)
                  (.mul (.mul (.var 6)
                              (.mul twoe (.add (.mul (.var 0) (.mul (.var 2) (.var 4)))
                                               (.mul (.var 1) (.mul (.var 3) (.var 5))))))
                        (.var 3))) rfl

/-- Every reflection `refl2 Q u` (`Q(u) ≠ 0`) is an orthogonal transformation (`IsOrth2 Q`). -/
theorem refl2_isOrth (Q : QuadForm2 F) {u : Vec2 F} (hu : Q.eval u ≠ 0) :
    IsOrth2 Q (refl2 Q u) := by
  intro v
  rw [refl2_mulVec]
  have hinv : Q.eval u * (Q.eval u)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ hu
  let t := (Q.eval u)⁻¹ * Q.polar u v
  have hstep1 :
      Q.eval ⟨v.x - t * u.x, v.y - t * u.y⟩ =
        Q.eval v - t * (twoF F * (Q.c0 * (u.x * v.x) + Q.c1 * (u.y * v.y))) + (t * t) * Q.eval u := by
    have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [Q.c0, Q.c1, u.x, u.y, v.x, v.y, t])
      (e₁ := .add (.mul (.var 0) (.mul (.sub (.var 4) (.mul (.var 6) (.var 2)))
                                       (.sub (.var 4) (.mul (.var 6) (.var 2)))))
                  (.mul (.var 1) (.mul (.sub (.var 5) (.mul (.var 6) (.var 3)))
                                       (.sub (.var 5) (.mul (.var 6) (.var 3))))))
      (e₂ := .add (.sub (.add (.mul (.var 0) (.mul (.var 4) (.var 4)))
                              (.mul (.var 1) (.mul (.var 5) (.var 5))))
                        (.mul (.var 6)
                              (.mul (.add .one .one)
                                    (.add (.mul (.var 0) (.mul (.var 2) (.var 4)))
                                          (.mul (.var 1) (.mul (.var 3) (.var 5)))))))
                  (.mul (.mul (.var 6) (.var 6))
                        (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
                              (.mul (.var 1) (.mul (.var 3) (.var 3)))))) rfl
    exact hr
  change Q.eval ⟨v.x - t * u.x, v.y - t * u.y⟩ = Q.eval v
  rw [hstep1, ← QuadForm2.polar_eq Q u v]
  let b := Q.polar u v
  let iq := (Q.eval u)⁻¹
  let q := Q.eval u
  have hstep2 :
      Q.eval v - (iq * b) * b + ((iq * b) * (iq * b)) * q =
        Q.eval v + (q * iq - 1) * (iq * (b * b)) := by
    have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [Q.eval v, q, iq, b])
      (e₁ := .add (.sub (.var 0) (.mul (.mul (.var 2) (.var 3)) (.var 3)))
                  (.mul (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.var 1)))
      (e₂ := .add (.var 0)
                  (.mul (.sub (.mul (.var 1) (.var 2)) .one)
                        (.mul (.var 2) (.mul (.var 3) (.var 3))))) rfl
    exact hr
  change Q.eval v - (iq * b) * b + ((iq * b) * (iq * b)) * q = Q.eval v
  rw [hstep2]
  have hg : q * iq - 1 = 0 := by change Q.eval u * (Q.eval u)⁻¹ - 1 = 0; rw [hinv, cr_sub_self]
  rw [hg, cr_zero_mul, cr_add_zero]

/-- Helper for `s0 * u.x + s1 * u.y = 2` where `s0 = iq * (2 c0 u.x)`, `s1 = iq * (2 c1 u.y)`. -/
theorem refl2_trace_aux (Q : QuadForm2 F) {u : Vec2 F} (hu : Q.eval u ≠ 0) :
    ((Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)) * u.x +
    ((Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)) * u.y = twoF F := by
  have hinv : Q.eval u * (Q.eval u)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ hu
  have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [Q.c0, Q.c1, u.x, u.y, (Q.eval u)⁻¹])
    (e₁ := .add (.mul (.mul (.var 4) (.mul (.mul (.add .one .one) (.var 0)) (.var 2))) (.var 2))
                (.mul (.mul (.var 4) (.mul (.mul (.add .one .one) (.var 1)) (.var 3))) (.var 3)))
    (e₂ := .mul (.add .one .one)
                (.mul (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
                            (.mul (.var 1) (.mul (.var 3) (.var 3))))
                      (.var 4))) rfl
  change _ = twoF F
  calc
    ((Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)) * u.x +
        ((Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)) * u.y
        = twoF F * (Q.eval u * (Q.eval u)⁻¹) := hr
    _ = twoF F := by rw [hinv, cr_mul_one]

/-- Every reflection `refl2 Q u` (`Q(u) ≠ 0`) is an involution: `r_u^2 = I_2`. -/
theorem refl2_involutive (Q : QuadForm2 F) {u : Vec2 F} (hu : Q.eval u ≠ 0) :
    Mat2.mul (refl2 Q u) (refl2 Q u) = Mat2.one F := by
  let s0 := (Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)
  let s1 := (Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)
  have hsum : s0 * u.x + s1 * u.y - twoF F = 0 := by
    change ((Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)) * u.x +
           ((Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)) * u.y - twoF F = 0
    rw [refl2_trace_aux Q hu, cr_sub_self]
  let env := envGet (0 : F) [s0, s1, u.x, u.y]
  let gape : RExpr := .sub (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.add .one .one)
  apply Mat2.ext
  · have hr := RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.sub .one (.mul (.var 0) (.var 2))) (.sub .one (.mul (.var 0) (.var 2))))
                  (.mul (.neg (.mul (.var 1) (.var 2))) (.neg (.mul (.var 0) (.var 3)))))
      (e₂ := .add .one (.mul (.mul (.var 0) (.var 2)) gape)) rfl
    change (1 - s0 * u.x) * (1 - s0 * u.x) + (-(s1 * u.x)) * (-(s0 * u.y)) = 1
    calc
      (1 - s0 * u.x) * (1 - s0 * u.x) + (-(s1 * u.x)) * (-(s0 * u.y))
          = 1 + (s0 * u.x) * (s0 * u.x + s1 * u.y - twoF F) := hr
      _ = 1 := by rw [hsum, cr_mul_zero, cr_add_zero]
  · have hr := RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.sub .one (.mul (.var 0) (.var 2))) (.neg (.mul (.var 1) (.var 2))))
                  (.mul (.neg (.mul (.var 1) (.var 2))) (.sub .one (.mul (.var 1) (.var 3)))))
      (e₂ := .mul (.mul (.var 1) (.var 2)) gape) rfl
    change (1 - s0 * u.x) * (-(s1 * u.x)) + (-(s1 * u.x)) * (1 - s1 * u.y) = 0
    calc
      (1 - s0 * u.x) * (-(s1 * u.x)) + (-(s1 * u.x)) * (1 - s1 * u.y)
          = (s1 * u.x) * (s0 * u.x + s1 * u.y - twoF F) := hr
      _ = 0 := by rw [hsum, cr_mul_zero]
  · have hr := RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.neg (.mul (.var 0) (.var 3))) (.sub .one (.mul (.var 0) (.var 2))))
                  (.mul (.sub .one (.mul (.var 1) (.var 3))) (.neg (.mul (.var 0) (.var 3)))))
      (e₂ := .mul (.mul (.var 0) (.var 3)) gape) rfl
    change (-(s0 * u.y)) * (1 - s0 * u.x) + (1 - s1 * u.y) * (-(s0 * u.y)) = 0
    calc
      (-(s0 * u.y)) * (1 - s0 * u.x) + (1 - s1 * u.y) * (-(s0 * u.y))
          = (s0 * u.y) * (s0 * u.x + s1 * u.y - twoF F) := hr
      _ = 0 := by rw [hsum, cr_mul_zero]
  · have hr := RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.neg (.mul (.var 0) (.var 3))) (.neg (.mul (.var 1) (.var 2))))
                  (.mul (.sub .one (.mul (.var 1) (.var 3))) (.sub .one (.mul (.var 1) (.var 3)))))
      (e₂ := .add .one (.mul (.mul (.var 1) (.var 3)) gape)) rfl
    change (-(s0 * u.y)) * (-(s1 * u.x)) + (1 - s1 * u.y) * (1 - s1 * u.y) = 1
    calc
      (-(s0 * u.y)) * (-(s1 * u.x)) + (1 - s1 * u.y) * (1 - s1 * u.y)
          = 1 + (s1 * u.y) * (s0 * u.x + s1 * u.y - twoF F) := hr
      _ = 1 := by rw [hsum, cr_mul_zero, cr_add_zero]

/-- Every reflection `refl2 Q u` (`Q(u) ≠ 0`) has determinant `-1`. -/
theorem refl2_det (Q : QuadForm2 F) {u : Vec2 F} (hu : Q.eval u ≠ 0) :
    (refl2 Q u).det = -(1 : F) := by
  let s0 := (Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)
  let s1 := (Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)
  have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [s0, s1, u.x, u.y])
    (e₁ := .sub (.mul (.sub .one (.mul (.var 0) (.var 2))) (.sub .one (.mul (.var 1) (.var 3))))
                (.mul (.neg (.mul (.var 1) (.var 2))) (.neg (.mul (.var 0) (.var 3)))))
    (e₂ := .sub .one (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))) rfl
  change (1 - s0 * u.x) * (1 - s1 * u.y) - (-(s1 * u.x)) * (-(s0 * u.y)) = -(1 : F)
  calc
    (1 - s0 * u.x) * (1 - s1 * u.y) - (-(s1 * u.x)) * (-(s0 * u.y))
        = 1 - (s0 * u.x + s1 * u.y) := hr
    _ = 1 - twoF F := by
      change 1 - (((Q.eval u)⁻¹ * (twoF F * Q.c0 * u.x)) * u.x +
                  ((Q.eval u)⁻¹ * (twoF F * Q.c1 * u.y)) * u.y) = 1 - twoF F
      rw [refl2_trace_aux Q hu]
    _ = -(1 : F) :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .sub .one (.add .one .one)) (e₂ := .neg .one) rfl

/-! ## Reflection Decompositions, Parity by Determinant, and Minimal Reflection Count -/

def IsReflection2 (Q : QuadForm2 F) (r : Mat2 F) : Prop :=
  ∃ u : Vec2 F, Q.eval u ≠ 0 ∧ r = refl2 Q u

def mat2Prod : List (Mat2 F) → Mat2 F
  | [] => Mat2.one F
  | M :: rest => Mat2.mul M (mat2Prod rest)

def IsReflDecomp2 (Q : QuadForm2 F) (g : Mat2 F) (rs : List (Mat2 F)) : Prop :=
  (∀ r, r ∈ rs → IsReflection2 Q r) ∧ mat2Prod rs = g

def HasReflCount2 (Q : QuadForm2 F) (g : Mat2 F) (k : Nat) : Prop :=
  ∃ rs : List (Mat2 F), rs.length = k ∧ IsReflDecomp2 Q g rs

def IsMinReflCount2 (Q : QuadForm2 F) (g : Mat2 F) (k : Nat) : Prop :=
  HasReflCount2 Q g k ∧ ∀ m : Nat, m < k → ¬ HasReflCount2 Q g m

/-- **Positive Parity Theorem (2D):** Every reflection decomposition `rs` of `g` has
    `det g = (-1)^(rs.length)`. -/
theorem reflDecomp2_det_parity {Q : QuadForm2 F} {g : Mat2 F} {rs : List (Mat2 F)}
    (hd : IsReflDecomp2 Q g rs) : g.det = signPow F rs.length := by
  obtain ⟨hrs, hprod⟩ := hd
  rw [← hprod]
  clear hprod
  induction rs with
  | nil =>
    change (Mat2.one F).det = 1
    exact Mat2.det_one
  | cons r rest ih =>
    have hr : IsReflection2 Q r := hrs r (.head _)
    obtain ⟨u, hu, rfl⟩ := hr
    have hrest : ∀ r', r' ∈ rest → IsReflection2 Q r' :=
      fun r' hm => hrs r' (.tail _ hm)
    change (Mat2.mul (refl2 Q u) (mat2Prod rest)).det = -(signPow F rest.length)
    rw [Mat2.det_mul, refl2_det Q hu, ih hrest]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [signPow F rest.length])
      (e₁ := .mul (.neg .one) (.var 0))
      (e₂ := .neg (.var 0)) rfl

/-- Corollary: Every reflection decomposition of a rotation `R ∈ SO(F^2, Q)` has even length,
    and every reflection decomposition of an improper orthogonal transformation (`det = -1`)
    has odd length. -/
theorem reflCount2_parity_iff {Q : QuadForm2 F} {g : Mat2 F} {k : Nat}
    (hc : HasReflCount2 Q g k) :
    (g.det = 1 ↔ k % 2 = 0) ∧ (g.det = -(1 : F) ↔ k % 2 = 1) := by
  obtain ⟨rs, hlen, hd⟩ := hc
  have hdet := reflDecomp2_det_parity hd
  rw [hlen] at hdet
  rw [hdet]
  exact ⟨signPow_even_iff k, signPow_odd_iff k⟩

/-! ## Complete Euclidean `O_2(F)` & `SO_2(F)` Structure and Minimal Reflection Counts -/

theorem orth2_euc_entries {M : Mat2 F} (hM : IsOrth2 (Q20 F) M) :
    M.a00 * M.a00 + M.a10 * M.a10 = 1 ∧
    M.a01 * M.a01 + M.a11 * M.a11 = 1 ∧
    M.a00 * M.a01 + M.a10 * M.a11 = 0 ∧
    (M.det = 1 ∨ M.det = -(1 : F)) := by
  have he0 := hM ⟨1, 0⟩
  have he1 := hM ⟨0, 1⟩
  have he11 := hM ⟨1, 1⟩
  have h0 : M.a00 * M.a00 + M.a10 * M.a10 = 1 := by
    calc
      M.a00 * M.a00 + M.a10 * M.a10 = (Q20 F).eval (M.mulVec ⟨1, 0⟩) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
          (e₁ := .add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))
          (e₂ := .add (.mul .one (.mul (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                                       (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))))
                      (.mul .one (.mul (.add (.mul (.var 2) .one) (.mul (.var 3) .zero))
                                       (.add (.mul (.var 2) .one) (.mul (.var 3) .zero))))) rfl
      _ = (Q20 F).eval ⟨1, 0⟩ := he0
      _ = 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .one .one)) (.mul .one (.mul .zero .zero)))
          (e₂ := .one) rfl
  have h1 : M.a01 * M.a01 + M.a11 * M.a11 = 1 := by
    calc
      M.a01 * M.a01 + M.a11 * M.a11 = (Q20 F).eval (M.mulVec ⟨0, 1⟩) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
          (e₁ := .add (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3)))
          (e₂ := .add (.mul .one (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))
                                       (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))))
                      (.mul .one (.mul (.add (.mul (.var 2) .zero) (.mul (.var 3) .one))
                                       (.add (.mul (.var 2) .zero) (.mul (.var 3) .one))))) rfl
      _ = (Q20 F).eval ⟨0, 1⟩ := he1
      _ = 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul .one (.mul .one .one)))
          (e₂ := .one) rfl
  have hdot2 : twoF F * (M.a00 * M.a01 + M.a10 * M.a11) = 0 := by
    have hexp :
        (Q20 F).eval (M.mulVec ⟨1, 1⟩) -
          (M.a00 * M.a00 + M.a10 * M.a10) -
          (M.a01 * M.a01 + M.a11 * M.a11) =
          twoF F * (M.a00 * M.a01 + M.a10 * M.a11) :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
        (e₁ := .sub (.sub (.add (.mul .one (.mul (.add (.mul (.var 0) .one) (.mul (.var 1) .one))
                                                 (.add (.mul (.var 0) .one) (.mul (.var 1) .one))))
                                (.mul .one (.mul (.add (.mul (.var 2) .one) (.mul (.var 3) .one))
                                                 (.add (.mul (.var 2) .one) (.mul (.var 3) .one)))))
                          (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))
                    (.add (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3))))
        (e₂ := .mul (.add .one .one)
                    (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))) rfl
    rw [← hexp, he11, h0, h1]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .sub (.sub (.add (.mul .one (.mul .one .one)) (.mul .one (.mul .one .one))) .one) .one)
      (e₂ := .zero) rfl
  have hdot : M.a00 * M.a01 + M.a10 * M.a11 = 0 := by
    cases mul_eq_zeroF hdot2 with
    | inl h2 => exact False.elim (two_ne_zeroF h2)
    | inr hd => exact hd
  have hdetsq : (M.det - 1) * (M.det + 1) = 0 := by
    have hlag :
        (M.det - 1) * (M.det + 1) =
          (M.a00 * M.a00 + M.a10 * M.a10) * (M.a01 * M.a01 + M.a11 * M.a11) -
          (M.a00 * M.a01 + M.a10 * M.a11) * (M.a00 * M.a01 + M.a10 * M.a11) - 1 :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
        (e₁ := .mul (.sub (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) .one)
                    (.add (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) .one))
        (e₂ := .sub (.sub (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))
                                (.add (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3))))
                          (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
                                (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))))
                    .one) rfl
    rw [hlag, h0, h1, hdot]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .sub (.sub (.mul .one .one) (.mul .zero .zero)) .one)
      (e₂ := .zero) rfl
  have hdetpm : M.det = 1 ∨ M.det = -(1 : F) := by
    cases mul_eq_zeroF hdetsq with
    | inl hm => exact Or.inl (cr_eq_of_sub_eq_zero hm)
    | inr hp =>
      rw [CommRingOps.add_comm] at hp
      exact Or.inr (cr_neg_eq_of_add_eq_zero hp).symm
  exact ⟨h0, h1, hdot, hdetpm⟩

/-- Every improper orthogonal `2 × 2` matrix (`IsOrth2 Q20 S ∧ S.det = -1`) is a single reflection! -/
theorem orth2_det_neg_one_isReflection {S : Mat2 F}
    (hO : IsOrth2 (Q20 F) S) (hdet : S.det = -(1 : F)) :
    IsReflection2 (Q20 F) S := by
  obtain ⟨h0, h1, _, _⟩ := orth2_euc_entries hO
  have hsumsq : (S.a00 + S.a11) * (S.a00 + S.a11) + (S.a01 - S.a10) * (S.a01 - S.a10) = 0 := by
    have hid :
        (S.a00 + S.a11) * (S.a00 + S.a11) + (S.a01 - S.a10) * (S.a01 - S.a10) =
          (S.a00 * S.a00 + S.a10 * S.a10) + (S.a01 * S.a01 + S.a11 * S.a11) + twoF F * S.det :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [S.a00, S.a01, S.a10, S.a11])
        (e₁ := .add (.mul (.add (.var 0) (.var 3)) (.add (.var 0) (.var 3)))
                    (.mul (.sub (.var 1) (.var 2)) (.sub (.var 1) (.var 2))))
        (e₂ := .add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))
                          (.add (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3))))
                    (.mul (.add .one .one) (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))) rfl
    rw [hid, h0, h1, hdet]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .add (.add .one .one) (.mul (.add .one .one) (.neg .one)))
      (e₂ := .zero) rfl
  obtain ⟨htr, hsym⟩ := sum_two_sq_eq_zeroF hsumsq
  have ha11 : S.a11 = -S.a00 := (cr_neg_eq_of_add_eq_zero htr).symm
  have ha10 : S.a10 = S.a01 := (cr_eq_of_sub_eq_zero hsym).symm
  have hab : S.a00 * S.a00 + S.a01 * S.a01 = 1 := by
    rw [← ha10]; exact h0
  by_cases ha1 : S.a00 = 1
  · have hb0 : S.a01 = 0 := by
      have hb2 : S.a01 * S.a01 + 0 * 0 = 0 := by
        rw [ha1, cr_mul_one] at hab
        have hb0' : S.a01 * S.a01 = 0 := by
          apply cr_add_left_cancel (a := (1 : F))
          rw [hab, cr_add_zero]
        rw [hb0', cr_mul_zero, cr_add_zero]
      exact (sum_two_sq_eq_zeroF hb2).1
    refine ⟨⟨0, 1⟩, ?_, ?_⟩
    · have hq : (Q20 F).eval ⟨0, 1⟩ = 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul .one (.mul .one .one)))
          (e₂ := .one) rfl
      rw [hq]; exact one_ne_zeroF
    · have hq1 : ((Q20 F).eval ⟨0, 1⟩)⁻¹ = 1 := by
        have hq : (Q20 F).eval ⟨0, 1⟩ = 1 :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [])
            (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul .one (.mul .one .one)))
            (e₂ := .one) rfl
        rw [hq]
        have h11 : (1 : F) * (1 : F)⁻¹ = 1 := FormallyRealField.mul_inv_cancel 1 one_ne_zeroF
        rw [CommRingOps.one_mul] at h11
        exact h11
      apply Mat2.ext
      · rw [ha1]; unfold refl2; rw [hq1]
        exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .one)
          (e₂ := .sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .zero)) .zero)) rfl
      · rw [hb0]; unfold refl2; rw [hq1]
        exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .zero)
          (e₂ := .neg (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .zero)) rfl
      · rw [ha10, hb0]; unfold refl2; rw [hq1]
        exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .zero)
          (e₂ := .neg (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .zero)) .one)) rfl
      · rw [ha11, ha1]; unfold refl2; rw [hq1]
        exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .neg .one)
          (e₂ := .sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .one)) rfl
  · let w : Vec2 F := ⟨1 - S.a00, -S.a01⟩
    have hqw : (Q20 F).eval w = twoF F * (1 - S.a00) := by
      calc
        (Q20 F).eval w = (S.a00 * S.a00 + S.a01 * S.a01 - 1) + twoF F * (1 - S.a00) :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [S.a00, S.a01])
            (e₁ := .add (.mul .one (.mul (.sub .one (.var 0)) (.sub .one (.var 0))))
                        (.mul .one (.mul (.neg (.var 1)) (.neg (.var 1)))))
            (e₂ := .add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) .one)
                        (.mul (.add .one .one) (.sub .one (.var 0)))) rfl
        _ = twoF F * (1 - S.a00) := by rw [hab, cr_sub_self, CommRingOps.zero_add]
    have h1ma : 1 - S.a00 ≠ 0 := by
      intro hz
      exact ha1 (cr_eq_of_sub_eq_zero hz).symm
    have hqw_ne : (Q20 F).eval w ≠ 0 := by
      rw [hqw]
      intro hz
      cases mul_eq_zeroF hz with
      | inl h2 => exact two_ne_zeroF h2
      | inr hd => exact h1ma hd
    refine ⟨w, hqw_ne, ?_⟩
    have hinv : (twoF F * (1 - S.a00)) * ((Q20 F).eval w)⁻¹ = 1 := by
      rw [← hqw]
      exact FormallyRealField.mul_inv_cancel _ hqw_ne
    let gapF : F := (twoF F * (1 - S.a00)) * ((Q20 F).eval w)⁻¹ - 1
    have hg0 : gapF = 0 := by
      change (twoF F * (1 - S.a00)) * ((Q20 F).eval w)⁻¹ - 1 = 0
      rw [hinv, cr_sub_self]
    let env := envGet (0 : F) [S.a00, S.a01, ((Q20 F).eval w)⁻¹]
    let twoe : RExpr := .add .one .one
    let gape : RExpr := .sub (.mul (.mul twoe (.sub .one (.var 0))) (.var 2)) .one
    let sqgape : RExpr := .sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) .one
    apply Mat2.ext
    · have hid : (refl2 (Q20 F) w).a00 = S.a00 - gapF * (1 - S.a00) :=
        RExpr.eq_of_norm_eq env
          (e₁ := .sub .one (.mul (.mul (.var 2) (.mul (.mul twoe .one) (.sub .one (.var 0))))
                                 (.sub .one (.var 0))))
          (e₂ := .sub (.var 0) (.mul gape (.sub .one (.var 0)))) rfl
      rw [hid, hg0, cr_zero_mul, CommRingOps.sub_eq_add_neg, cr_neg_zero, cr_add_zero]
    · have hid : (refl2 (Q20 F) w).a01 = S.a01 + gapF * S.a01 :=
        RExpr.eq_of_norm_eq env
          (e₁ := .neg (.mul (.mul (.var 2) (.mul (.mul twoe .one) (.neg (.var 1))))
                            (.sub .one (.var 0))))
          (e₂ := .add (.var 1) (.mul gape (.var 1))) rfl
      rw [hid, hg0, cr_zero_mul, cr_add_zero]
    · rw [ha10]
      have hid : (refl2 (Q20 F) w).a10 = S.a01 + gapF * S.a01 :=
        RExpr.eq_of_norm_eq env
          (e₁ := .neg (.mul (.mul (.var 2) (.mul (.mul twoe .one) (.sub .one (.var 0))))
                            (.neg (.var 1))))
          (e₂ := .add (.var 1) (.mul gape (.var 1))) rfl
      rw [hid, hg0, cr_zero_mul, cr_add_zero]
    · rw [ha11]
      have hid : (refl2 (Q20 F) w).a11 =
          (-S.a00 - gapF * (1 + S.a00)) -
            (twoF F * ((Q20 F).eval w)⁻¹) * (S.a00 * S.a00 + S.a01 * S.a01 - 1) :=
        RExpr.eq_of_norm_eq env
          (e₁ := .sub .one (.mul (.mul (.var 2) (.mul (.mul twoe .one) (.neg (.var 1))))
                                 (.neg (.var 1))))
          (e₂ := .sub (.sub (.neg (.var 0)) (.mul gape (.add .one (.var 0))))
                      (.mul (.mul twoe (.var 2)) sqgape)) rfl
      rw [hid, hab, cr_sub_self, cr_mul_zero, hg0, cr_zero_mul,
          CommRingOps.sub_eq_add_neg, CommRingOps.sub_eq_add_neg,
          cr_neg_zero, cr_add_zero, cr_add_zero]

/-- Parameterized family of slope vectors `u_t = (1, t)` in `F^2`: always anisotropic (`1 + t^2 ≠ 0`)
    and yielding pairwise distinct reflection operators `refl2 Q20 (1, t)`! -/
def slopeVec (t : F) : Vec2 F := ⟨1, t⟩

theorem slopeVec_anisotropic (t : F) : (Q20 F).eval (slopeVec t) ≠ 0 := by
  have heq : (Q20 F).eval (slopeVec t) = 1 + t * t :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [t])
      (e₁ := .add (.mul .one (.mul .one .one)) (.mul .one (.mul (.var 0) (.var 0))))
      (e₂ := .add .one (.mul (.var 0) (.var 0))) rfl
  rw [heq]
  exact one_add_sq_ne_zeroF t

/-- **Operator Injectivity:** `refl2 Q20 (1, t) = refl2 Q20 (1, s) ↔ t = s`! -/
theorem refl2_slopeVec_inj {t s : F} (h : refl2 (Q20 F) (slopeVec t) = refl2 (Q20 F) (slopeVec s)) :
    t = s := by
  -- Evaluate both operators on `v = (-s, 1)`: `refl2 Q20 (1, s)` fixes `(-s, 1)`!
  let v : Vec2 F := ⟨-s, 1⟩
  have heval : (refl2 (Q20 F) (slopeVec t)).mulVec v = (refl2 (Q20 F) (slopeVec s)).mulVec v :=
    congrArg (fun M => M.mulVec v) h
  rw [refl2_mulVec, refl2_mulVec] at heval
  have hpol_s : (Q20 F).polar (slopeVec s) v = 0 :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [s])
      (e₁ := .sub (.sub (.add (.mul .one (.mul (.add .one (.neg (.var 0))) (.add .one (.neg (.var 0)))))
                              (.mul .one (.mul (.add (.var 0) .one) (.add (.var 0) .one))))
                        (.add (.mul .one (.mul .one .one)) (.mul .one (.mul (.var 0) (.var 0)))))
                  (.add (.mul .one (.mul (.neg (.var 0)) (.neg (.var 0))))
                        (.mul .one (.mul .one .one))))
      (e₂ := .zero) rfl
  have hpol_t : (Q20 F).polar (slopeVec t) v = twoF F * (t - s) :=
    RExpr.eq_of_norm_eq (envGet (0 : F) [t, s])
      (e₁ := .sub (.sub (.add (.mul .one (.mul (.add .one (.neg (.var 1))) (.add .one (.neg (.var 1)))))
                              (.mul .one (.mul (.add (.var 0) .one) (.add (.var 0) .one))))
                        (.add (.mul .one (.mul .one .one)) (.mul .one (.mul (.var 0) (.var 0)))))
                  (.add (.mul .one (.mul (.neg (.var 1)) (.neg (.var 1))))
                        (.mul .one (.mul .one .one))))
      (e₂ := .mul (.add .one .one) (.sub (.var 0) (.var 1))) rfl
  have hx := congrArg Vec2.x heval
  dsimp only at hx
  rw [hpol_s, hpol_t] at hx
  change -s - ((Q20 F).eval (slopeVec t))⁻¹ * (twoF F * (t - s)) * 1 =
         -s - ((Q20 F).eval (slopeVec s))⁻¹ * 0 * 1 at hx
  rw [cr_mul_zero, cr_zero_mul, cr_mul_one] at hx
  have hzero : ((Q20 F).eval (slopeVec t))⁻¹ * (twoF F * (t - s)) = 0 := by
    have hrhs : -s - 0 = -s := by
      rw [CommRingOps.sub_eq_add_neg, cr_neg_zero, cr_add_zero]
    rw [hrhs] at hx
    apply cr_add_left_cancel (a := s)
    calc
      s + ((Q20 F).eval (slopeVec t))⁻¹ * (twoF F * (t - s))
          = -(-s - ((Q20 F).eval (slopeVec t))⁻¹ * (twoF F * (t - s))) :=
            RExpr.eq_of_norm_eq
              (envGet (0 : F) [s, ((Q20 F).eval (slopeVec t))⁻¹ * (twoF F * (t - s))])
              (e₁ := .add (.var 0) (.var 1))
              (e₂ := .neg (.sub (.neg (.var 0)) (.var 1))) rfl
      _ = -(-s) := by rw [hx]
      _ = s + 0 := by rw [cr_neg_neg, cr_add_zero]
  cases mul_eq_zeroF hzero with
  | inl hinv0 =>
    exfalso
    have hmul1 := FormallyRealField.mul_inv_cancel _ (slopeVec_anisotropic t)
    rw [hinv0, cr_mul_zero] at hmul1
    exact one_ne_zeroF hmul1.symm
  | inr h2ts =>
    cases mul_eq_zeroF h2ts with
    | inl h2 => exact False.elim (two_ne_zeroF h2)
    | inr hts => exact cr_eq_of_sub_eq_zero hts

/-- **Universal Parameterized Two-Reflection Factorization of Any Planar Rotation:**
    For EVERY `R ∈ SO_2(F)` and EVERY `t ∈ F`, setting `r₁ = refl2 Q20 (1, t)` and
    `r₂ = r₁ * R` gives two genuine reflections in `O_2(F)` with `[r₁, r₂]` decomposing `R`! -/
theorem so2_param_reflDecomp {R : Mat2 F} (hR : InSO2 (Q20 F) R) (t : F) :
    let r₁ := refl2 (Q20 F) (slopeVec t)
    let r₂ := Mat2.mul r₁ R
    IsReflection2 (Q20 F) r₁ ∧
    IsReflection2 (Q20 F) r₂ ∧
    IsReflDecomp2 (Q20 F) R [r₁, r₂] := by
  intro r₁ r₂
  have hu : (Q20 F).eval (slopeVec t) ≠ 0 := slopeVec_anisotropic t
  have hr1 : IsReflection2 (Q20 F) r₁ := ⟨slopeVec t, hu, rfl⟩
  have hr2O : IsOrth2 (Q20 F) r₂ := isOrth2_mul (refl2_isOrth (Q20 F) hu) hR.1
  have hr2det : r₂.det = -(1 : F) := by
    change (Mat2.mul r₁ R).det = -(1 : F)
    rw [Mat2.det_mul, refl2_det (Q20 F) hu, hR.2, cr_mul_one]
  have hr2 : IsReflection2 (Q20 F) r₂ := orth2_det_neg_one_isReflection hr2O hr2det
  refine ⟨hr1, hr2, ?_, ?_⟩
  · intro r hmem
    cases hmem with
    | head => exact hr1
    | tail _ hmem2 =>
      cases hmem2 with
      | head => exact hr2
      | tail _ hnil => nomatch hnil
  · change Mat2.mul r₁ (Mat2.mul r₂ (Mat2.one F)) = R
    rw [Mat2.mul_one, ← Mat2.mul_assoc, refl2_involutive (Q20 F) hu, Mat2.one_mul]

/-- **Complete Euclidean `SO_2(F) \ {I_2}` Minimal Reflection Count (`= 2`):**
    Every non-identity planar rotation `R ∈ SO_2(F)` has exact minimal reflection count `2`. -/
theorem so2_nonid_minReflCount_two {R : Mat2 F} (hR : InSO2 (Q20 F) R) (hne : R ≠ Mat2.one F) :
    IsMinReflCount2 (Q20 F) R 2 := by
  refine ⟨⟨[refl2 (Q20 F) (slopeVec 0), Mat2.mul (refl2 (Q20 F) (slopeVec 0)) R],
           rfl, (so2_param_reflDecomp hR 0).2.2⟩, ?_⟩
  intro m hm hc
  obtain ⟨rs, hlen, hd⟩ := hc
  cases rs with
  | nil =>
    exact hne hd.2.symm
  | cons r₁ rest =>
    cases rest with
    | nil =>
      have hpar := (reflCount2_parity_iff ⟨[r₁], rfl, hd⟩).1
      have hm0 : (1 : Nat) % 2 = 0 := hpar.mp hR.2
      omega
    | cons _ _ =>
      simp at hlen
      omega

/-- **Refutation R1 (Infinite Minimal-Length Reflection-Operator Decompositions & Unbounded Lengths):**
    For EVERY non-identity rotation `R ∈ SO_2(F)`:
    1. Its minimal reflection count is `2`,
    2. The sequence `n ↦ [r_n, r_n * R]` (`r_n = refl2 Q20 (1, n)`) consists of infinitely many
       pairwise distinct minimal-length (`k = 2`) reflection-operator decompositions of `R`,
    3. No finite pool of operators `pool : List (Mat2 F)` contains even all first-factor reflections
       appearing in minimal decompositions of `R` (nor unordered pairs `{r₁, r₂}`!),
    4. `R` also admits valid reflection decompositions of length `2 + 2 * m` for EVERY `m : Nat`. -/
theorem so2_infinite_reflection_counting {R : Mat2 F}
    (hR : InSO2 (Q20 F) R) (hne : R ≠ Mat2.one F) :
    IsMinReflCount2 (Q20 F) R 2 ∧
    (∃ pairSeq : Nat → Mat2 F × Mat2 F,
      (∀ n : Nat,
        IsReflDecomp2 (Q20 F) R [(pairSeq n).1, (pairSeq n).2] ∧
        (pairSeq n).1 ≠ (pairSeq n).2) ∧
      (∀ m n : Nat, m ≠ n → (pairSeq m).1 ≠ (pairSeq n).1) ∧
      (∀ pool : List (Mat2 F), ¬ (∀ n : Nat, (pairSeq n).1 ∈ pool))) ∧
    (∀ m : Nat, HasReflCount2 (Q20 F) R (2 + 2 * m)) := by
  refine ⟨so2_nonid_minReflCount_two hR hne, ?_, ?_⟩
  · let pairSeq : Nat → Mat2 F × Mat2 F := fun n =>
      let r₁ := refl2 (Q20 F) (slopeVec (crOfNat F n))
      (r₁, Mat2.mul r₁ R)
    refine ⟨pairSeq, ?_, ?_, ?_⟩
    · intro n
      have hdecomp := (so2_param_reflDecomp hR (crOfNat F n)).2.2
      refine ⟨hdecomp, ?_⟩
      intro heq
      -- If `r₁ = r₁ * R`, multiplying on left by `r₁` gives `I₂ = R`, contradiction!
      have hu := slopeVec_anisotropic (crOfNat F n)
      have hR1 : Mat2.one F = R := by
        calc
          Mat2.one F = Mat2.mul (refl2 (Q20 F) (slopeVec (crOfNat F n)))
                                (refl2 (Q20 F) (slopeVec (crOfNat F n))) :=
            (refl2_involutive (Q20 F) hu).symm
          _ = Mat2.mul (refl2 (Q20 F) (slopeVec (crOfNat F n)))
                       (Mat2.mul (refl2 (Q20 F) (slopeVec (crOfNat F n))) R) := by
            dsimp [pairSeq] at heq
            rw [← heq]
          _ = R := by
            rw [← Mat2.mul_assoc, refl2_involutive (Q20 F) hu, Mat2.one_mul]
      exact hne hR1.symm
    · intro m n hmn heq
      have ht : crOfNat F m = crOfNat F n := refl2_slopeVec_inj heq
      exact hmn (crOfNat_injF ht)
    · -- Pigeonhole: an injective map `Fin (pool.length + 1) → pool` is impossible!
      intro pool hcov
      have hpig : ∀ (L : List (Mat2 F)) (f : Nat → Mat2 F),
          (∀ i j : Nat, i ≠ j → f i ≠ f j) →
          ¬ (∀ i : Nat, i ≤ L.length → f i ∈ L) := by
        intro L
        induction L with
        | nil =>
          intro f _ hall
          nomatch hall 0 (Nat.zero_le 0)
        | cons a rest ih =>
          intro f hinj hall
          simp only [List.length_cons] at hall
          by_cases hex : ∃ k : Nat, k ≤ rest.length + 1 ∧ f k = a
          · obtain ⟨k, hk, hfk⟩ := hex
            let g : Nat → Mat2 F := fun i => if i < k then f i else f (i + 1)
            have hginj : ∀ i j : Nat, i ≠ j → g i ≠ g j := by
              intro i j hij
              dsimp [g]
              by_cases hi : i < k <;> by_cases hj : j < k <;> simp [hi, hj]
              · exact hinj i j hij
              · exact hinj i (j + 1) (by omega)
              · exact hinj (i + 1) j (by omega)
              · exact hinj (i + 1) (j + 1) (by omega)
            apply ih g hginj
            intro i hi
            dsimp [g]
            by_cases hik : i < k
            · simp only [hik, ↓reduceIte]
              have hmem := hall i (by omega)
              cases hmem with
              | head =>
                exfalso
                exact hinj i k (by omega) (hfk.symm ▸ rfl)
              | tail _ hm => exact hm
            · simp only [hik, ↓reduceIte]
              have hmem := hall (i + 1) (by omega)
              cases hmem with
              | head =>
                exfalso
                exact hinj (i + 1) k (by omega) (hfk.symm ▸ rfl)
              | tail _ hm => exact hm
          · apply ih f hinj
            intro i hi
            have hmem := hall i (by omega)
            cases hmem with
            | head =>
              exfalso
              exact hex ⟨i, by omega, rfl⟩
            | tail _ hm => exact hm
      exact hpig pool (fun n => (pairSeq n).1)
        (fun i j hij heq => hij (crOfNat_injF (refl2_slopeVec_inj heq)))
        (fun i _ => hcov i)
  · intro m
    induction m with
    | zero =>
      exact (so2_nonid_minReflCount_two hR hne).1
    | succ m ih =>
      obtain ⟨rs, hlen, hrs, hprod⟩ := ih
      let r₀ := refl2 (Q20 F) (slopeVec 0)
      have hu0 : (Q20 F).eval (slopeVec 0) ≠ 0 := slopeVec_anisotropic 0
      have hr0 : IsReflection2 (Q20 F) r₀ := ⟨slopeVec 0, hu0, rfl⟩
      refine ⟨r₀ :: r₀ :: rs, ?_, ?_, ?_⟩
      · simp [hlen]; omega
      · intro r hmem
        cases hmem with
        | head => exact hr0
        | tail _ hm1 =>
          cases hm1 with
          | head => exact hr0
          | tail _ hm2 => exact hrs r hm2
      · change Mat2.mul r₀ (Mat2.mul r₀ (mat2Prod rs)) = R
        rw [← Mat2.mul_assoc, refl2_involutive (Q20 F) hu0, Mat2.one_mul, hprod]

/-! ## Refutation R2a: Infinite Distinct-Angle Cayley Family in `SO_2(F)` with Constant Count `2` -/

/-- Rational Cayley planar rotation `R_t = (1 + t^2)⁻¹ [[1 - t^2, -2t], [2t, 1 - t^2]]`. -/
def cayleyRot2 (t : F) : Mat2 F :=
  let iq := (1 + t * t)⁻¹
  ⟨iq * (1 - t * t), -(iq * (twoF F * t)),
   iq * (twoF F * t), iq * (1 - t * t)⟩

theorem cayleyRot2_inSO2 (t : F) : InSO2 (Q20 F) (cayleyRot2 t) := by
  have hq : 1 + t * t ≠ 0 := one_add_sq_ne_zeroF t
  have hinv : (1 + t * t) * (1 + t * t)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ hq
  let iq := (1 + t * t)⁻¹
  let c := iq * (1 - t * t)
  let s := iq * (twoF F * t)
  have hcs : c * c + s * s = 1 := by
    have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [t, iq])
      (e₁ := .add (.mul (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0))))
                        (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0)))))
                  (.mul (.mul (.var 1) (.mul (.add .one .one) (.var 0)))
                        (.mul (.var 1) (.mul (.add .one .one) (.var 0)))))
      (e₂ := .mul (.mul (.add .one (.mul (.var 0) (.var 0))) (.var 1))
                  (.mul (.add .one (.mul (.var 0) (.var 0))) (.var 1))) rfl
    calc
      c * c + s * s = ((1 + t * t) * iq) * ((1 + t * t) * iq) := hr
      _ = 1 := by
        change ((1 + t * t) * (1 + t * t)⁻¹) * ((1 + t * t) * (1 + t * t)⁻¹) = 1
        rw [hinv, cr_mul_one]
  refine ⟨?_, ?_⟩
  · intro v
    have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [c, s, v.x, v.y])
      (e₁ := .add (.mul .one (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.neg (.var 1)) (.var 3)))
                                   (.add (.mul (.var 0) (.var 2)) (.mul (.neg (.var 1)) (.var 3)))))
                  (.mul .one (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
                                   (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))))))
      (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                  (.add (.mul .one (.mul (.var 2) (.var 2)))
                        (.mul .one (.mul (.var 3) (.var 3))))) rfl
    change 1 * ((c * v.x + (-s) * v.y) * (c * v.x + (-s) * v.y)) +
           1 * ((s * v.x + c * v.y) * (s * v.x + c * v.y)) =
           (Q20 F).eval v
    calc
      1 * ((c * v.x + (-s) * v.y) * (c * v.x + (-s) * v.y)) +
          1 * ((s * v.x + c * v.y) * (s * v.x + c * v.y))
          = (c * c + s * s) * (Q20 F).eval v := hr
      _ = (Q20 F).eval v := by rw [hcs, CommRingOps.one_mul]
  · have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [c, s])
      (e₁ := .sub (.mul (.var 0) (.var 0)) (.mul (.neg (.var 1)) (.var 1)))
      (e₂ := .add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) rfl
    change c * c - (-s) * s = 1
    exact hr.trans hcs

theorem cayleyRot2_ne_one {t : F} (ht : t ≠ 0) : cayleyRot2 t ≠ Mat2.one F := by
  intro heq
  have h10 := congrArg Mat2.a10 heq
  dsimp [cayleyRot2, Mat2.one] at h10
  cases mul_eq_zeroF h10 with
  | inl hinv0 =>
    have hmul1 := FormallyRealField.mul_inv_cancel _ (one_add_sq_ne_zeroF t)
    rw [hinv0, cr_mul_zero] at hmul1
    exact one_ne_zeroF hmul1.symm
  | inr h2t =>
    cases mul_eq_zeroF h2t with
    | inl h2 => exact two_ne_zeroF h2
    | inr ht0 => exact ht ht0

/-- Positive natural parameters `t_n = n + 1` yield pairwise distinct rotation angles / traces
    `tr (cayleyRot2 (n + 1))`, yet EVERY ONE has exact minimal reflection count `2`! -/
theorem so2_infinite_distinct_angles_same_minReflCount :
    (∀ n : Nat,
      InSO2 (Q20 F) (cayleyRot2 (crOfNat F (n + 1))) ∧
      IsMinReflCount2 (Q20 F) (cayleyRot2 (crOfNat F (n + 1))) 2) ∧
    (∀ m n : Nat, m ≠ n →
      (cayleyRot2 (crOfNat F (m + 1))).tr ≠ (cayleyRot2 (crOfNat F (n + 1))).tr) := by
  refine ⟨?_, ?_⟩
  · intro n
    have hSO := cayleyRot2_inSO2 (crOfNat F (n + 1))
    have hne := cayleyRot2_ne_one (FormallyRealField.char_zero (F := F) n)
    exact ⟨hSO, so2_nonid_minReflCount_two hSO hne⟩
  · intro m n _ htr
    let tm := crOfNat F (m + 1)
    let tn := crOfNat F (n + 1)
    have hqm : 1 + tm * tm ≠ 0 := one_add_sq_ne_zeroF tm
    have hqn : 1 + tn * tn ≠ 0 := one_add_sq_ne_zeroF tn
    have hinvm : (1 + tm * tm) * (1 + tm * tm)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ hqm
    have hinvn : (1 + tn * tn) * (1 + tn * tn)⁻¹ = 1 := FormallyRealField.mul_inv_cancel _ hqn
    have hdiff :
        (1 + tm * tm) * (1 + tn * tn) * ((cayleyRot2 tm).tr - (cayleyRot2 tn).tr) =
          (twoF F * twoF F) * ((tn - tm) * (tn + tm)) := by
      have hr1 := RExpr.eq_of_norm_eq
        (envGet (0 : F) [1 + tm * tm, 1 + tn * tn, (cayleyRot2 tm).tr, (cayleyRot2 tn).tr])
        (e₁ := .mul (.mul (.var 0) (.var 1)) (.sub (.var 2) (.var 3)))
        (e₂ := .sub (.mul (.var 1) (.mul (.var 0) (.var 2)))
                    (.mul (.var 0) (.mul (.var 1) (.var 3)))) rfl
      have hm_tr : (1 + tm * tm) * (cayleyRot2 tm).tr = twoF F * (1 - tm * tm) := by
        have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [tm, (1 + tm * tm)⁻¹])
          (e₁ := .mul (.add .one (.mul (.var 0) (.var 0)))
                      (.add (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0))))
                            (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0))))))
          (e₂ := .mul (.mul (.add .one (.mul (.var 0) (.var 0))) (.var 1))
                      (.mul (.add .one .one) (.sub .one (.mul (.var 0) (.var 0))))) rfl
        dsimp only [RExpr.eval, envGet] at hr
        exact hr.trans (by rw [hinvm, CommRingOps.one_mul]; rfl)
      have hn_tr : (1 + tn * tn) * (cayleyRot2 tn).tr = twoF F * (1 - tn * tn) := by
        have hr := RExpr.eq_of_norm_eq (envGet (0 : F) [tn, (1 + tn * tn)⁻¹])
          (e₁ := .mul (.add .one (.mul (.var 0) (.var 0)))
                      (.add (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0))))
                            (.mul (.var 1) (.sub .one (.mul (.var 0) (.var 0))))))
          (e₂ := .mul (.mul (.add .one (.mul (.var 0) (.var 0))) (.var 1))
                      (.mul (.add .one .one) (.sub .one (.mul (.var 0) (.var 0))))) rfl
        dsimp only [RExpr.eval, envGet] at hr
        exact hr.trans (by rw [hinvn, CommRingOps.one_mul]; rfl)
      calc
        (1 + tm * tm) * (1 + tn * tn) * ((cayleyRot2 tm).tr - (cayleyRot2 tn).tr)
            = (1 + tn * tn) * ((1 + tm * tm) * (cayleyRot2 tm).tr) -
              (1 + tm * tm) * ((1 + tn * tn) * (cayleyRot2 tn).tr) := hr1
        _ = (1 + tn * tn) * (twoF F * (1 - tm * tm)) -
            (1 + tm * tm) * (twoF F * (1 - tn * tn)) := by rw [hm_tr, hn_tr]
        _ = (twoF F * twoF F) * ((tn - tm) * (tn + tm)) :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [tm, tn])
              (e₁ := .sub (.mul (.add .one (.mul (.var 1) (.var 1)))
                                (.mul (.add .one .one) (.sub .one (.mul (.var 0) (.var 0)))))
                          (.mul (.add .one (.mul (.var 0) (.var 0)))
                                (.mul (.add .one .one) (.sub .one (.mul (.var 1) (.var 1))))))
              (e₂ := .mul (.mul (.add .one .one) (.add .one .one))
                          (.mul (.sub (.var 1) (.var 0)) (.add (.var 1) (.var 0)))) rfl
    rw [htr, cr_sub_self, cr_mul_zero] at hdiff
    cases mul_eq_zeroF hdiff.symm with
    | inl h4 =>
      cases mul_eq_zeroF h4 with
      | inl h2 => exact two_ne_zeroF h2
      | inr h2 => exact two_ne_zeroF h2
    | inr hsq =>
      cases mul_eq_zeroF hsq with
      | inl hsub =>
        have heq : tn = tm := cr_eq_of_sub_eq_zero hsub
        have hnat : n + 1 = m + 1 := crOfNat_injF heq
        omega
      | inr hsum =>
        -- `tn + tm = crOfNat F ((n + 1) + (m + 1)) = 0` contradicts `char_zero`!
        have hnat0 : crOfNat F ((n + 1 + m) + 1) = 0 := by
          have hadd : crOfNat F ((n + 1) + (m + 1)) = tn + tm := crOfNat_add (n + 1) (m + 1)
          have hidx : (n + 1) + (m + 1) = (n + 1 + m) + 1 := by omega
          rw [← hidx, hadd]
          exact hsum
        exact FormallyRealField.char_zero (n + 1 + m) hnat0

/-! ## Refutation R3a: Lorentzian `SO(1, 1; F)` Disconnectedness vs Minimal Reflection Count `2` -/

theorem so11_entries {M : Mat2 F} (hM : InSO2 (Q11 F) M) :
    M.a00 = M.a11 ∧ M.a10 = M.a01 ∧ M.a00 * M.a00 - M.a01 * M.a01 = 1 := by
  obtain ⟨hO, hdet⟩ := hM
  have he0 := hO ⟨1, 0⟩
  have he11 := hO ⟨1, 1⟩
  have h0 : M.a00 * M.a00 - M.a10 * M.a10 = 1 := by
    calc
      M.a00 * M.a00 - M.a10 * M.a10 = (Q11 F).eval (M.mulVec ⟨1, 0⟩) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
          (e₁ := .sub (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))
          (e₂ := .add (.mul .one (.mul (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))
                                       (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))))
                      (.mul (.neg .one) (.mul (.add (.mul (.var 2) .one) (.mul (.var 3) .zero))
                                              (.add (.mul (.var 2) .one) (.mul (.var 3) .zero))))) rfl
      _ = (Q11 F).eval ⟨1, 0⟩ := he0
      _ = 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .one .one)) (.mul (.neg .one) (.mul .zero .zero)))
          (e₂ := .one) rfl
  have he1 := hO ⟨0, 1⟩
  have h1 : M.a01 * M.a01 - M.a11 * M.a11 = -(1 : F) := by
    calc
      M.a01 * M.a01 - M.a11 * M.a11 = (Q11 F).eval (M.mulVec ⟨0, 1⟩) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
          (e₁ := .sub (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3)))
          (e₂ := .add (.mul .one (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))
                                       (.add (.mul (.var 0) .zero) (.mul (.var 1) .one))))
                      (.mul (.neg .one) (.mul (.add (.mul (.var 2) .zero) (.mul (.var 3) .one))
                                              (.add (.mul (.var 2) .zero) (.mul (.var 3) .one))))) rfl
      _ = (Q11 F).eval ⟨0, 1⟩ := he1
      _ = -(1 : F) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul (.neg .one) (.mul .one .one)))
          (e₂ := .neg .one) rfl
  have hdot2 : twoF F * (M.a00 * M.a01 - M.a10 * M.a11) = 0 := by
    have hexp :
        (Q11 F).eval (M.mulVec ⟨1, 1⟩) -
          (M.a00 * M.a00 - M.a10 * M.a10) -
          (M.a01 * M.a01 - M.a11 * M.a11) =
          twoF F * (M.a00 * M.a01 - M.a10 * M.a11) :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
        (e₁ := .sub (.sub (.add (.mul .one (.mul (.add (.mul (.var 0) .one) (.mul (.var 1) .one))
                                                 (.add (.mul (.var 0) .one) (.mul (.var 1) .one))))
                                (.mul (.neg .one) (.mul (.add (.mul (.var 2) .one) (.mul (.var 3) .one))
                                                        (.add (.mul (.var 2) .one) (.mul (.var 3) .one)))))
                          (.sub (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))
                    (.sub (.mul (.var 1) (.var 1)) (.mul (.var 3) (.var 3))))
        (e₂ := .mul (.add .one .one)
                    (.sub (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))) rfl
    rw [← hexp, he11, h0, h1]
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .sub (.sub (.add (.mul .one (.mul .one .one)) (.mul (.neg .one) (.mul .one .one))) .one)
                  (.neg .one))
      (e₂ := .zero) rfl
  have hdot : M.a00 * M.a01 - M.a10 * M.a11 = 0 := by
    cases mul_eq_zeroF hdot2 with
    | inl h2 => exact False.elim (two_ne_zeroF h2)
    | inr hd => exact hd
  have ha00 : M.a11 - M.a00 = 0 := by
    calc
      M.a11 - M.a00
          = M.a00 * (M.det - 1) - M.a11 * ((M.a00 * M.a00 - M.a10 * M.a10) - 1) +
              M.a10 * (M.a00 * M.a01 - M.a10 * M.a11) :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
              (e₁ := .sub (.var 3) (.var 0))
              (e₂ := .add (.sub (.mul (.var 0) (.sub (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) .one))
                                (.mul (.var 3) (.sub (.sub (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) .one)))
                          (.mul (.var 2) (.sub (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))))) rfl
      _ = 0 := by
        rw [hdet, h0, hdot]
        simp only [cr_sub_self, cr_mul_zero, cr_add_zero]
  have ha10 : M.a01 - M.a10 = 0 := by
    calc
      M.a01 - M.a10
          = M.a10 * (M.det - 1) - M.a01 * ((M.a00 * M.a00 - M.a10 * M.a10) - 1) +
              M.a00 * (M.a00 * M.a01 - M.a10 * M.a11) :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [M.a00, M.a01, M.a10, M.a11])
              (e₁ := .sub (.var 1) (.var 2))
              (e₂ := .add (.sub (.mul (.var 2) (.sub (.sub (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) .one))
                                (.mul (.var 1) (.sub (.sub (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) .one)))
                          (.mul (.var 0) (.sub (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))))) rfl
      _ = 0 := by
        rw [hdet, h0, hdot]
        simp only [cr_sub_self, cr_mul_zero, cr_add_zero]
  have heq00 := (cr_eq_of_sub_eq_zero ha00).symm
  have heq10 := (cr_eq_of_sub_eq_zero ha10).symm
  refine ⟨heq00, heq10, ?_⟩
  rw [← heq10]; exact h0

theorem so11_comm {A B : Mat2 F} (hA : InSO2 (Q11 F) A) (hB : InSO2 (Q11 F) B) :
    Mat2.mul A B = Mat2.mul B A := by
  obtain ⟨hA0, hA1, _⟩ := so11_entries hA
  obtain ⟨hB0, hB1, _⟩ := so11_entries hB
  cases A with | mk a00 a01 a10 a11 =>
  cases B with | mk b00 b01 b10 b11 =>
  dsimp only at hA0 hA1 hB0 hB1
  rw [← hA0, hA1, ← hB0, hB1]
  dsimp only [Mat2.mul]
  let env := envGet (0 : F) [a00, a01, b00, b01]
  apply Mat2.ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (e₂ := .add (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
      (e₂ := .add (.mul (.var 2) (.var 1)) (.mul (.var 3) (.var 0))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
      (e₂ := .add (.mul (.var 3) (.var 0)) (.mul (.var 2) (.var 1))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2)))
      (e₂ := .add (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 0))) rfl

/-- The subgroup of `SO(1, 1; F)` generated by squares `M^2` (the algebraic divisible /
    identity-component subgroup `SO^+(1, 1; F)`, which over `ℝ` equals `{exp(t X) | t ∈ ℝ}`). -/
inductive InSqGenSO11 (F : Type) [FormallyRealField F] : Mat2 F → Prop where
  | one : InSqGenSO11 F (Mat2.one F)
  | sq {M : Mat2 F} : InSO2 (Q11 F) M → InSqGenSO11 F (Mat2.mul M M)
  | mul {A B : Mat2 F} : InSqGenSO11 F A → InSqGenSO11 F B → InSqGenSO11 F (Mat2.mul A B)

theorem inSqGenSO11_is_square {G : Mat2 F} (hG : InSqGenSO11 F G) :
    ∃ M : Mat2 F, InSO2 (Q11 F) M ∧ G = Mat2.mul M M := by
  induction hG with
  | one =>
    exact ⟨Mat2.one F, inSO2_one (Q11 F), (Mat2.one_mul (Mat2.one F)).symm⟩
  | sq hM =>
    exact ⟨_, hM, rfl⟩
  | mul _ _ ihA ihB =>
    obtain ⟨M₁, hM₁, rfl⟩ := ihA
    obtain ⟨M₂, hM₂, rfl⟩ := ihB
    refine ⟨Mat2.mul M₁ M₂, inSO2_mul hM₁ hM₂, ?_⟩
    calc
      Mat2.mul (Mat2.mul M₁ M₁) (Mat2.mul M₂ M₂)
          = Mat2.mul M₁ (Mat2.mul M₁ (Mat2.mul M₂ M₂)) := Mat2.mul_assoc _ _ _
      _ = Mat2.mul M₁ (Mat2.mul (Mat2.mul M₁ M₂) M₂) := by rw [← Mat2.mul_assoc M₁ M₂ M₂]
      _ = Mat2.mul M₁ (Mat2.mul (Mat2.mul M₂ M₁) M₂) := by rw [so11_comm hM₁ hM₂]
      _ = Mat2.mul M₁ (Mat2.mul M₂ (Mat2.mul M₁ M₂)) := by rw [Mat2.mul_assoc M₂ M₁ M₂]
      _ = Mat2.mul (Mat2.mul M₁ M₂) (Mat2.mul M₁ M₂) := (Mat2.mul_assoc _ _ _).symm

/-- **Refutation R3a (Lorentzian `SO(1, 1; F)` Disconnectedness):**
    `-I_2 ∈ SO(1, 1; F)` has exact minimal reflection count `2` (`-I_2 = r_{e_1} * r_{e_2}`),
    yet `-I_2 ∉ InSqGenSO11 F` — no geodesic / divisible subgroup element reaches `-I_2`! -/
theorem lorentz_negOne_minRefl_two_yet_not_geodesic :
    InSO2 (Q11 F) (Mat2.negOne F) ∧
    IsMinReflCount2 (Q11 F) (Mat2.negOne F) 2 ∧
    ¬ InSqGenSO11 F (Mat2.negOne F) := by
  have he0 : (Q11 F).eval ⟨1, 0⟩ ≠ 0 := by
    have hq : (Q11 F).eval ⟨1, 0⟩ = 1 :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul .one (.mul .one .one)) (.mul (.neg .one) (.mul .zero .zero)))
        (e₂ := .one) rfl
    rw [hq]; exact one_ne_zeroF
  have he1 : (Q11 F).eval ⟨0, 1⟩ ≠ 0 := by
    have hq : (Q11 F).eval ⟨0, 1⟩ = -(1 : F) :=
      RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul (.neg .one) (.mul .one .one)))
        (e₂ := .neg .one) rfl
    rw [hq]
    intro h0
    have h10 : (1 : F) = 0 := by rw [← cr_neg_neg (1 : F), h0, cr_neg_zero]
    exact one_ne_zeroF h10
  have hprod : Mat2.mul (refl2 (Q11 F) ⟨1, 0⟩) (refl2 (Q11 F) ⟨0, 1⟩) = Mat2.negOne F := by
    have hi0 : ((Q11 F).eval ⟨1, 0⟩)⁻¹ = 1 := by
      have hq : (Q11 F).eval ⟨1, 0⟩ = 1 :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .one .one)) (.mul (.neg .one) (.mul .zero .zero)))
          (e₂ := .one) rfl
      rw [hq]
      have h1 := FormallyRealField.mul_inv_cancel (1 : F) one_ne_zeroF
      rw [CommRingOps.one_mul] at h1; exact h1
    have hi1 : ((Q11 F).eval ⟨0, 1⟩)⁻¹ = -(1 : F) := by
      have hq : (Q11 F).eval ⟨0, 1⟩ = -(1 : F) :=
        RExpr.eq_of_norm_eq (envGet (0 : F) [])
          (e₁ := .add (.mul .one (.mul .zero .zero)) (.mul (.neg .one) (.mul .one .one)))
          (e₂ := .neg .one) rfl
      rw [hq]
      have hm1 := FormallyRealField.mul_inv_cancel (-(1 : F)) (by
        intro h0
        have h10 : (1 : F) = 0 := by rw [← cr_neg_neg (1 : F), h0, cr_neg_zero]
        exact one_ne_zeroF h10)
      calc
        (-(1 : F))⁻¹ = 1 * (-(1 : F))⁻¹ := (CommRingOps.one_mul _).symm
        _ = ((-(1 : F)) * (-(1 : F))) * (-(1 : F))⁻¹ := by
          have hsq1 : (-(1 : F)) * (-(1 : F)) = 1 :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [])
              (e₁ := .mul (.neg .one) (.neg .one)) (e₂ := .one) rfl
          rw [hsq1]
        _ = (-(1 : F)) * ((-(1 : F)) * (-(1 : F))⁻¹) := CommRingOps.mul_assoc _ _ _
        _ = -(1 : F) := by rw [hm1, cr_mul_one]
    apply Mat2.ext
    · unfold refl2 Mat2.mul Mat2.negOne; dsimp only; rw [hi0, hi1]
      exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul (.sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .one))
                          (.sub .one (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) .one) .zero)) .zero)))
                    (.mul (.neg (.mul (.mul .one (.mul (.mul (.add .one .one) (.neg .one)) .zero)) .one))
                          (.neg (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) .one) .zero)) .one))))
        (e₂ := .neg .one) rfl
    · unfold refl2 Mat2.mul Mat2.negOne; dsimp only; rw [hi0, hi1]
      exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul (.sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .one))
                          (.neg (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) (.neg .one)) .one)) .zero)))
                    (.mul (.neg (.mul (.mul .one (.mul (.mul (.add .one .one) (.neg .one)) .zero)) .one))
                          (.sub .one (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) (.neg .one)) .one)) .one))))
        (e₂ := .zero) rfl
    · unfold refl2 Mat2.mul Mat2.negOne; dsimp only; rw [hi0, hi1]
      exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul (.neg (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .zero))
                          (.sub .one (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) .one) .zero)) .zero)))
                    (.mul (.sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) (.neg .one)) .zero)) .zero))
                          (.neg (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) .one) .zero)) .one))))
        (e₂ := .zero) rfl
    · unfold refl2 Mat2.mul Mat2.negOne; dsimp only; rw [hi0, hi1]
      exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
        (e₁ := .add (.mul (.neg (.mul (.mul .one (.mul (.mul (.add .one .one) .one) .one)) .zero))
                          (.neg (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) (.neg .one)) .one)) .zero)))
                    (.mul (.sub .one (.mul (.mul .one (.mul (.mul (.add .one .one) (.neg .one)) .zero)) .zero))
                          (.sub .one (.mul (.mul (.neg .one) (.mul (.mul (.add .one .one) (.neg .one)) .one)) .one))))
        (e₂ := .neg .one) rfl
  have hSO : InSO2 (Q11 F) (Mat2.negOne F) := by
    refine ⟨?_, Mat2.det_negOne⟩
    rw [← hprod]
    exact isOrth2_mul (refl2_isOrth (Q11 F) he0) (refl2_isOrth (Q11 F) he1)
  have hhas2 : HasReflCount2 (Q11 F) (Mat2.negOne F) 2 := by
    refine ⟨[refl2 (Q11 F) ⟨1, 0⟩, refl2 (Q11 F) ⟨0, 1⟩], rfl, ?_, ?_⟩
    · intro r hm
      cases hm with
      | head => exact ⟨⟨1, 0⟩, he0, rfl⟩
      | tail _ hm2 =>
        cases hm2 with
        | head => exact ⟨⟨0, 1⟩, he1, rfl⟩
        | tail _ hn => nomatch hn
    · change Mat2.mul (refl2 (Q11 F) ⟨1, 0⟩) (Mat2.mul (refl2 (Q11 F) ⟨0, 1⟩) (Mat2.one F)) = _
      rw [Mat2.mul_one]
      exact hprod
  have hne1 : Mat2.negOne F ≠ Mat2.one F := by
    intro heq
    exact neg_one_ne_oneF (congrArg Mat2.a00 heq)
  refine ⟨hSO, ⟨hhas2, ?_⟩, ?_⟩
  · intro m hm hc
    obtain ⟨rs, hlen, hd⟩ := hc
    cases rs with
    | nil => exact hne1 hd.2.symm
    | cons r₁ rest =>
      cases rest with
      | nil =>
        have hpar := (reflCount2_parity_iff ⟨[r₁], rfl, hd⟩).1
        have hm0 : (1 : Nat) % 2 = 0 := hpar.mp hSO.2
        omega
      | cons _ _ => simp at hlen; omega
  · intro hsq
    obtain ⟨M, hM, heq⟩ := inSqGenSO11_is_square hsq
    obtain ⟨_, h10, _⟩ := so11_entries hM
    have h00 := congrArg Mat2.a00 heq
    dsimp [Mat2.mul, Mat2.negOne] at h00
    rw [h10] at h00
    have h4 : M.a00 * M.a00 + M.a01 * M.a01 + (1 : F) * 1 + 0 * 0 = 0 := by
      calc
        M.a00 * M.a00 + M.a01 * M.a01 + (1 : F) * 1 + 0 * 0
            = (-(1 : F)) + (1 : F) * 1 + 0 * 0 := by rw [← h00]
        _ = 0 :=
          RExpr.eq_of_norm_eq (envGet (0 : F) [])
            (e₁ := .add (.add (.neg .one) (.mul .one .one)) (.mul .zero .zero))
            (e₂ := .zero) rfl
    exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero M.a00 M.a01 1 0 h4).2.2.1

end PlanarTheory

end Conjecture00000007609
