/-
  Conjecture 00000007628 — Split & Euclidean 2D Clifford Algebras (`Cl_{1,1}(K)`, `Cl_{2,0}(K)`),
  Positive Non-Vacuity Theorem, and Minimal Two-Sided Ideal Simplicity Refutation.
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007628.Field

namespace Conjecture00000007628

open CommField

/-- 2-component column vector over `K` (models minimal left ideal `S₁ = M₂(K) E₁₁ ≅ K²`). -/
structure Vec2 (K : Type) where
  x : K
  y : K
  deriving DecidableEq, Repr

/-- `2 × 2` matrix over `K` (models `Cl_{1,1}(K) ≅ M₂(K)` and `Cl_{2,0}(K) ≅ M₂(K)`). -/
structure Mat2 (K : Type) where
  a11 : K
  a12 : K
  a21 : K
  a22 : K
  deriving DecidableEq, Repr

namespace Vec2

@[ext]
theorem ext {K : Type} {u v : Vec2 K} (hx : u.x = v.x) (hy : u.y = v.y) : u = v := by
  cases u; cases v; simp only at hx hy; subst hx; subst hy; rfl

section VecOps
variable {K : Type} [CommField K]

def zero : Vec2 K := ⟨0, 0⟩
def e1 : Vec2 K := ⟨1, 0⟩
def e2 : Vec2 K := ⟨0, 1⟩
def add (u v : Vec2 K) : Vec2 K := ⟨u.x + v.x, u.y + v.y⟩
def neg (u : Vec2 K) : Vec2 K := ⟨-u.x, -u.y⟩
def smul (c : K) (u : Vec2 K) : Vec2 K := ⟨c * u.x, c * u.y⟩

/-- Basis decomposition `u = u.x • e₁ + u.y • e₂` witnessing `dim_K(Vec2 K) = 2`. -/
theorem basis_decomp (u : Vec2 K) : add (smul u.x e1) (smul u.y e2) = u := by
  ext <;> simp [add, smul, e1, e2, mul_one, mul_zero, add_zero, zero_add]

theorem basis_unique {c1 c2 : K} (h : add (smul c1 e1) (smul c2 e2) = zero) :
    c1 = 0 ∧ c2 = 0 := by
  have hx : (add (smul c1 e1) (smul c2 e2)).x = (0 : K) := congrArg Vec2.x h
  have hy : (add (smul c1 e1) (smul c2 e2)).y = (0 : K) := congrArg Vec2.y h
  simp only [add, smul, e1, e2, mul_one, mul_zero, add_zero, zero_add] at hx hy
  exact ⟨hx, hy⟩

end VecOps
end Vec2

namespace Mat2

@[ext]
theorem ext {K : Type} {A B : Mat2 K}
    (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12)
    (h21 : A.a21 = B.a21) (h22 : A.a22 = B.a22) : A = B := by
  cases A; cases B
  simp only at h11 h12 h21 h22
  subst h11; subst h12; subst h21; subst h22; rfl

section MatOps
variable {K : Type} [CommField K]

def zero : Mat2 K := ⟨0, 0, 0, 0⟩
def I2   : Mat2 K := ⟨1, 0, 0, 1⟩
def negI2 : Mat2 K := ⟨-1, 0, 0, -1⟩

def E11 : Mat2 K := ⟨1, 0, 0, 0⟩
def E12 : Mat2 K := ⟨0, 1, 0, 0⟩
def E21 : Mat2 K := ⟨0, 0, 1, 0⟩
def E22 : Mat2 K := ⟨0, 0, 0, 1⟩

def add (A B : Mat2 K) : Mat2 K :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩

def neg (A : Mat2 K) : Mat2 K :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

def sub (A B : Mat2 K) : Mat2 K :=
  ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩

def smul (c : K) (A : Mat2 K) : Mat2 K :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩

def mul (A B : Mat2 K) : Mat2 K :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

def tr (A : Mat2 K) : Mat2 K :=
  ⟨A.a11, A.a21, A.a12, A.a22⟩

/-- Adjugate / Clifford conjugation on `Cl_{1,1}(K) ≅ M₂(K)`: `X ↦ J⁻¹ Xᵀ J`. -/
def cliffConj (A : Mat2 K) : Mat2 K :=
  ⟨A.a22, -A.a12, -A.a21, A.a11⟩

def det (A : Mat2 K) : K :=
  A.a11 * A.a22 - A.a12 * A.a21

def act (A : Mat2 K) (u : Vec2 K) : Vec2 K :=
  ⟨A.a11 * u.x + A.a12 * u.y, A.a21 * u.x + A.a22 * u.y⟩

theorem mul_I2 (A : Mat2 K) : mul A I2 = A := by
  ext <;> simp [mul, I2, mul_one, mul_zero, add_zero, zero_add]

theorem I2_mul (A : Mat2 K) : mul I2 A = A := by
  ext <;> simp [mul, I2, one_mul, zero_mul, add_zero, zero_add]

theorem act_I2 (u : Vec2 K) : act I2 u = u := by
  apply Vec2.ext <;> simp [act, I2, one_mul, zero_mul, add_zero, zero_add]

theorem eq_of_act_basis {A B : Mat2 K}
    (h1 : act A Vec2.e1 = act B Vec2.e1)
    (h2 : act A Vec2.e2 = act B Vec2.e2) : A = B := by
  have h1x := congrArg Vec2.x h1
  have h1y := congrArg Vec2.y h1
  have h2x := congrArg Vec2.x h2
  have h2y := congrArg Vec2.y h2
  simp only [act, Vec2.e1, Vec2.e2, mul_one, mul_zero, add_zero, zero_add] at h1x h1y h2x h2y
  exact ext h1x h2x h1y h2y

theorem act_mul (A B : Mat2 K) (u : Vec2 K) : act (mul A B) u = act A (act B u) := by
  apply Vec2.ext
  · unfold act mul
    calc
      (A.a11 * B.a11 + A.a12 * B.a21) * u.x + (A.a11 * B.a12 + A.a12 * B.a22) * u.y
        = ((A.a11 * B.a11) * u.x + (A.a12 * B.a21) * u.x) +
          ((A.a11 * B.a12) * u.y + (A.a12 * B.a22) * u.y) := by
            rw [right_distrib, right_distrib]
      _ = ((A.a11 * B.a11) * u.x + (A.a11 * B.a12) * u.y) +
          ((A.a12 * B.a21) * u.x + (A.a12 * B.a22) * u.y) := by
            rw [add_assoc, ← add_assoc ((A.a12 * B.a21) * u.x),
                add_comm ((A.a12 * B.a21) * u.x) ((A.a11 * B.a12) * u.y),
                add_assoc, ← add_assoc]
      _ = A.a11 * (B.a11 * u.x + B.a12 * u.y) + A.a12 * (B.a21 * u.x + B.a22 * u.y) := by
            rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← left_distrib, ← left_distrib]
  · unfold act mul
    calc
      (A.a21 * B.a11 + A.a22 * B.a21) * u.x + (A.a21 * B.a12 + A.a22 * B.a22) * u.y
        = ((A.a21 * B.a11) * u.x + (A.a22 * B.a21) * u.x) +
          ((A.a21 * B.a12) * u.y + (A.a22 * B.a22) * u.y) := by
            rw [right_distrib, right_distrib]
      _ = ((A.a21 * B.a11) * u.x + (A.a21 * B.a12) * u.y) +
          ((A.a22 * B.a21) * u.x + (A.a22 * B.a22) * u.y) := by
            rw [add_assoc, ← add_assoc ((A.a22 * B.a21) * u.x),
                add_comm ((A.a22 * B.a21) * u.x) ((A.a21 * B.a12) * u.y),
                add_assoc, ← add_assoc]
      _ = A.a21 * (B.a11 * u.x + B.a12 * u.y) + A.a22 * (B.a21 * u.x + B.a22 * u.y) := by
            rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← left_distrib, ← left_distrib]

theorem mul_assoc (A B C : Mat2 K) : mul (mul A B) C = mul A (mul B C) := by
  apply eq_of_act_basis <;> simp only [act_mul]

/-! ### Split Clifford Algebra `Cl_{1,1}(K) ≅ M₂(K)` (`Q(x, y) = x² - y²`) -/

/-- First Clifford generator `γ₁` with `γ₁² = +I₂`. -/
def cl11_g1 : Mat2 K := ⟨1, 0, 0, -1⟩

/-- Second Clifford generator `γ₂` with `γ₂² = -I₂` and `γ₁ γ₂ + γ₂ γ₁ = 0`. -/
def cl11_g2 : Mat2 K := ⟨0, 1, -1, 0⟩

/-- Bivector `γ₁₂ = γ₁ γ₂`. -/
def cl11_g12 : Mat2 K := mul cl11_g1 cl11_g2

theorem cl11_relations :
    mul cl11_g1 (cl11_g1 (K := K)) = I2 ∧
    mul cl11_g2 (cl11_g2 (K := K)) = neg I2 ∧
    add (mul cl11_g1 (cl11_g2 (K := K))) (mul cl11_g2 cl11_g1) = zero := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [mul, cl11_g1, I2, one_mul, mul_one, zero_mul, mul_zero,
      neg_mul_neg, add_zero, zero_add]
  · ext <;> simp [mul, cl11_g2, neg, I2, zero_mul, mul_zero, one_mul, mul_one,
      neg_one_mul, mul_neg, add_zero, zero_add, neg_zero]
  · ext <;> simp [add, mul, cl11_g1, cl11_g2, zero, one_mul, mul_one, zero_mul, mul_zero,
      neg_one_mul, mul_neg, add_zero, zero_add, add_neg_cancel, neg_add_cancel]

/-- Standard matrix units give a 4-element `K`-basis of `M₂(K) ≅ Cl_{1,1}(K)` (`dim_K = 4 = 2²`). -/
theorem mat2_basis_decomp (A : Mat2 K) :
    add (add (smul A.a11 E11) (smul A.a12 E12))
        (add (smul A.a21 E21) (smul A.a22 E22)) = A := by
  ext <;> simp [add, smul, E11, E12, E21, E22, mul_one, mul_zero, add_zero, zero_add]

theorem mat2_basis_unique {c11 c12 c21 c22 : K}
    (h : add (add (smul c11 E11) (smul c12 E12))
             (add (smul c21 E21) (smul c22 E22)) = zero) :
    c11 = 0 ∧ c12 = 0 ∧ c21 = 0 ∧ c22 = 0 := by
  have h11 := congrArg Mat2.a11 h
  have h12 := congrArg Mat2.a12 h
  have h21 := congrArg Mat2.a21 h
  have h22 := congrArg Mat2.a22 h
  simp only [add, smul, E11, E12, E21, E22, zero, mul_one, mul_zero, add_zero, zero_add]
    at h11 h12 h21 h22
  exact ⟨h11, h12, h21, h22⟩

/-- When `char(K) ≠ 2`, `E₁₁ = ½(I₂ + γ₁)` and `E₂₂ = ½(I₂ - γ₁)` are orthogonal primitive
    idempotents generated directly inside `Cl_{1,1}(K)`. -/
theorem cl11_idempotents (hchar : (1 : K) + 1 ≠ 0) :
    smul (half K) (add I2 cl11_g1) = (E11 (K := K)) ∧
    smul (half K) (sub I2 cl11_g1) = (E22 (K := K)) ∧
    mul (E11 (K := K)) E11 = E11 ∧
    mul (E22 (K := K)) E22 = E22 ∧
    mul (E11 (K := K)) E22 = zero ∧
    mul (E22 (K := K)) E11 = zero ∧
    add (E11 (K := K)) E22 = I2 := by
  have htwo : half K * ((1 : K) + 1) = 1 := half_mul_two hchar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [smul, add, I2, cl11_g1, E11, add_zero, add_neg_cancel, mul_zero, htwo]
  · ext
    · simp [smul, sub, I2, cl11_g1, E22, sub_self, mul_zero]
    · simp [smul, sub, I2, cl11_g1, E22, sub_self, mul_zero]
    · simp [smul, sub, I2, cl11_g1, E22, sub_self, mul_zero]
    · simp [smul, sub, I2, cl11_g1, E22, sub_eq_add_neg, neg_neg, htwo]
  · ext <;> simp [mul, E11, one_mul, zero_mul, add_zero]
  · ext <;> simp [mul, E22, one_mul, zero_mul, zero_add, add_zero]
  · ext <;> simp [mul, E11, E22, zero, mul_zero, zero_mul, add_zero]
  · ext <;> simp [mul, E22, E11, zero, mul_zero, zero_mul, add_zero]
  · ext <;> simp [add, E11, E22, I2, add_zero, zero_add]

/-! ### Minimal Left Ideals `S₁ = M₂(K) E₁₁`, `S₂ = M₂(K) E₂₂` and Semisimple Decomposition -/

/-- Membership predicate for `S₁ = M₂(K) E₁₁` (first column matrices, `dim_K S₁ = 2`). -/
def inS1 (A : Mat2 K) : Prop := A.a12 = 0 ∧ A.a22 = 0

/-- Membership predicate for `S₂ = M₂(K) E₂₂` (second column matrices, `dim_K S₂ = 2`). -/
def inS2 (A : Mat2 K) : Prop := A.a11 = 0 ∧ A.a21 = 0

/-- Embedding `Vec2 K → Mat2 K` identifying `K²` with `S₁ = M₂(K) E₁₁`. -/
def embedS1 (u : Vec2 K) : Mat2 K := ⟨u.x, 0, u.y, 0⟩

theorem embedS1_inS1 (u : Vec2 K) : inS1 (embedS1 u) := ⟨rfl, rfl⟩

theorem embedS1_left_action (X : Mat2 K) (u : Vec2 K) :
    mul X (embedS1 u) = embedS1 (act X u) := by
  ext <;> simp [mul, embedS1, act, mul_zero, add_zero]

/-- Exact Wedderburn–Artin semisimple decomposition `Cl_{1,1}(K) = S₁ ⊕ S₂`. -/
theorem cl11_semisimple_decomposition (X : Mat2 K) :
    inS1 (mul X E11) ∧
    inS2 (mul X E22) ∧
    add (mul X E11) (mul X E22) = X ∧
    (∀ Y Z : Mat2 K, inS1 Y → inS2 Z → add Y Z = zero → Y = zero ∧ Z = zero) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [inS1, mul, E11, mul_zero, add_zero]
  · simp [inS2, mul, E22, mul_zero, add_zero]
  · ext <;> simp [add, mul, E11, E22, mul_one, mul_zero, add_zero, zero_add]
  · intro Y Z hY hZ hsum
    rcases hY with ⟨hy12, hy22⟩
    rcases hZ with ⟨hz11, hz21⟩
    have h11 := congrArg Mat2.a11 hsum
    have h12 := congrArg Mat2.a12 hsum
    have h21 := congrArg Mat2.a21 hsum
    have h22 := congrArg Mat2.a22 hsum
    simp only [add, zero] at h11 h12 h21 h22
    rw [hz11, add_zero] at h11
    rw [hy12, zero_add] at h12
    rw [hz21, add_zero] at h21
    rw [hy22, zero_add] at h22
    exact ⟨ext h11 hy12 h21 hy22, ext hz11 h12 hz21 h22⟩

/-- Minimality of `S₁`: for every nonzero `u ∈ S₁` and target `w ∈ S₁`, some `X ∈ Cl_{1,1}(K)`
    satisfies `X u = w` (`S₁` is a simple left `Cl_{1,1}(K)`-module / minimal nonzero left ideal). -/
theorem S1_is_minimal_left_ideal {u : Vec2 K} (hu : u ≠ Vec2.zero) (w : Vec2 K) :
    ∃ X : Mat2 K, act X u = w := by
  by_cases hux : u.x ≠ 0
  · refine ⟨⟨w.x * inv u.x, 0, w.y * inv u.x, 0⟩, ?_⟩
    apply Vec2.ext
    · simp only [act, zero_mul, add_zero]
      rw [CommField.mul_assoc, inv_mul_cancel hux, mul_one]
    · simp only [act, zero_mul, add_zero]
      rw [CommField.mul_assoc, inv_mul_cancel hux, mul_one]
  · have hux0 : u.x = 0 := by
      by_cases h : u.x = 0
      · exact h
      · exact absurd h hux
    have huy : u.y ≠ 0 := by
      intro huy0
      exact hu (Vec2.ext hux0 huy0)
    refine ⟨⟨0, w.x * inv u.y, 0, w.y * inv u.y⟩, ?_⟩
    apply Vec2.ext
    · simp only [act, zero_mul, zero_add]
      rw [CommField.mul_assoc, inv_mul_cancel huy, mul_one]
    · simp only [act, zero_mul, zero_add]
      rw [CommField.mul_assoc, inv_mul_cancel huy, mul_one]

/-! ### Canonical Symplectic Spinor Form on `S₁` (Positive Non-Vacuity Theorem) -/

/-- Canonical alternating spinor bilinear form `ω(u, v) = u.x * v.y - u.y * v.x` on `S₁ ≅ K²`. -/
def omega (u v : Vec2 K) : K := u.x * v.y - u.y * v.x

theorem omega_alternating (u : Vec2 K) : omega u u = 0 := by
  unfold omega
  rw [mul_comm u.y u.x, sub_self]

theorem omega_nondegenerate {u : Vec2 K} (h : ∀ v : Vec2 K, omega u v = 0) : u = Vec2.zero := by
  have h1 := h Vec2.e2
  have h2 := h Vec2.e1
  unfold omega Vec2.e2 at h1
  unfold omega Vec2.e1 at h2
  simp only [mul_one, mul_zero, sub_zero, zero_sub] at h1 h2
  have huy : u.y = 0 := by
    rw [← neg_neg u.y, h2, neg_zero]
  exact Vec2.ext h1 huy

/-- Clifford conjugation negates the generating vectors `γ₁, γ₂` of `Cl_{1,1}(K)`. -/
theorem cliffConj_generators :
    cliffConj (I2 (K := K)) = I2 ∧
    cliffConj (cl11_g1 (K := K)) = neg cl11_g1 ∧
    cliffConj (cl11_g2 (K := K)) = neg cl11_g2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [cliffConj, I2, neg_zero]
  · ext <;> simp [cliffConj, cl11_g1, neg, neg_zero, neg_neg]
  · ext <;> simp [cliffConj, cl11_g2, neg, neg_zero, neg_neg]

/-- Canonical Lounesto/Chevalley spinor pairing covariance:
    `ω(X u, v) = ω(u, cliffConj(X) v)` for all `X ∈ Cl_{1,1}(K)` and spinors `u, v ∈ S₁`. -/
theorem omega_clifford_covariant (X : Mat2 K) (u v : Vec2 K) :
    omega (act X u) v = omega u (act (cliffConj X) v) := by
  unfold omega act cliffConj
  calc
    (X.a11 * u.x + X.a12 * u.y) * v.y - (X.a21 * u.x + X.a22 * u.y) * v.x
      = ((X.a11 * u.x) * v.y + (X.a12 * u.y) * v.y) -
        ((X.a21 * u.x) * v.x + (X.a22 * u.y) * v.x) := by
          rw [right_distrib, right_distrib]
    _ = ((X.a11 * u.x) * v.y + (X.a12 * u.y) * v.y) +
        (-((X.a21 * u.x) * v.x) + -((X.a22 * u.y) * v.x)) := by
          rw [sub_eq_add_neg, neg_add]
    _ = ((X.a11 * u.x) * v.y + -((X.a21 * u.x) * v.x)) +
        ((X.a12 * u.y) * v.y + -((X.a22 * u.y) * v.x)) := by
          rw [add_assoc, ← add_assoc ((X.a12 * u.y) * v.y),
              add_comm ((X.a12 * u.y) * v.y) (-((X.a21 * u.x) * v.x)),
              add_assoc, ← add_assoc]
    _ = (u.x * ((-X.a21) * v.x) + u.x * (X.a11 * v.y)) +
        (-(u.y * (X.a22 * v.x)) + -(-(u.y * (X.a12 * v.y)))) := by
          have t1 : (X.a11 * u.x) * v.y = u.x * (X.a11 * v.y) := by
            rw [mul_comm X.a11 u.x, CommField.mul_assoc]
          have t2 : -((X.a21 * u.x) * v.x) = u.x * ((-X.a21) * v.x) := by
            rw [mul_comm X.a21 u.x, CommField.mul_assoc, ← mul_neg, ← neg_mul]
          have t3 : (X.a12 * u.y) * v.y = -(-(u.y * (X.a12 * v.y))) := by
            rw [neg_neg, mul_comm X.a12 u.y, CommField.mul_assoc]
          have t4 : -((X.a22 * u.y) * v.x) = -(u.y * (X.a22 * v.x)) := by
            rw [mul_comm X.a22 u.y, CommField.mul_assoc]
          rw [t1, t2, t3, t4, add_comm (u.x * (X.a11 * v.y)),
              add_comm (-(u.y * (X.a22 * v.x)))]
    _ = u.x * ((-X.a21) * v.x + X.a11 * v.y) -
        u.y * (X.a22 * v.x + (-X.a12) * v.y) := by
          have t5 : u.y * ((-X.a12) * v.y) = -(u.y * (X.a12 * v.y)) := by
            rw [neg_mul, mul_neg]
          rw [← left_distrib, ← neg_add, ← t5, ← left_distrib, ← sub_eq_add_neg]

/-- Adjugate-action identity `cliffConj(g) * (g v) = det(g) • v`. -/
theorem act_cliffConj_act (g : Mat2 K) (v : Vec2 K) :
    act (cliffConj g) (act g v) = Vec2.smul (det g) v := by
  apply Vec2.ext
  · unfold act cliffConj det Vec2.smul
    calc
      g.a22 * (g.a11 * v.x + g.a12 * v.y) + (-g.a12) * (g.a21 * v.x + g.a22 * v.y)
        = (g.a22 * (g.a11 * v.x) + g.a22 * (g.a12 * v.y)) +
          ((-g.a12) * (g.a21 * v.x) + (-g.a12) * (g.a22 * v.y)) := by
            rw [left_distrib, left_distrib]
      _ = (g.a22 * (g.a11 * v.x) + (-g.a12) * (g.a21 * v.x)) +
          (g.a22 * (g.a12 * v.y) + (-g.a12) * (g.a22 * v.y)) := by
            rw [add_assoc, ← add_assoc (g.a22 * (g.a12 * v.y)),
                add_comm (g.a22 * (g.a12 * v.y)) ((-g.a12) * (g.a21 * v.x)),
                add_assoc, ← add_assoc]
      _ = (g.a11 * g.a22 - g.a12 * g.a21) * v.x + 0 := by
            have p1 : g.a22 * (g.a11 * v.x) = (g.a11 * g.a22) * v.x := by
              rw [← CommField.mul_assoc, mul_comm g.a22 g.a11]
            have p2 : (-g.a12) * (g.a21 * v.x) = -((g.a12 * g.a21) * v.x) := by
              rw [neg_mul, ← CommField.mul_assoc]
            have p3 : (-g.a12) * (g.a22 * v.y) = -(g.a22 * (g.a12 * v.y)) := by
              rw [neg_mul, ← CommField.mul_assoc, mul_comm g.a12 g.a22, CommField.mul_assoc]
            rw [p1, p2, ← sub_eq_add_neg, ← sub_mul, p3, add_neg_cancel]
      _ = (g.a11 * g.a22 - g.a12 * g.a21) * v.x := add_zero _
  · unfold act cliffConj det Vec2.smul
    calc
      (-g.a21) * (g.a11 * v.x + g.a12 * v.y) + g.a11 * (g.a21 * v.x + g.a22 * v.y)
        = ((-g.a21) * (g.a11 * v.x) + (-g.a21) * (g.a12 * v.y)) +
          (g.a11 * (g.a21 * v.x) + g.a11 * (g.a22 * v.y)) := by
            rw [left_distrib, left_distrib]
      _ = ((-g.a21) * (g.a11 * v.x) + g.a11 * (g.a21 * v.x)) +
          (g.a11 * (g.a22 * v.y) + (-g.a21) * (g.a12 * v.y)) := by
            rw [add_assoc, ← add_assoc ((-g.a21) * (g.a12 * v.y)),
                add_comm ((-g.a21) * (g.a12 * v.y)),
                add_assoc, ← add_assoc,
                add_comm ((-g.a21) * (g.a12 * v.y)) (g.a11 * (g.a22 * v.y))]
      _ = 0 + (g.a11 * g.a22 - g.a12 * g.a21) * v.y := by
            have q1 : (-g.a21) * (g.a11 * v.x) = -(g.a11 * (g.a21 * v.x)) := by
              rw [neg_mul, ← CommField.mul_assoc, mul_comm g.a21 g.a11, CommField.mul_assoc]
            have q2 : g.a11 * (g.a22 * v.y) = (g.a11 * g.a22) * v.y :=
              (CommField.mul_assoc _ _ _).symm
            have q3 : (-g.a21) * (g.a12 * v.y) = -((g.a12 * g.a21) * v.y) := by
              rw [neg_mul, ← CommField.mul_assoc, mul_comm g.a21 g.a12]
            rw [q1, neg_add_cancel, q2, q3, ← sub_eq_add_neg, ← sub_mul]
      _ = (g.a11 * g.a22 - g.a12 * g.a21) * v.y := zero_add _

/-- Fundamental symplectic determinant identity: `ω(g u, g v) = det(g) * ω(u, v)`. -/
theorem omega_act_eq_det_mul (g : Mat2 K) (u v : Vec2 K) :
    omega (act g u) (act g v) = det g * omega u v := by
  rw [omega_clifford_covariant, act_cliffConj_act]
  unfold omega Vec2.smul
  have t1 : u.x * (det g * v.y) = det g * (u.x * v.y) := by
    rw [← CommField.mul_assoc u.x (det g) v.y, mul_comm u.x (det g),
        CommField.mul_assoc (det g) u.x v.y]
  have t2 : u.y * (det g * v.x) = det g * (u.y * v.x) := by
    rw [← CommField.mul_assoc u.y (det g) v.x, mul_comm u.y (det g),
        CommField.mul_assoc (det g) u.y v.x]
  rw [t1, t2, ← mul_sub]

/-- Exact characterization of the spinor-pairing automorphism group on `S₁`:
    `g ∈ End_K(S₁)` preserves `ω` if and only if `det g = 1` (`Aut_K(S₁, ω) = Sp₂(K)`). -/
theorem preserves_omega_iff_det_eq_one (g : Mat2 K) :
    (∀ u v : Vec2 K, omega (act g u) (act g v) = omega u v) ↔ det g = 1 := by
  constructor
  · intro h
    have hbase := h Vec2.e1 Vec2.e2
    rw [omega_act_eq_det_mul] at hbase
    have he12 : omega (Vec2.e1 (K := K)) Vec2.e2 = 1 := by
      simp [omega, Vec2.e1, Vec2.e2, mul_one, mul_zero, sub_zero]
    rw [he12, mul_one] at hbase
    exact hbase
  · intro hdet u v
    rw [omega_act_eq_det_mul, hdet, one_mul]

/-! ### Refutation 1: Minimal Two-Sided Ideal of `Cl_{1,1}(K) ≅ M₂(K)` Has Dimension `4 ≠ 2` -/

/-- `Cl_{1,1}(K) ≅ M₂(K)` is a simple two-sided `K`-algebra: every nonzero element `X` generates
    the entire 4-dimensional algebra (`I₂` is a two-term `M₂(K)`-bimodule combination of `X`).
    Hence the unique minimal nonzero two-sided ideal has `dim_K = 4 ≠ 2 = d_spin`. -/
theorem mat2_is_simple_two_sided {X : Mat2 K} (hX : X ≠ zero) :
    ∃ L1 R1 L2 R2 : Mat2 K,
      add (mul (mul L1 X) R1) (mul (mul L2 X) R2) = I2 := by
  by_cases h11 : X.a11 ≠ 0
  · refine ⟨smul (inv X.a11) E11, E11, smul (inv X.a11) E21, E12, ?_⟩
    ext <;> simp [add, mul, smul, E11, E12, E21, I2,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, inv_mul_cancel h11]
  · by_cases h12 : X.a12 ≠ 0
    · refine ⟨smul (inv X.a12) E11, E21, smul (inv X.a12) E21, E22, ?_⟩
      ext <;> simp [add, mul, smul, E11, E21, E22, I2,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, inv_mul_cancel h12]
    · by_cases h21 : X.a21 ≠ 0
      · refine ⟨smul (inv X.a21) E12, E11, smul (inv X.a21) E22, E12, ?_⟩
        ext <;> simp [add, mul, smul, E11, E12, E22, I2,
          mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, inv_mul_cancel h21]
      · have z11 : X.a11 = 0 := by by_cases h : X.a11 = 0; exact h; exact absurd h h11
        have z12 : X.a12 = 0 := by by_cases h : X.a12 = 0; exact h; exact absurd h h12
        have z21 : X.a21 = 0 := by by_cases h : X.a21 = 0; exact h; exact absurd h h21
        have h22 : X.a22 ≠ 0 := by
          intro z22
          exact hX (ext z11 z12 z21 z22)
        refine ⟨smul (inv X.a22) E12, E21, smul (inv X.a22) E22, E22, ?_⟩
        ext <;> simp [add, mul, smul, E12, E21, E22, I2,
          mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, inv_mul_cancel h22]

/-! ### Euclidean Clifford Algebra `Cl_{2,0}(K) ≅ M₂(K)` (`Q(x, y) = x² + y²`) -/

/-- First generator `ε₁` of `Cl_{2,0}(K)` (`ε₁² = +I₂`). -/
def cl20_e1 : Mat2 K := ⟨1, 0, 0, -1⟩

/-- Second generator `ε₂` of `Cl_{2,0}(K)` (`ε₂² = +I₂`, `ε₁ ε₂ + ε₂ ε₁ = 0`). -/
def cl20_e2 : Mat2 K := ⟨0, 1, 1, 0⟩

theorem cl20_relations :
    mul cl20_e1 (cl20_e1 (K := K)) = I2 ∧
    mul cl20_e2 (cl20_e2 (K := K)) = I2 ∧
    add (mul cl20_e1 (cl20_e2 (K := K))) (mul cl20_e2 cl20_e1) = zero ∧
    tr (I2 (K := K)) = I2 ∧
    tr (cl20_e1 (K := K)) = cl20_e1 ∧
    tr (cl20_e2 (K := K)) = cl20_e2 ∧
    tr (mul cl20_e1 (cl20_e2 (K := K))) = mul cl20_e2 cl20_e1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [mul, cl20_e1, I2, one_mul, mul_one, zero_mul, mul_zero,
      neg_mul_neg, add_zero, zero_add]
  · ext <;> simp [mul, cl20_e2, I2, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]
  · ext <;> simp [add, mul, cl20_e1, cl20_e2, zero, one_mul, mul_one, zero_mul, mul_zero,
      neg_one_mul, mul_neg, add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  · rfl
  · rfl
  · rfl
  · ext <;> simp [tr, mul, cl20_e1, cl20_e2, one_mul, mul_one, zero_mul, mul_zero,
      neg_one_mul, mul_neg, add_zero, zero_add, neg_zero]

/-- Every reversion-covariant bilinear form `β` on the minimal left ideal `S₁ ≅ K²` of `Cl_{2,0}(K)`
    (satisfying `β(X u, v) = β(u, Xᵀ v)` for all `X ∈ Cl_{2,0}(K)`) is scalar-proportional to the
    symmetric Euclidean dot product `u.x * v.x + u.y * v.y`, and NEVER alternating unless `β ≡ 0`. -/
theorem cl20_reversion_form_is_symmetric
    (beta : Vec2 K → Vec2 K → K)
    (hlin_right_add : ∀ u v1 v2 : Vec2 K, beta u (Vec2.add v1 v2) = beta u v1 + beta u v2)
    (hlin_right_smul : ∀ (c : K) (u v : Vec2 K), beta u (Vec2.smul c v) = c * beta u v)
    (hlin_left_add : ∀ u1 u2 v : Vec2 K, beta (Vec2.add u1 u2) v = beta u1 v + beta u2 v)
    (hlin_left_smul : ∀ (c : K) (u v : Vec2 K), beta (Vec2.smul c u) v = c * beta u v)
    (hcov : ∀ (X : Mat2 K) (u v : Vec2 K), beta (act X u) v = beta u (act (tr X) v)) :
    let c := beta Vec2.e1 Vec2.e1
    (∀ u v : Vec2 K, beta u v = c * (u.x * v.x + u.y * v.y)) ∧
    ((∀ u : Vec2 K, beta u u = 0) → ∀ u v : Vec2 K, beta u v = 0) := by
  intro c
  have hzero_r : ∀ u : Vec2 K, beta u Vec2.zero = 0 := by
    intro u
    have h0 : Vec2.smul (0 : K) Vec2.e1 = Vec2.zero := by
      apply Vec2.ext <;> simp [Vec2.smul, Vec2.e1, Vec2.zero, zero_mul]
    rw [← h0, hlin_right_smul, zero_mul]
  have hb12 : beta (Vec2.e1 (K := K)) Vec2.e2 = 0 := by
    have hc1 := hcov E11 Vec2.e1 Vec2.e2
    have ha1 : act (E11 (K := K)) Vec2.e1 = Vec2.e1 := by
      apply Vec2.ext <;> simp [act, E11, Vec2.e1, one_mul, zero_mul, add_zero]
    have ha2 : act (tr (E11 (K := K))) Vec2.e2 = Vec2.zero := by
      apply Vec2.ext <;> simp [act, tr, E11, Vec2.e2, Vec2.zero, mul_zero, zero_mul, add_zero]
    rw [ha1, ha2, hzero_r] at hc1
    exact hc1
  have hb21 : beta (Vec2.e2 (K := K)) Vec2.e1 = 0 := by
    have hc2 := hcov E22 Vec2.e2 Vec2.e1
    have ha1 : act (E22 (K := K)) Vec2.e2 = Vec2.e2 := by
      apply Vec2.ext <;> simp [act, E22, Vec2.e2, mul_one, zero_mul, zero_add]
    have ha2 : act (tr (E22 (K := K))) Vec2.e1 = Vec2.zero := by
      apply Vec2.ext <;> simp [act, tr, E22, Vec2.e1, Vec2.zero, mul_zero, zero_mul, add_zero]
    rw [ha1, ha2, hzero_r] at hc2
    exact hc2
  have hb22 : beta (Vec2.e2 (K := K)) Vec2.e2 = c := by
    have hc3 := hcov cl20_e2 Vec2.e1 Vec2.e2
    have ha1 : act (cl20_e2 (K := K)) Vec2.e1 = Vec2.e2 := by
      apply Vec2.ext <;> simp [act, cl20_e2, Vec2.e1, Vec2.e2,
        zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]
    have ha2 : act (tr (cl20_e2 (K := K))) Vec2.e2 = Vec2.e1 := by
      apply Vec2.ext <;> simp [act, tr, cl20_e2, Vec2.e1, Vec2.e2,
        zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    rw [ha1, ha2] at hc3
    exact hc3
  have hformula : ∀ u v : Vec2 K, beta u v = c * (u.x * v.x + u.y * v.y) := by
    intro u v
    have hu_eq : u = Vec2.add (Vec2.smul u.x Vec2.e1) (Vec2.smul u.y Vec2.e2) :=
      (Vec2.basis_decomp u).symm
    have hv_eq : v = Vec2.add (Vec2.smul v.x Vec2.e1) (Vec2.smul v.y Vec2.e2) :=
      (Vec2.basis_decomp v).symm
    calc
      beta u v
        = beta (Vec2.add (Vec2.smul u.x Vec2.e1) (Vec2.smul u.y Vec2.e2))
               (Vec2.add (Vec2.smul v.x Vec2.e1) (Vec2.smul v.y Vec2.e2)) := by
            conv => lhs; rw [hu_eq, hv_eq]
      _ = u.x * (v.x * c + v.y * 0) + u.y * (v.x * 0 + v.y * c) := by
            have hc_def : beta Vec2.e1 Vec2.e1 = c := rfl
            rw [hlin_left_add, hlin_left_smul, hlin_left_smul,
                hlin_right_add, hlin_right_add,
                hlin_right_smul, hlin_right_smul, hlin_right_smul, hlin_right_smul,
                hb12, hb21, hb22, hc_def]
      _ = u.x * (c * v.x) + u.y * (c * v.y) := by
            rw [mul_zero, mul_zero, add_zero, zero_add, mul_comm v.x c, mul_comm v.y c]
      _ = c * (u.x * v.x) + c * (u.y * v.y) := by
            have s1 : u.x * (c * v.x) = c * (u.x * v.x) := by
              rw [← CommField.mul_assoc u.x c v.x, mul_comm u.x c, CommField.mul_assoc c u.x v.x]
            have s2 : u.y * (c * v.y) = c * (u.y * v.y) := by
              rw [← CommField.mul_assoc u.y c v.y, mul_comm u.y c, CommField.mul_assoc c u.y v.y]
            rw [s1, s2]
      _ = c * (u.x * v.x + u.y * v.y) := (left_distrib _ _ _).symm
  refine ⟨hformula, ?_⟩
  intro halt u v
  have hc0 : c = 0 := halt Vec2.e1
  rw [hformula u v, hc0, zero_mul]

end MatOps
end Mat2

end Conjecture00000007628
