import Conjecture00000007607.Clifford3

namespace Conjecture00000007607

/-!
# Higher-Dimensional Obstructions (`n = 4` and All `n ≥ 3`): `Cl_{4,0}^+(R)` & `𝔰𝔬(n)`

Establishes two complementary higher-dimensional theorems completing the analysis of
Conjecture `00000007607` across all dimensions `n ≥ 3`:
1. The four-dimensional disjoint-plane phenomenon (`Cl_{4,0}^+(R)` and `𝔰𝔬(4, R)`):
   even commuting simple bivectors (`[B₁, B₂] = 0`) fail single-angle additivity when
   their planes are completely orthogonal (`u₁ = e₁₂`, `u₂ = e₃₄`).
2. Universal refutation across every dimension `n ≥ 3` (`∀ n : Nat, 3 ≤ n → ...`).
-/

/-! ## Part 1: Even Clifford Algebra `Cl_{4,0}^+(R)` and Disjoint Orthogonal Planes -/

/-- Element of `Cl_{4,0}^+(R)` in the basis `{1, e₂₃, e₃₁, e₁₂, e₁₄, e₂₄, e₃₄, e₁₂₃₄}`. -/
structure Cl4Even (R : Type) where
  s : R
  b23 : R
  b31 : R
  b12 : R
  b14 : R
  b24 : R
  b34 : R
  p1234 : R

namespace Cl4Even

@[ext]
theorem ext {R : Type} {x y : Cl4Even R}
    (hs : x.s = y.s) (hb23 : x.b23 = y.b23) (hb31 : x.b31 = y.b31) (hb12 : x.b12 = y.b12)
    (hb14 : x.b14 = y.b14) (hb24 : x.b24 = y.b24) (hb34 : x.b34 = y.b34)
    (hp : x.p1234 = y.p1234) : x = y := by
  cases x; cases y; simp_all

section RingOps
variable {R : Type} [CommRing R]

@[simp] def zero : Cl4Even R := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
@[simp] def one : Cl4Even R := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
@[simp] def scalar (c : R) : Cl4Even R := ⟨c, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] def e23 : Cl4Even R := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
@[simp] def e31 : Cl4Even R := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
@[simp] def e12 : Cl4Even R := ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
@[simp] def e14 : Cl4Even R := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
@[simp] def e24 : Cl4Even R := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
@[simp] def e34 : Cl4Even R := ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
@[simp] def e1234 : Cl4Even R := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

def add (x y : Cl4Even R) : Cl4Even R :=
  ⟨x.s + y.s, x.b23 + y.b23, x.b31 + y.b31, x.b12 + y.b12,
   x.b14 + y.b14, x.b24 + y.b24, x.b34 + y.b34, x.p1234 + y.p1234⟩

def neg (x : Cl4Even R) : Cl4Even R :=
  ⟨-x.s, -x.b23, -x.b31, -x.b12, -x.b14, -x.b24, -x.b34, -x.p1234⟩

def sub (x y : Cl4Even R) : Cl4Even R :=
  ⟨x.s - y.s, x.b23 - y.b23, x.b31 - y.b31, x.b12 - y.b12,
   x.b14 - y.b14, x.b24 - y.b24, x.b34 - y.b34, x.p1234 - y.p1234⟩

@[simp] def smul (c : R) (x : Cl4Even R) : Cl4Even R :=
  ⟨c * x.s, c * x.b23, c * x.b31, c * x.b12,
   c * x.b14, c * x.b24, c * x.b34, c * x.p1234⟩

def mul (x y : Cl4Even R) : Cl4Even R where
  s     := x.s * y.s + x.p1234 * y.p1234
         - x.b23 * y.b23 - x.b14 * y.b14
         - x.b31 * y.b31 - x.b24 * y.b24
         - x.b12 * y.b12 - x.b34 * y.b34
  b23   := x.s * y.b23 + x.b23 * y.s - x.p1234 * y.b14 - x.b14 * y.p1234
         - x.b31 * y.b12 + x.b12 * y.b31 - x.b24 * y.b34 + x.b34 * y.b24
  b31   := x.s * y.b31 + x.b31 * y.s - x.p1234 * y.b24 - x.b24 * y.p1234
         - x.b12 * y.b23 + x.b23 * y.b12 - x.b34 * y.b14 + x.b14 * y.b34
  b12   := x.s * y.b12 + x.b12 * y.s - x.p1234 * y.b34 - x.b34 * y.p1234
         - x.b23 * y.b31 + x.b31 * y.b23 - x.b14 * y.b24 + x.b24 * y.b14
  b14   := x.s * y.b14 + x.b14 * y.s - x.p1234 * y.b23 - x.b23 * y.p1234
         - x.b31 * y.b34 + x.b34 * y.b31 - x.b24 * y.b12 + x.b12 * y.b24
  b24   := x.s * y.b24 + x.b24 * y.s - x.p1234 * y.b31 - x.b31 * y.p1234
         - x.b12 * y.b14 + x.b14 * y.b12 - x.b34 * y.b23 + x.b23 * y.b34
  b34   := x.s * y.b34 + x.b34 * y.s - x.p1234 * y.b12 - x.b12 * y.p1234
         - x.b23 * y.b24 + x.b24 * y.b23 - x.b14 * y.b31 + x.b31 * y.b14
  p1234 := x.s * y.p1234 + x.p1234 * y.s
         + x.b23 * y.b14 + x.b14 * y.b23
         + x.b31 * y.b24 + x.b24 * y.b31
         + x.b12 * y.b34 + x.b34 * y.b12

instance : OfNat (Cl4Even R) 0 := ⟨zero⟩
instance : OfNat (Cl4Even R) 1 := ⟨one⟩
instance : Add (Cl4Even R) := ⟨add⟩
instance : Neg (Cl4Even R) := ⟨neg⟩
instance : Sub (Cl4Even R) := ⟨sub⟩
instance : Mul (Cl4Even R) := ⟨mul⟩

@[simp] def bracket (x y : Cl4Even R) : Cl4Even R := x * y - y * x

@[simp] theorem zero_s : (0 : Cl4Even R).s = 0 := rfl
@[simp] theorem zero_b23 : (0 : Cl4Even R).b23 = 0 := rfl
@[simp] theorem zero_b31 : (0 : Cl4Even R).b31 = 0 := rfl
@[simp] theorem zero_b12 : (0 : Cl4Even R).b12 = 0 := rfl
@[simp] theorem zero_b14 : (0 : Cl4Even R).b14 = 0 := rfl
@[simp] theorem zero_b24 : (0 : Cl4Even R).b24 = 0 := rfl
@[simp] theorem zero_b34 : (0 : Cl4Even R).b34 = 0 := rfl
@[simp] theorem zero_p1234 : (0 : Cl4Even R).p1234 = 0 := rfl

@[simp] theorem one_s : (1 : Cl4Even R).s = 1 := rfl
@[simp] theorem one_b23 : (1 : Cl4Even R).b23 = 0 := rfl
@[simp] theorem one_b31 : (1 : Cl4Even R).b31 = 0 := rfl
@[simp] theorem one_b12 : (1 : Cl4Even R).b12 = 0 := rfl
@[simp] theorem one_b14 : (1 : Cl4Even R).b14 = 0 := rfl
@[simp] theorem one_b24 : (1 : Cl4Even R).b24 = 0 := rfl
@[simp] theorem one_b34 : (1 : Cl4Even R).b34 = 0 := rfl
@[simp] theorem one_p1234 : (1 : Cl4Even R).p1234 = 0 := rfl

@[simp] theorem add_s (x y : Cl4Even R) : (x + y).s = x.s + y.s := rfl
@[simp] theorem add_b23 (x y : Cl4Even R) : (x + y).b23 = x.b23 + y.b23 := rfl
@[simp] theorem add_b31 (x y : Cl4Even R) : (x + y).b31 = x.b31 + y.b31 := rfl
@[simp] theorem add_b12 (x y : Cl4Even R) : (x + y).b12 = x.b12 + y.b12 := rfl
@[simp] theorem add_b14 (x y : Cl4Even R) : (x + y).b14 = x.b14 + y.b14 := rfl
@[simp] theorem add_b24 (x y : Cl4Even R) : (x + y).b24 = x.b24 + y.b24 := rfl
@[simp] theorem add_b34 (x y : Cl4Even R) : (x + y).b34 = x.b34 + y.b34 := rfl
@[simp] theorem add_p1234 (x y : Cl4Even R) : (x + y).p1234 = x.p1234 + y.p1234 := rfl

@[simp] theorem neg_s (x : Cl4Even R) : (-x).s = -x.s := rfl
@[simp] theorem neg_b23 (x : Cl4Even R) : (-x).b23 = -x.b23 := rfl
@[simp] theorem neg_b31 (x : Cl4Even R) : (-x).b31 = -x.b31 := rfl
@[simp] theorem neg_b12 (x : Cl4Even R) : (-x).b12 = -x.b12 := rfl
@[simp] theorem neg_b14 (x : Cl4Even R) : (-x).b14 = -x.b14 := rfl
@[simp] theorem neg_b24 (x : Cl4Even R) : (-x).b24 = -x.b24 := rfl
@[simp] theorem neg_b34 (x : Cl4Even R) : (-x).b34 = -x.b34 := rfl
@[simp] theorem neg_p1234 (x : Cl4Even R) : (-x).p1234 = -x.p1234 := rfl

@[simp] theorem sub_s (x y : Cl4Even R) : (x - y).s = x.s - y.s := rfl
@[simp] theorem sub_b23 (x y : Cl4Even R) : (x - y).b23 = x.b23 - y.b23 := rfl
@[simp] theorem sub_b31 (x y : Cl4Even R) : (x - y).b31 = x.b31 - y.b31 := rfl
@[simp] theorem sub_b12 (x y : Cl4Even R) : (x - y).b12 = x.b12 - y.b12 := rfl
@[simp] theorem sub_b14 (x y : Cl4Even R) : (x - y).b14 = x.b14 - y.b14 := rfl
@[simp] theorem sub_b24 (x y : Cl4Even R) : (x - y).b24 = x.b24 - y.b24 := rfl
@[simp] theorem sub_b34 (x y : Cl4Even R) : (x - y).b34 = x.b34 - y.b34 := rfl
@[simp] theorem sub_p1234 (x y : Cl4Even R) : (x - y).p1234 = x.p1234 - y.p1234 := rfl

@[simp] theorem mul_s (x y : Cl4Even R) : (x * y).s =
    x.s * y.s + x.p1234 * y.p1234 - x.b23 * y.b23 - x.b14 * y.b14 -
    x.b31 * y.b31 - x.b24 * y.b24 - x.b12 * y.b12 - x.b34 * y.b34 := rfl
@[simp] theorem mul_b23 (x y : Cl4Even R) : (x * y).b23 =
    x.s * y.b23 + x.b23 * y.s - x.p1234 * y.b14 - x.b14 * y.p1234 -
    x.b31 * y.b12 + x.b12 * y.b31 - x.b24 * y.b34 + x.b34 * y.b24 := rfl
@[simp] theorem mul_b31 (x y : Cl4Even R) : (x * y).b31 =
    x.s * y.b31 + x.b31 * y.s - x.p1234 * y.b24 - x.b24 * y.p1234 -
    x.b12 * y.b23 + x.b23 * y.b12 - x.b34 * y.b14 + x.b14 * y.b34 := rfl
@[simp] theorem mul_b12 (x y : Cl4Even R) : (x * y).b12 =
    x.s * y.b12 + x.b12 * y.s - x.p1234 * y.b34 - x.b34 * y.p1234 -
    x.b23 * y.b31 + x.b31 * y.b23 - x.b14 * y.b24 + x.b24 * y.b14 := rfl
@[simp] theorem mul_b14 (x y : Cl4Even R) : (x * y).b14 =
    x.s * y.b14 + x.b14 * y.s - x.p1234 * y.b23 - x.b23 * y.p1234 -
    x.b31 * y.b34 + x.b34 * y.b31 - x.b24 * y.b12 + x.b12 * y.b24 := rfl
@[simp] theorem mul_b24 (x y : Cl4Even R) : (x * y).b24 =
    x.s * y.b24 + x.b24 * y.s - x.p1234 * y.b31 - x.b31 * y.p1234 -
    x.b12 * y.b14 + x.b14 * y.b12 - x.b34 * y.b23 + x.b23 * y.b34 := rfl
@[simp] theorem mul_b34 (x y : Cl4Even R) : (x * y).b34 =
    x.s * y.b34 + x.b34 * y.s - x.p1234 * y.b12 - x.b12 * y.p1234 -
    x.b23 * y.b24 + x.b24 * y.b23 - x.b14 * y.b31 + x.b31 * y.b14 := rfl
@[simp] theorem mul_p1234 (x y : Cl4Even R) : (x * y).p1234 =
    x.s * y.p1234 + x.p1234 * y.s + x.b23 * y.b14 + x.b14 * y.b23 +
    x.b31 * y.b24 + x.b24 * y.b31 + x.b12 * y.b34 + x.b34 * y.b12 := rfl

theorem mul_assoc (x y z : Cl4Even R) : (x * y) * z = x * (y * z) := by
  ext <;> simp <;> comm_ring

theorem e12_mul_e34 : (e12 : Cl4Even R) * e34 = e1234 := by
  ext <;> simp <;> comm_ring

theorem e34_mul_e12 : (e34 : Cl4Even R) * e12 = e1234 := by
  ext <;> simp <;> comm_ring

theorem e1234_sq : (e1234 : Cl4Even R) * e1234 = 1 := by
  ext <;> simp <;> comm_ring

/-- Disjoint orthogonal planes `e₁₂` and `e₃₄` **commute** in `𝔰𝔭𝔦𝔫(4, R)`: `[e₁₂, e₃₄] = 0`. -/
theorem disjoint_planes_commute (a1 a2 : R) :
    bracket (smul (-a1) e12) (smul (-a2) e34) = 0 := by
  ext <;> simp <;> comm_ring

/-- Yet `(B₁ + B₂)² = -(a₁² + a₂²) · 1 + 2 a₁ a₂ e₁₂₃₄` has grade-4 wedge part `2 a₁ a₂ e₁₂₃₄`. -/
theorem disjoint_sum_sq_has_grade4 (a1 a2 : R) :
    let bsum := smul (-a1) (e12 : Cl4Even R) + smul (-a2) e34
    bsum * bsum = scalar (-(a1 * a1 + a2 * a2)) + smul ((1 + 1) * a1 * a2) e1234 := by
  ext <;> simp <;> comm_ring

/-- Chiral spinor minimal polynomial: `((B₁+B₂)² + (a₁+a₂)²) ((B₁+B₂)² + (a₁-a₂)²) = 0`. -/
theorem disjoint_sum_chiral_minpoly (a1 a2 : R) :
    let bsum := smul (-a1) (e12 : Cl4Even R) + smul (-a2) e34
    (bsum * bsum + scalar ((a1 + a2) * (a1 + a2))) *
    (bsum * bsum + scalar ((a1 - a2) * (a1 - a2))) = 0 := by
  ext <;> simp <;> comm_ring

end RingOps

/-- **Theorem (`n = 4` Commuting-Generator Counterexample)**:
    Over any `StrictOrderedCommRing R` (hence `ℤ`, `ℚ`, and `ℝ`), whenever `a₁ ≠ 0` and `a₂ ≠ 0`,
    `B₁ = -a₁ e₁₂` and `B₂ = -a₂ e₃₄` satisfy `[B₁, B₂] = 0`, **yet** `(B₁ + B₂)²` has a
    strictly nonzero grade-4 component (`(B₁ + B₂)² ≠ -(a₁ + a₂)² · 1`). -/
theorem spin4_commuting_still_not_angle_additive {R : Type} [StrictOrderedCommRing R]
    {a1 a2 : R} (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0) :
    let b1 := smul (-a1) (e12 : Cl4Even R)
    let b2 := smul (-a2) (e34 : Cl4Even R)
    bracket b1 b2 = 0 ∧
    (b1 + b2) * (b1 + b2) ≠ scalar (-((a1 + a2) * (a1 + a2))) := by
  dsimp only []
  refine ⟨disjoint_planes_commute a1 a2, ?_⟩
  intro heq
  have hp : ((smul (-a1) (e12 : Cl4Even R) + smul (-a2) e34) *
             (smul (-a1) (e12 : Cl4Even R) + smul (-a2) e34)).p1234 =
            (scalar (-((a1 + a2) * (a1 + a2))) : Cl4Even R).p1234 :=
    congrArg Cl4Even.p1234 heq
  rw [disjoint_sum_sq_has_grade4] at hp
  simp only [add_p1234, scalar, smul, e1234] at hp
  have hp' : ((1 : R) + 1) * (a1 * a2) = 0 := by
    calc
      ((1 : R) + 1) * (a1 * a2) = 0 + ((1 + 1) * a1 * a2) * 1 := by comm_ring
      _ = 0 := hp
  have h2a12 : ((1 : R) + 1) * (a1 * a2) ≠ 0 :=
    StrictOrderedCommRing.mul_ne_zero StrictOrderedCommRing.two_ne_zero
      (StrictOrderedCommRing.mul_ne_zero ha1 ha2)
  exact h2a12 hp'

end Cl4Even

/-! ### Vector Representation `𝔰𝔬(4)` Double-Rotation Spectrum Check -/

/-- Action of the double-rotation generator `A(θ₁, θ₂) = θ₁ J₁₂ + θ₂ J₃₄ ∈ 𝔰𝔬(4, R)` on `R⁴`. -/
@[simp] def so4DoubleGen {R : Type} [CommRing R] (θ1 θ2 : R) (v : R × R × R × R) :
    R × R × R × R :=
  (-θ1 * v.2.1, θ1 * v.1, -θ2 * v.2.2.2, θ2 * v.2.2.1)

/-- In `𝔰𝔬(4, R)`, `A(θ₁, θ₂)` satisfies `(A² + θ₁² I)(A² + θ₂² I) = 0` on all of `R⁴`,
    whereas for `(θ₁, θ₂) = (3, 4)` the single-angle operator `A²(A² + (3+4)² I)` maps
    `e₁ = (1, 0, 0, 0)` to `(-360, 0, 0, 0) ≠ (0, 0, 0, 0)`. -/
theorem so4_double_rotation_spectrum_refutation :
    (∀ (θ1 θ2 : Int) (v : Int × Int × Int × Int),
      let a2 := fun w => so4DoubleGen θ1 θ2 (so4DoubleGen θ1 θ2 w)
      let p1 := fun w =>
        let u := a2 w
        (u.1 + θ1 * θ1 * w.1, u.2.1 + θ1 * θ1 * w.2.1,
         u.2.2.1 + θ1 * θ1 * w.2.2.1, u.2.2.2 + θ1 * θ1 * w.2.2.2)
      let p2 := fun w =>
        let u := a2 w
        (u.1 + θ2 * θ2 * w.1, u.2.1 + θ2 * θ2 * w.2.1,
         u.2.2.1 + θ2 * θ2 * w.2.2.1, u.2.2.2 + θ2 * θ2 * w.2.2.2)
      p1 (p2 v) = (0, 0, 0, 0)) ∧
    (let θ1 : Int := 3
     let θ2 : Int := 4
     let e1 : Int × Int × Int × Int := (1, 0, 0, 0)
     let a2 := fun w => so4DoubleGen θ1 θ2 (so4DoubleGen θ1 θ2 w)
     let singleAddPoly :=
       let u := a2 e1
       a2 (u.1 + (θ1 + θ2) * (θ1 + θ2) * e1.1,
           u.2.1 + (θ1 + θ2) * (θ1 + θ2) * e1.2.1,
           u.2.2.1 + (θ1 + θ2) * (θ1 + θ2) * e1.2.2.1,
           u.2.2.2 + (θ1 + θ2) * (θ1 + θ2) * e1.2.2.2)
     singleAddPoly = (-360, 0, 0, 0) ∧ singleAddPoly ≠ (0, 0, 0, 0)) := by
  refine ⟨?_, ?_⟩
  · intro θ1 θ2 ⟨x1, x2, x3, x4⟩
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp [so4DoubleGen] <;> comm_ring
  · refine ⟨rfl, ?_⟩
    intro h
    have h1 : (-360 : Int) = 0 := congrArg Prod.fst h
    cases h1

/-! ## Part 2: Universal Extension to Every Dimension `n ≥ 3` -/

namespace DimN

/-- Standard basis vector `e_k ∈ ℤ^n`. -/
def stdBasis (n : Nat) (k : Fin n) : Fin n → Int :=
  fun i => if i.val = k.val then 1 else 0

/-- Orthogonal `90°` rotation `Q₁₂^(n)` in the `(e₀, e₁)`-plane of `ℤ^n` (`n ≥ 3`). -/
def rot12 (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i =>
    if i.val = 0 then -v ⟨1, by omega⟩
    else if i.val = 1 then v ⟨0, by omega⟩
    else v i

/-- Orthogonal `90°` rotation `Q₂₃^(n)` in the `(e₁, e₂)`-plane of `ℤ^n` (`n ≥ 3`). -/
def rot23 (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i =>
    if i.val = 1 then -v ⟨2, by omega⟩
    else if i.val = 2 then v ⟨1, by omega⟩
    else v i

/-- Skew-symmetric Lie generator `A₁₂^(n) ∈ 𝔰𝔬(n, ℤ)` of unit angle in plane `(e₀, e₁)`. -/
def gen12 (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i =>
    if i.val = 0 then -v ⟨1, by omega⟩
    else if i.val = 1 then v ⟨0, by omega⟩
    else 0

/-- Skew-symmetric Lie generator `A₂₃^(n) ∈ 𝔰𝔬(n, ℤ)` of unit angle in plane `(e₁, e₂)`. -/
def gen23 (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i =>
    if i.val = 1 then -v ⟨2, by omega⟩
    else if i.val = 2 then v ⟨1, by omega⟩
    else 0

/-- Lie bracket `(A₁₂^(n) ∘ A₂₃^(n) - A₂₃^(n) ∘ A₁₂^(n))` on `ℤ^n`. -/
def lieBracket12_23 (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i => gen12 n h (gen23 n h v) i - gen23 n h (gen12 n h v) i

/-- Generator sum `S^(n) = A₁₂^(n) + A₂₃^(n)` on `ℤ^n`. -/
def genSum (n : Nat) (h : 3 ≤ n) (v : Fin n → Int) : Fin n → Int :=
  fun i => gen12 n h v i + gen23 n h v i

/-- **Universal `n ≥ 3` Refutation Theorem** across every Euclidean dimension `n ≥ 3`. -/
theorem universal_refutation_ge_3 (n : Nat) (h : 3 ≤ n) :
    let e0 := stdBasis n ⟨0, by omega⟩
    let e1 := stdBasis n ⟨1, by omega⟩
    let e2 := stdBasis n ⟨2, by omega⟩
    let comp := fun v => rot12 n h (rot23 n h v)
    let sOp := genSum n h
    (comp e0 = e1 ∧ comp e1 = e2 ∧ comp e2 = e0) ∧
    (∀ v : Fin n → Int, comp (comp (comp v)) = v) ∧
    (comp (comp e0) ≠ e0 ∧ comp (comp e0) ≠ fun i => -e0 i) ∧
    (∀ v : Fin n → Int, (fun i => sOp (fun j => sOp (sOp v) j + 2 * v j) i) = fun _ => 0) ∧
    ((fun i => sOp (sOp e0) i + 4 * e0 i) ≠ fun _ => 0) ∧
    (lieBracket12_23 n h e0 ≠ fun _ => 0) := by
  dsimp only []
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext i
    dsimp [rot12, rot23, stdBasis]
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 1
      · simp [h0, h1]
      · by_cases h2 : i.val = 2 <;> simp [h0, h1, h2]
  · funext i
    dsimp [rot12, rot23, stdBasis]
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 1
      · simp [h0, h1]
      · by_cases h2 : i.val = 2 <;> simp [h0, h1, h2]
  · funext i
    dsimp [rot12, rot23, stdBasis]
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 1
      · simp [h0, h1]
      · by_cases h2 : i.val = 2 <;> simp [h0, h1, h2]
  · intro v
    funext i
    dsimp [rot12, rot23]
    by_cases h0 : i.val = 0
    · have hi : (⟨0, by omega⟩ : Fin n) = i := Fin.ext h0.symm
      simp [h0, hi]
    · by_cases h1 : i.val = 1
      · have hi : (⟨1, by omega⟩ : Fin n) = i := Fin.ext h1.symm
        simp [h0, h1, hi]
      · by_cases h2 : i.val = 2
        · have hi : (⟨2, by omega⟩ : Fin n) = i := Fin.ext h2.symm
          simp [h0, h1, h2, hi]
        · simp [h0, h1, h2]
  · intro heq
    have hval := congrFun heq ⟨0, by omega⟩
    dsimp [rot12, rot23, stdBasis] at hval
    omega
  · intro heq
    have hval := congrFun heq ⟨0, by omega⟩
    dsimp [rot12, rot23, stdBasis] at hval
    omega
  · intro v
    funext i
    dsimp [genSum, gen12, gen23]
    by_cases h0 : i.val = 0
    · simp [h0]; omega
    · by_cases h1 : i.val = 1
      · simp [h0, h1]; omega
      · by_cases h2 : i.val = 2
        · simp [h0, h1, h2]; omega
        · simp [h0, h1, h2]
  · intro heq
    have hval := congrFun heq ⟨0, by omega⟩
    dsimp [genSum, gen12, gen23, stdBasis] at hval
    omega
  · intro heq
    have hval := congrFun heq ⟨2, by omega⟩
    dsimp [lieBracket12_23, gen12, gen23, stdBasis] at hval
    omega

end DimN

end Conjecture00000007607
