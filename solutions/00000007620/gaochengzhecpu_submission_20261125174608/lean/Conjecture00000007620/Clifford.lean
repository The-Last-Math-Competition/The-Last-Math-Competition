/-
  Conjecture 00000007620 — Layer 2: Universal 2ⁿ-Dimensional Clifford Algebras
  Genuine graded-extension construction, associativity, fundamental quadratic law,
  and Universal Property over any FormallyRealField.
  Pure Core Lean 4.19.0 (zero external dependencies, zero sorry, zero axioms).
-/
import Conjecture00000007620.Conformal

namespace Conjecture00000007620

universe u v

/-- Underlying 2ⁿ-dimensional carrier of a Clifford algebra over `F`,
    realized as nested pairs `F^(2ⁿ)`. -/
@[reducible] def CliffordCarrier (F : Type u) : Nat → Type u
  | 0 => F
  | n + 1 => CliffordCarrier F n × CliffordCarrier F n

section CarrierOps

variable {F : Type u} [FormallyRealField F]

def clZero : (n : Nat) → CliffordCarrier F n
  | 0 => 0
  | n + 1 => (clZero n, clZero n)

def clOne : (n : Nat) → CliffordCarrier F n
  | 0 => 1
  | n + 1 => (clOne n, clZero n)

def clOfScalar (c : F) : (n : Nat) → CliffordCarrier F n
  | 0 => c
  | n + 1 => (clOfScalar c n, clZero n)

def clAdd : {n : Nat} → CliffordCarrier F n → CliffordCarrier F n → CliffordCarrier F n
  | 0, x, y => x + y
  | _ + 1, (a1, b1), (a2, b2) => (clAdd a1 a2, clAdd b1 b2)

def clNeg : {n : Nat} → CliffordCarrier F n → CliffordCarrier F n
  | 0, x => -x
  | _ + 1, (a, b) => (clNeg a, clNeg b)

def clScale (c : F) : {n : Nat} → CliffordCarrier F n → CliffordCarrier F n
  | 0, x => c * x
  | _ + 1, (a, b) => (clScale c a, clScale c b)

/-- Canonical Z₂-grade involution `x ↦ x̂` on the 2ⁿ-dimensional carrier. -/
def clInvol : {n : Nat} → CliffordCarrier F n → CliffordCarrier F n
  | 0, x => x
  | _ + 1, (a, b) => (clInvol a, clNeg (clInvol b))

/-- Graded Clifford multiplication on `CliffordCarrier F n` for quadratic form `q : Fin n → F`.
    In `Cl(n + 1, q)`, `(a₁ + eₙ b₁)(a₂ + eₙ b₂) = (a₁ a₂ + qₙ b̂₁ b₂) + eₙ (â₁ b₂ + b₁ a₂)`. -/
def clMul : {n : Nat} → (q : Fin n → F) →
    CliffordCarrier F n → CliffordCarrier F n → CliffordCarrier F n
  | 0, _, x, y => x * y
  | _ + 1, q, (a1, b1), (a2, b2) =>
    (clAdd (clMul (fun j => q (finCastSucc j)) a1 a2)
           (clScale (q (finLast _)) (clMul (fun j => q (finCastSucc j)) (clInvol b1) b2)),
     clAdd (clMul (fun j => q (finCastSucc j)) (clInvol a1) b2)
           (clMul (fun j => q (finCastSucc j)) b1 a2))

/-! ### Explicit Reduction Equation Lemmas -/

@[simp] theorem clZero_succ (m : Nat) :
    (clZero (m + 1) : CliffordCarrier F (m + 1)) = (clZero m, clZero m) := rfl

@[simp] theorem clOne_succ (m : Nat) :
    (clOne (m + 1) : CliffordCarrier F (m + 1)) = (clOne m, clZero m) := rfl

@[simp] theorem clAdd_succ {m : Nat} (a1 b1 a2 b2 : CliffordCarrier F m) :
    clAdd (n := m + 1) (a1, b1) (a2, b2) = (clAdd a1 a2, clAdd b1 b2) := rfl

@[simp] theorem clNeg_succ {m : Nat} (a b : CliffordCarrier F m) :
    clNeg (n := m + 1) (a, b) = (clNeg a, clNeg b) := rfl

@[simp] theorem clScale_succ {m : Nat} (c : F) (a b : CliffordCarrier F m) :
    clScale (n := m + 1) c (a, b) = (clScale c a, clScale c b) := rfl

@[simp] theorem clInvol_succ {m : Nat} (a b : CliffordCarrier F m) :
    clInvol (n := m + 1) (a, b) = (clInvol a, clNeg (clInvol b)) := rfl

@[simp] theorem clMul_succ {m : Nat} (q : Fin (m + 1) → F)
    (a1 b1 a2 b2 : CliffordCarrier F m) :
    clMul (n := m + 1) q (a1, b1) (a2, b2) =
      (clAdd (clMul (fun j => q (finCastSucc j)) a1 a2)
             (clScale (q (finLast m)) (clMul (fun j => q (finCastSucc j)) (clInvol b1) b2)),
       clAdd (clMul (fun j => q (finCastSucc j)) (clInvol a1) b2)
             (clMul (fun j => q (finCastSucc j)) b1 a2)) := rfl

/-! ### Carrier Ring Axioms by Structural Induction -/

theorem clAdd_assoc {n : Nat} (x y z : CliffordCarrier F n) :
    clAdd (clAdd x y) z = clAdd x (clAdd y z) := by
  induction n with
  | zero => exact AssocRing.add_assoc x y z
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩; rcases z with ⟨z1, z2⟩
    simp only [clAdd_succ]
    rw [ih x1 y1 z1, ih x2 y2 z2]

theorem clAdd_comm {n : Nat} (x y : CliffordCarrier F n) :
    clAdd x y = clAdd y x := by
  induction n with
  | zero => exact AssocRing.add_comm x y
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clAdd_succ]
    rw [ih x1 y1, ih x2 y2]

theorem clZero_add {n : Nat} (x : CliffordCarrier F n) :
    clAdd (clZero n) x = x := by
  induction n with
  | zero => exact AssocRing.zero_add x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clZero_succ, clAdd_succ]
    rw [ih x1, ih x2]

theorem clAdd_zero {n : Nat} (x : CliffordCarrier F n) :
    clAdd x (clZero n) = x := by
  rw [clAdd_comm, clZero_add]

theorem clNeg_add_cancel {n : Nat} (x : CliffordCarrier F n) :
    clAdd (clNeg x) x = clZero n := by
  induction n with
  | zero => exact AssocRing.neg_add_cancel x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clNeg_succ, clAdd_succ, clZero_succ]
    rw [ih x1, ih x2]

theorem clNeg_zero (n : Nat) : clNeg (clZero n : CliffordCarrier F n) = clZero n := by
  induction n with
  | zero => exact neg_zero_ring
  | succ m ih =>
    simp only [clZero_succ, clNeg_succ]
    rw [ih]

theorem clNeg_neg {n : Nat} (x : CliffordCarrier F n) :
    clNeg (clNeg x) = x := by
  induction n with
  | zero => exact neg_neg_ring x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clNeg_succ]
    rw [ih x1, ih x2]

theorem clNeg_add {n : Nat} (x y : CliffordCarrier F n) :
    clNeg (clAdd x y) = clAdd (clNeg x) (clNeg y) := by
  induction n with
  | zero => exact neg_add_distrib_ring x y
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clAdd_succ, clNeg_succ]
    rw [ih x1 y1, ih x2 y2]

theorem clScale_zero {n : Nat} (c : F) :
    clScale c (clZero n) = clZero n := by
  induction n with
  | zero => exact mul_zero_ring c
  | succ m ih =>
    simp only [clZero_succ, clScale_succ]
    rw [ih]

theorem clZero_scale {n : Nat} (x : CliffordCarrier F n) :
    clScale 0 x = clZero n := by
  induction n with
  | zero => exact zero_mul_ring x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ, clZero_succ]
    rw [ih x1, ih x2]

theorem clOne_scale {n : Nat} (x : CliffordCarrier F n) :
    clScale 1 x = x := by
  induction n with
  | zero => exact AssocRing.one_mul x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ]
    rw [ih x1, ih x2]

theorem clScale_add {n : Nat} (c : F) (x y : CliffordCarrier F n) :
    clScale c (clAdd x y) = clAdd (clScale c x) (clScale c y) := by
  induction n with
  | zero => exact AssocRing.left_distrib c x y
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clAdd_succ, clScale_succ]
    rw [ih x1 y1, ih x2 y2]

theorem clAdd_scale {n : Nat} (c d : F) (x : CliffordCarrier F n) :
    clScale (c + d) x = clAdd (clScale c x) (clScale d x) := by
  induction n with
  | zero => exact AssocRing.right_distrib c d x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ, clAdd_succ]
    rw [ih x1, ih x2]

theorem clScale_neg {n : Nat} (c : F) (x : CliffordCarrier F n) :
    clScale c (clNeg x) = clNeg (clScale c x) := by
  induction n with
  | zero => exact mul_neg_ring c x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clNeg_succ, clScale_succ]
    rw [ih x1, ih x2]

theorem clNeg_scale {n : Nat} (c : F) (x : CliffordCarrier F n) :
    clScale (-c) x = clNeg (clScale c x) := by
  induction n with
  | zero => exact neg_mul_ring c x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ, clNeg_succ]
    rw [ih x1, ih x2]

theorem clScale_scale {n : Nat} (c d : F) (x : CliffordCarrier F n) :
    clScale c (clScale d x) = clScale (c * d) x := by
  induction n with
  | zero => exact (AssocRing.mul_assoc c d x).symm
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ]
    rw [ih x1, ih x2]

theorem clInvol_zero (n : Nat) : clInvol (clZero n : CliffordCarrier F n) = clZero n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [clZero_succ, clInvol_succ]
    rw [ih, clNeg_zero]

theorem clInvol_one (n : Nat) : clInvol (clOne n : CliffordCarrier F n) = clOne n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [clOne_succ, clInvol_succ]
    rw [ih, clInvol_zero, clNeg_zero]

theorem clInvol_neg {n : Nat} (x : CliffordCarrier F n) :
    clInvol (clNeg x) = clNeg (clInvol x) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clNeg_succ, clInvol_succ]
    rw [ih x1, ih x2]

theorem clInvol_invol {n : Nat} (x : CliffordCarrier F n) :
    clInvol (clInvol x) = x := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clInvol_succ]
    rw [ih x1, clInvol_neg, ih x2, clNeg_neg]

theorem clInvol_add {n : Nat} (x y : CliffordCarrier F n) :
    clInvol (clAdd x y) = clAdd (clInvol x) (clInvol y) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clAdd_succ, clInvol_succ]
    rw [ih x1 y1, ih x2 y2, clNeg_add]

theorem clInvol_scale {n : Nat} (c : F) (x : CliffordCarrier F n) :
    clInvol (clScale c x) = clScale c (clInvol x) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clScale_succ, clInvol_succ]
    rw [ih x1, ih x2, clScale_neg]

theorem clMul_zero_right {n : Nat} (q : Fin n → F) (x : CliffordCarrier F n) :
    clMul q x (clZero n) = clZero n := by
  induction n with
  | zero => exact mul_zero_ring x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clZero_succ, clMul_succ]
    rw [ih, ih, ih, ih, clScale_zero, clAdd_zero]

theorem clMul_zero_left {n : Nat} (q : Fin n → F) (x : CliffordCarrier F n) :
    clMul q (clZero n) x = clZero n := by
  induction n with
  | zero => exact zero_mul_ring x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clZero_succ, clMul_succ, clInvol_zero, ih, clScale_zero, clAdd_zero]

theorem clMul_scale_left {n : Nat} (q : Fin n → F) (c : F) (x y : CliffordCarrier F n) :
    clMul q (clScale c x) y = clScale c (clMul q x y) := by
  induction n with
  | zero => exact AssocRing.mul_assoc c x y
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clScale_succ, clMul_succ]
    rw [clInvol_scale, clInvol_scale, ih, ih, ih, ih, clScale_add, clScale_add,
        clScale_scale, clScale_scale, FormallyRealField.mul_comm (q (finLast m)) c]

theorem clMul_scale_right {n : Nat} (q : Fin n → F) (c : F) (x y : CliffordCarrier F n) :
    clMul q x (clScale c y) = clScale c (clMul q x y) := by
  induction n with
  | zero =>
    show x * (c * y) = c * (x * y)
    rw [← AssocRing.mul_assoc, FormallyRealField.mul_comm x c, AssocRing.mul_assoc]
  | succ m ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    simp only [clScale_succ, clMul_succ]
    rw [ih, ih, ih, ih, clScale_add, clScale_add,
        clScale_scale, clScale_scale, FormallyRealField.mul_comm (q (finLast m)) c]

theorem clMul_neg_left {n : Nat} (q : Fin n → F) (x y : CliffordCarrier F n) :
    clMul q (clNeg x) y = clNeg (clMul q x y) := by
  have h : clNeg x = clScale (-1) x := by
    rw [clNeg_scale, clOne_scale]
  have h2 : clNeg (clMul q x y) = clScale (-1) (clMul q x y) := by
    rw [clNeg_scale, clOne_scale]
  rw [h, h2, clMul_scale_left]

theorem clMul_neg_right {n : Nat} (q : Fin n → F) (x y : CliffordCarrier F n) :
    clMul q x (clNeg y) = clNeg (clMul q x y) := by
  have h : clNeg y = clScale (-1) y := by
    rw [clNeg_scale, clOne_scale]
  have h2 : clNeg (clMul q x y) = clScale (-1) (clMul q x y) := by
    rw [clNeg_scale, clOne_scale]
  rw [h, h2, clMul_scale_right]

theorem clInvol_mul {n : Nat} (q : Fin n → F) (x y : CliffordCarrier F n) :
    clInvol (clMul q x y) = clMul q (clInvol x) (clInvol y) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
    simp only [clInvol_succ, clMul_succ, clInvol_add, clInvol_scale,
               clInvol_neg, clInvol_invol, clMul_neg_left, clMul_neg_right,
               clNeg_add, clNeg_neg, ih]

theorem clOne_mul {n : Nat} (q : Fin n → F) (x : CliffordCarrier F n) :
    clMul q (clOne n) x = x := by
  induction n with
  | zero => exact AssocRing.one_mul x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clOne_succ, clMul_succ]
    rw [clInvol_zero, clInvol_one, ih, ih, clMul_zero_left, clMul_zero_left,
        clScale_zero, clAdd_zero, clAdd_zero]

theorem clMul_one {n : Nat} (q : Fin n → F) (x : CliffordCarrier F n) :
    clMul q x (clOne n) = x := by
  induction n with
  | zero => exact AssocRing.mul_one x
  | succ m ih =>
    rcases x with ⟨x1, x2⟩
    simp only [clOne_succ, clMul_succ]
    rw [ih, ih, clMul_zero_right, clMul_zero_right,
        clScale_zero, clAdd_zero, clZero_add]

theorem clLeft_distrib {n : Nat} (q : Fin n → F) (x y z : CliffordCarrier F n) :
    clMul q x (clAdd y z) = clAdd (clMul q x y) (clMul q x z) := by
  induction n with
  | zero => exact AssocRing.left_distrib x y z
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩; rcases z with ⟨a3, b3⟩
    simp only [clAdd_succ, clMul_succ]
    have sum4 : ∀ u1 u2 v1 v2 : CliffordCarrier F m,
        clAdd (clAdd u1 u2) (clAdd v1 v2) = clAdd (clAdd u1 v1) (clAdd u2 v2) := by
      intro u1 u2 v1 v2
      rw [clAdd_assoc u1 u2 (clAdd v1 v2),
          ← clAdd_assoc u2 v1 v2,
          clAdd_comm u2 v1,
          clAdd_assoc v1 u2 v2,
          ← clAdd_assoc u1 v1 (clAdd u2 v2)]
    rw [ih, ih, ih, ih, clScale_add]
    exact Prod.ext (sum4 _ _ _ _) (sum4 _ _ _ _)

theorem clRight_distrib {n : Nat} (q : Fin n → F) (x y z : CliffordCarrier F n) :
    clMul q (clAdd x y) z = clAdd (clMul q x z) (clMul q y z) := by
  induction n with
  | zero => exact AssocRing.right_distrib x y z
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩; rcases z with ⟨a3, b3⟩
    simp only [clAdd_succ, clMul_succ]
    have sum4 : ∀ u1 u2 v1 v2 : CliffordCarrier F m,
        clAdd (clAdd u1 u2) (clAdd v1 v2) = clAdd (clAdd u1 v1) (clAdd u2 v2) := by
      intro u1 u2 v1 v2
      rw [clAdd_assoc u1 u2 (clAdd v1 v2),
          ← clAdd_assoc u2 v1 v2,
          clAdd_comm u2 v1,
          clAdd_assoc v1 u2 v2,
          ← clAdd_assoc u1 v1 (clAdd u2 v2)]
    rw [clInvol_add, clInvol_add, ih, ih, ih, ih, clScale_add]
    exact Prod.ext (sum4 _ _ _ _) (sum4 _ _ _ _)

/-- Full associativity of the 2ⁿ-dimensional Clifford algebra for arbitrary `n` and `q`! -/
theorem clMul_assoc {n : Nat} (q : Fin n → F) (x y z : CliffordCarrier F n) :
    clMul q (clMul q x y) z = clMul q x (clMul q y z) := by
  induction n with
  | zero => exact AssocRing.mul_assoc x y z
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩; rcases z with ⟨a3, b3⟩
    simp only [clMul_succ]
    have sum4_23 : ∀ t1 t2 t3 t4 : CliffordCarrier F m,
        clAdd (clAdd t1 t2) (clAdd t3 t4) = clAdd (clAdd t1 t3) (clAdd t4 t2) := by
      intro t1 t2 t3 t4
      rw [clAdd_assoc t1 t2 (clAdd t3 t4),
          clAdd_comm t3 t4,
          ← clAdd_assoc t2 t4 t3,
          clAdd_comm (clAdd t2 t4) t3,
          clAdd_comm t2 t4,
          ← clAdd_assoc t1 t3 (clAdd t4 t2)]
    apply Prod.ext
    · dsimp only
      simp only [clRight_distrib, clLeft_distrib, clInvol_add, clScale_add,
                 clMul_scale_left, clMul_scale_right, clInvol_mul, clInvol_invol, ih]
      exact sum4_23 _ _ _ _
    · dsimp only
      simp only [clInvol_add, clInvol_scale, clRight_distrib, clLeft_distrib,
                 clMul_scale_left, clMul_scale_right, clInvol_mul, clInvol_invol, ih]
      exact sum4_23 _ _ _ _

end CarrierOps

/-- Genuine 2ⁿ-dimensional Clifford algebra `Cl(Fⁿ, Q_q)` parameterized by `q : Fin n → F`. -/
structure CliffordAlg (F : Type u) (n : Nat) (q : Fin n → F) : Type u where
  raw : CliffordCarrier F n

namespace CliffordAlg

@[ext]
theorem ext {F : Type u} {n : Nat} {q : Fin n → F}
    {x y : CliffordAlg F n q} (h : x.raw = y.raw) : x = y := by
  cases x; cases y; simp at h; subst h; rfl

section BasicRing

variable {F : Type u} [FormallyRealField F] {n : Nat} {q : Fin n → F}

instance : AssocRing (CliffordAlg F n q) where
  zero := ⟨clZero n⟩
  ofNat := ⟨clOne n⟩
  add := fun x y => ⟨clAdd x.raw y.raw⟩
  neg := fun x => ⟨clNeg x.raw⟩
  sub := fun x y => ⟨clAdd x.raw (clNeg y.raw)⟩
  mul := fun x y => ⟨clMul q x.raw y.raw⟩
  add_assoc := fun x y z => ext (clAdd_assoc x.raw y.raw z.raw)
  add_comm := fun x y => ext (clAdd_comm x.raw y.raw)
  zero_add := fun x => ext (clZero_add x.raw)
  add_zero := fun x => ext (clAdd_zero x.raw)
  neg_add_cancel := fun x => ext (clNeg_add_cancel x.raw)
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := fun x y z => ext (clMul_assoc q x.raw y.raw z.raw)
  one_mul := fun x => ext (clOne_mul q x.raw)
  mul_one := fun x => ext (clMul_one q x.raw)
  left_distrib := fun x y z => ext (clLeft_distrib q x.raw y.raw z.raw)
  right_distrib := fun x y z => ext (clRight_distrib q x.raw y.raw z.raw)

/-- Canonical scalar embedding `F → Z(Cl(Fⁿ, q))`. -/
def ofScalar (c : F) : CliffordAlg F n q := ⟨clScale c (clOne n)⟩

def smul (c : F) (x : CliffordAlg F n q) : CliffordAlg F n q := ⟨clScale c x.raw⟩

def invol (x : CliffordAlg F n q) : CliffordAlg F n q := ⟨clInvol x.raw⟩

theorem ofScalar_mul_eq_smul (c : F) (x : CliffordAlg F n q) :
    ofScalar c * x = smul c x := by
  apply ext
  show clMul q (clScale c (clOne n)) x.raw = clScale c x.raw
  rw [clMul_scale_left, clOne_mul]

theorem mul_ofScalar_eq_smul (x : CliffordAlg F n q) (c : F) :
    x * ofScalar c = smul c x := by
  apply ext
  show clMul q x.raw (clScale c (clOne n)) = clScale c x.raw
  rw [clMul_scale_right, clMul_one]

theorem ofScalar_central (c : F) : IsCentral (ofScalar c : CliffordAlg F n q) := by
  intro x
  rw [ofScalar_mul_eq_smul, mul_ofScalar_eq_smul]

theorem ofScalar_add (c d : F) :
    (ofScalar (c + d) : CliffordAlg F n q) = ofScalar c + ofScalar d :=
  ext (clAdd_scale c d (clOne n))

theorem ofScalar_mul (c d : F) :
    (ofScalar (c * d) : CliffordAlg F n q) = ofScalar c * ofScalar d := by
  rw [ofScalar_mul_eq_smul]
  exact ext (clScale_scale c d (clOne n)).symm

theorem ofScalar_one : (ofScalar 1 : CliffordAlg F n q) = 1 :=
  ext (clOne_scale (clOne n))

theorem ofScalar_zero : (ofScalar 0 : CliffordAlg F n q) = 0 :=
  ext (clZero_scale (clOne n))

/-- Extract the identity (`e_∅`) scalar coordinate of any Clifford element. -/
def scalarPart : {m : Nat} → CliffordCarrier F m → F
  | 0, x => x
  | _ + 1, (a, _) => scalarPart a

theorem scalarPart_zero (m : Nat) : scalarPart (clZero m : CliffordCarrier F m) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => exact ih

theorem scalarPart_one (m : Nat) : scalarPart (clOne m : CliffordCarrier F m) = 1 := by
  induction m with
  | zero => rfl
  | succ k ih => exact ih

theorem scalarPart_scale {m : Nat} (c : F) (x : CliffordCarrier F m) :
    scalarPart (clScale c x) = c * scalarPart x := by
  induction m with
  | zero => rfl
  | succ k ih => exact ih x.1

theorem ofScalar_injective {c d : F}
    (h : (ofScalar c : CliffordAlg F n q) = ofScalar d) : c = d := by
  have hs : scalarPart (clScale c (clOne n)) = scalarPart (clScale d (clOne n)) :=
    congrArg (fun x : CliffordAlg F n q => scalarPart x.raw) h
  rw [scalarPart_scale, scalarPart_scale, scalarPart_one, AssocRing.mul_one, AssocRing.mul_one] at hs
  exact hs

end BasicRing

/-! ### Orthogonal Basis Generators, Vector Embedding, and Quadratic Law `v² = Q(v)·1` -/

section Generators

variable {F : Type u} [FormallyRealField F]

def clGamma : {n : Nat} → Fin n → CliffordCarrier F n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
    if h : i.val < n then
      (clGamma ⟨i.val, h⟩, clZero n)
    else
      (clZero n, clOne n)

theorem clGamma_castSucc {n : Nat} (j : Fin n) :
    (clGamma (finCastSucc j) : CliffordCarrier F (n + 1)) = (clGamma j, clZero n) := by
  change (if h : j.val < n then (clGamma ⟨j.val, h⟩, clZero n) else (clZero n, clOne n)) =
    (clGamma j, clZero n)
  rw [dif_pos j.isLt]

theorem clGamma_last (n : Nat) :
    (clGamma (finLast n) : CliffordCarrier F (n + 1)) = (clZero n, clOne n) := by
  change (if h : n < n then (clGamma ⟨n, h⟩, clZero n) else (clZero n, clOne n)) =
    (clZero n, clOne n)
  rw [dif_neg (Nat.lt_irrefl n)]

theorem clInvol_gamma {n : Nat} (i : Fin n) :
    clInvol (clGamma i : CliffordCarrier F n) = clNeg (clGamma i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases fin_cases_last i with
    | inl hi =>
      rcases hi with ⟨j, rfl⟩
      rw [clGamma_castSucc, clInvol_succ, clNeg_succ, ih j, clInvol_zero]
    | inr hi =>
      subst hi
      rw [clGamma_last, clInvol_succ, clNeg_succ, clInvol_zero, clInvol_one, clNeg_zero]

/-- Basis generator `γ_i ∈ Cl(Fⁿ, q)`. -/
def gamma {n : Nat} {q : Fin n → F} (i : Fin n) : CliffordAlg F n q :=
  ⟨clGamma i⟩

/-- Generator square law: `γ_i * γ_i = q(i) · 1`. -/
theorem gamma_sq {n : Nat} (q : Fin n → F) (i : Fin n) :
    (gamma i : CliffordAlg F n q) * gamma i = ofScalar (q i) := by
  apply ext
  unfold gamma ofScalar
  show clMul q (clGamma i) (clGamma i) = clScale (q i) (clOne n)
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases fin_cases_last i with
    | inl hi =>
      rcases hi with ⟨j, rfl⟩
      rw [clGamma_castSucc, clOne_succ, clScale_succ, clMul_succ,
          clInvol_zero, clMul_zero_left, clMul_zero_right, clMul_zero_left,
          clScale_zero, clScale_zero, clAdd_zero, clAdd_zero,
          ih (fun k => q (finCastSucc k)) j]
    | inr hi =>
      subst hi
      rw [clGamma_last, clOne_succ, clScale_succ, clMul_succ,
          clInvol_one, clInvol_zero, clMul_zero_left, clMul_zero_left, clMul_zero_right,
          clOne_mul, clZero_add, clAdd_zero, clScale_zero]

/-- Generator anticommutation law: `γ_i * γ_j + γ_j * γ_i = 0` for `i ≠ j`. -/
theorem gamma_anticomm {n : Nat} (q : Fin n → F) {i j : Fin n} (hij : i ≠ j) :
    (gamma i : CliffordAlg F n q) * gamma j + gamma j * gamma i = 0 := by
  apply ext
  unfold gamma
  show clAdd (clMul q (clGamma i) (clGamma j)) (clMul q (clGamma j) (clGamma i)) = clZero n
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases fin_cases_last i with
    | inl hi =>
      rcases hi with ⟨i', rfl⟩
      cases fin_cases_last j with
      | inl hj =>
        rcases hj with ⟨j', rfl⟩
        have hij' : i' ≠ j' := fun hc => hij (congrArg finCastSucc hc)
        simp only [clGamma_castSucc, clZero_succ, clMul_succ, clAdd_succ,
                   clInvol_zero, clMul_zero_left, clMul_zero_right, clScale_zero,
                   clAdd_zero, clZero_add, ih (fun k => q (finCastSucc k)) hij']
      | inr hj =>
        subst hj
        simp only [clGamma_castSucc, clGamma_last, clZero_succ, clMul_succ, clAdd_succ,
                   clInvol_zero, clInvol_one, clInvol_gamma,
                   clMul_zero_right, clMul_zero_left, clScale_zero, clMul_one, clOne_mul,
                   clAdd_zero, clZero_add, clNeg_add_cancel]
    | inr hi =>
      subst hi
      cases fin_cases_last j with
      | inl hj =>
        rcases hj with ⟨j', rfl⟩
        simp only [clGamma_last, clGamma_castSucc, clZero_succ, clMul_succ, clAdd_succ,
                   clInvol_zero, clInvol_one, clInvol_gamma,
                   clMul_zero_right, clMul_zero_left, clScale_zero, clMul_one, clOne_mul,
                   clAdd_zero, clZero_add]
        exact Prod.ext rfl (by rw [clAdd_comm, clNeg_add_cancel])
      | inr hj =>
        subst hj
        exact False.elim (hij rfl)

/-- Linear embedding of vectors `v ∈ Fⁿ` into the grade-1 subspace of `Cl(Fⁿ, q)`. -/
def clEmbedVec : {n : Nat} → Vec F n → CliffordCarrier F n
  | 0, _ => 0
  | n + 1, v =>
    (clEmbedVec (fun j => v (finCastSucc j)), clScale (v (finLast n)) (clOne n))

@[simp] theorem clEmbedVec_succ {m : Nat} (v : Vec F (m + 1)) :
    clEmbedVec v =
      (clEmbedVec (fun j => v (finCastSucc j)), clScale (v (finLast m)) (clOne m)) := rfl

theorem clInvol_embedVec {n : Nat} (v : Vec F n) :
    clInvol (clEmbedVec v) = clNeg (clEmbedVec v) := by
  induction n with
  | zero => exact neg_zero_ring.symm
  | succ m ih =>
    rw [clEmbedVec_succ, clInvol_succ, clNeg_succ, ih, clInvol_scale, clInvol_one]

/-- Vector embedding `Fⁿ → Cl(Fⁿ, q)`. -/
def embedVec {n : Nat} {q : Fin n → F} (v : Vec F n) : CliffordAlg F n q :=
  ⟨clEmbedVec v⟩

/-- Fundamental Clifford Quadratic Identity: `v * v = Q_q(v) · 1` for EVERY vector `v ∈ Fⁿ`! -/
theorem embedVec_sq {n : Nat} (q : Fin n → F) (v : Vec F n) :
    (embedVec v : CliffordAlg F n q) * embedVec v = ofScalar (quadFormVec q v) := by
  apply ext
  unfold embedVec ofScalar quadFormVec polarFormVec
  show clMul q (clEmbedVec v) (clEmbedVec v) =
    clScale (finSum n (fun i => q i * v i * v i)) (clOne n)
  induction n with
  | zero =>
    show (0 : F) * 0 = 0 * 1
    rw [mul_zero_ring, zero_mul_ring]
  | succ m ih =>
    rw [clEmbedVec_succ, clMul_succ, finSum_succ_len, clOne_succ, clScale_succ]
    apply Prod.ext
    · dsimp only
      rw [ih (fun j => q (finCastSucc j)) (fun j => v (finCastSucc j)),
          clInvol_scale, clInvol_one,
          clMul_scale_left, clMul_scale_right, clOne_mul,
          clScale_scale, clScale_scale,
          ← clAdd_scale]
    · dsimp only
      simp only [clInvol_embedVec, clMul_scale_right, clMul_scale_left, clMul_neg_left,
                 clMul_one, clOne_mul, clScale_neg, clNeg_add_cancel, clScale_zero]

end Generators

/-! ### Universal Property of `CliffordAlg F n q` (Existence & Uniqueness of `lift`) -/

section UniversalProperty

variable {F : Type u} [FormallyRealField F]
variable {A : Type v} [AssocRing A]

def clLiftAux (φ : RingHom F A) :
    {n : Nat} → (Fin n → A) → CliffordCarrier F n → A
  | 0, _, c => φ.toFun c
  | _ + 1, g, (a, b) =>
    clLiftAux φ (fun j => g (finCastSucc j)) a +
    g (finLast _) * clLiftAux φ (fun j => g (finCastSucc j)) b

@[simp] theorem clLiftAux_succ (φ : RingHom F A) {m : Nat} (g : Fin (m + 1) → A)
    (a b : CliffordCarrier F m) :
    clLiftAux (n := m + 1) φ g (a, b) =
      clLiftAux φ (fun j => g (finCastSucc j)) a +
      g (finLast m) * clLiftAux φ (fun j => g (finCastSucc j)) b := rfl

private theorem clLiftAux_zero (φ : RingHom F A) {n : Nat} (g : Fin n → A) :
    clLiftAux φ g (clZero n) = 0 := by
  induction n with
  | zero => exact φ.map_zero
  | succ m ih =>
    rw [clZero_succ, clLiftAux_succ, ih, mul_zero_ring, AssocRing.add_zero]

private theorem clLiftAux_one (φ : RingHom F A) {n : Nat} (g : Fin n → A) :
    clLiftAux φ g (clOne n) = 1 := by
  induction n with
  | zero => exact φ.map_one
  | succ m ih =>
    rw [clOne_succ, clLiftAux_succ, ih, clLiftAux_zero, mul_zero_ring, AssocRing.add_zero]

private theorem clLiftAux_add (φ : RingHom F A) {n : Nat} (g : Fin n → A)
    (x y : CliffordCarrier F n) :
    clLiftAux φ g (clAdd x y) = clLiftAux φ g x + clLiftAux φ g y := by
  induction n with
  | zero => exact φ.map_add x y
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
    simp only [clAdd_succ, clLiftAux_succ]
    rw [ih, ih, AssocRing.left_distrib]
    let u1 := clLiftAux φ (fun j => g (finCastSucc j)) a1
    let u2 := clLiftAux φ (fun j => g (finCastSucc j)) a2
    let v1 := g (finLast m) * clLiftAux φ (fun j => g (finCastSucc j)) b1
    let v2 := g (finLast m) * clLiftAux φ (fun j => g (finCastSucc j)) b2
    show (u1 + u2) + (v1 + v2) = (u1 + v1) + (u2 + v2)
    rw [AssocRing.add_assoc u1 u2 (v1 + v2),
        ← AssocRing.add_assoc u2 v1 v2,
        AssocRing.add_comm u2 v1,
        AssocRing.add_assoc v1 u2 v2,
        ← AssocRing.add_assoc u1 v1 (u2 + v2)]

private theorem clLiftAux_scale (φ : RingHom F A)
    (hφC : ∀ c : F, IsCentral (φ.toFun c))
    {n : Nat} (g : Fin n → A) (c : F) (x : CliffordCarrier F n) :
    clLiftAux φ g (clScale c x) = φ.toFun c * clLiftAux φ g x := by
  induction n with
  | zero => exact φ.map_mul c x
  | succ m ih =>
    rcases x with ⟨a, b⟩
    simp only [clScale_succ, clLiftAux_succ]
    rw [ih, ih, AssocRing.left_distrib,
        ← AssocRing.mul_assoc (φ.toFun c) (g (finLast m)) _,
        hφC c (g (finLast m)),
        AssocRing.mul_assoc]

private theorem clLiftAux_comm_invol (φ : RingHom F A)
    (hφC : ∀ c : F, IsCentral (φ.toFun c))
    {n : Nat} (g : Fin n → A) (u : A)
    (hanti : ∀ j : Fin n, g j * u + u * g j = 0)
    (x : CliffordCarrier F n) :
    clLiftAux φ g x * u = u * clLiftAux φ g (clInvol x) := by
  induction n with
  | zero =>
    exact hφC x u
  | succ m ih =>
    rcases x with ⟨a, b⟩
    simp only [clInvol_succ, clLiftAux_succ]
    let gi : Fin m → A := fun j => g (finCastSucc j)
    let gn : A := g (finLast m)
    have hanti_i : ∀ j : Fin m, gi j * u + u * gi j = 0 :=
      fun j => hanti (finCastSucc j)
    have hgn_u : gn * u = -(u * gn) := by
      have h0 : gn * u + u * gn = 0 := hanti (finLast m)
      have h1 : -(gn * u) = u * gn := neg_eq_of_add_eq_zero h0
      rw [← neg_neg_ring (gn * u), h1]
    have hneg_lift : clLiftAux φ gi (clNeg (clInvol b)) = -(clLiftAux φ gi (clInvol b)) := by
      have hns : clNeg (clInvol b) = clScale (-1) (clInvol b) := by
        rw [clNeg_scale, clOne_scale]
      rw [hns, clLiftAux_scale φ hφC, φ.map_neg, φ.map_one, neg_mul_ring, AssocRing.one_mul]
    rw [AssocRing.right_distrib,
        ih gi hanti_i a,
        AssocRing.mul_assoc gn _ u,
        ih gi hanti_i b,
        ← AssocRing.mul_assoc gn u _,
        hgn_u,
        neg_mul_ring,
        hneg_lift,
        mul_neg_ring gn _,
        AssocRing.left_distrib u _ _,
        mul_neg_ring u _,
        AssocRing.mul_assoc u gn _]

private theorem clLiftAux_mul (φ : RingHom F A)
    (hφC : ∀ c : F, IsCentral (φ.toFun c))
    {n : Nat} (q : Fin n → F) (g : Fin n → A)
    (hsq : ∀ i : Fin n, g i * g i = φ.toFun (q i))
    (hanti : ∀ i j : Fin n, i ≠ j → g i * g j + g j * g i = 0)
    (x y : CliffordCarrier F n) :
    clLiftAux φ g (clMul q x y) = clLiftAux φ g x * clLiftAux φ g y := by
  induction n with
  | zero => exact φ.map_mul x y
  | succ m ih =>
    rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
    simp only [clMul_succ, clLiftAux_succ]
    let gi : Fin m → A := fun j => g (finCastSucc j)
    let gn : A := g (finLast m)
    let ql : F := q (finLast m)
    have hsq_i : ∀ j : Fin m, gi j * gi j = φ.toFun (q (finCastSucc j)) :=
      fun j => hsq (finCastSucc j)
    have hanti_i : ∀ i j : Fin m, i ≠ j → gi i * gi j + gi j * gi i = 0 :=
      fun i j hij => hanti (finCastSucc i) (finCastSucc j) (fun hc => hij (finCastSucc_inj hc))
    have hanti_gn : ∀ j : Fin m, gi j * gn + gn * gi j = 0 :=
      fun j => hanti (finCastSucc j) (finLast m) (finCastSucc_ne_last j)
    rw [clLiftAux_add, clLiftAux_scale φ hφC, clLiftAux_add,
        ih _ gi hsq_i hanti_i a1 a2,
        ih _ gi hsq_i hanti_i (clInvol b1) b2,
        ih _ gi hsq_i hanti_i (clInvol a1) b2,
        ih _ gi hsq_i hanti_i b1 a2]
    let La1 := clLiftAux φ gi a1
    let Lb1 := clLiftAux φ gi b1
    let La2 := clLiftAux φ gi a2
    let Lb2 := clLiftAux φ gi b2
    let Lia1 := clLiftAux φ gi (clInvol a1)
    let Lib1 := clLiftAux φ gi (clInvol b1)
    have comm_a1 : La1 * gn = gn * Lia1 :=
      clLiftAux_comm_invol φ hφC gi gn hanti_gn a1
    have comm_b1 : Lb1 * gn = gn * Lib1 :=
      clLiftAux_comm_invol φ hφC gi gn hanti_gn b1
    have hrhs :
        (La1 + gn * Lb1) * (La2 + gn * Lb2) =
        (La1 * La2 + φ.toFun ql * (Lib1 * Lb2)) + gn * (Lia1 * Lb2 + Lb1 * La2) := by
      have t1 : La1 * (gn * Lb2) = gn * (Lia1 * Lb2) := by
        rw [← AssocRing.mul_assoc La1 gn Lb2, comm_a1, AssocRing.mul_assoc]
      have t2 : (gn * Lb1) * La2 = gn * (Lb1 * La2) :=
        AssocRing.mul_assoc gn Lb1 La2
      have t3 : (gn * Lb1) * (gn * Lb2) = φ.toFun ql * (Lib1 * Lb2) := by
        calc
          (gn * Lb1) * (gn * Lb2)
              = gn * (Lb1 * (gn * Lb2)) := AssocRing.mul_assoc gn Lb1 _
          _ = gn * ((Lb1 * gn) * Lb2) := by rw [← AssocRing.mul_assoc Lb1 gn Lb2]
          _ = gn * ((gn * Lib1) * Lb2) := by rw [comm_b1]
          _ = (gn * gn) * (Lib1 * Lb2) := by
                rw [AssocRing.mul_assoc gn Lib1 Lb2, ← AssocRing.mul_assoc gn gn _]
          _ = φ.toFun ql * (Lib1 * Lb2) := by rw [hsq (finLast m)]
      rw [AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib,
          t1, t2, t3, AssocRing.left_distrib gn]
      let U1 := La1 * La2
      let V1 := gn * (Lia1 * Lb2)
      let V2 := gn * (Lb1 * La2)
      let U2 := φ.toFun ql * (Lib1 * Lb2)
      show (U1 + V1) + (V2 + U2) = (U1 + U2) + (V1 + V2)
      rw [AssocRing.add_assoc U1 V1 (V2 + U2),
          AssocRing.add_comm V2 U2,
          ← AssocRing.add_assoc V1 U2 V2,
          AssocRing.add_comm V1 U2,
          AssocRing.add_assoc U2 V1 V2,
          ← AssocRing.add_assoc U1 U2 (V1 + V2)]
    exact hrhs.symm

/-- Universal Property of `CliffordAlg`: any family of elements `g_i ∈ A` satisfying
    `g_i² = φ(q_i)` and `g_i g_j + g_j g_i = 0` (`i ≠ j`) extends to a unital ring homomorphism
    `CliffordAlg F n q → A`! -/
def lift {n : Nat} {q : Fin n → F}
    (φ : RingHom F A) (hφC : ∀ c : F, IsCentral (φ.toFun c))
    (g : Fin n → A)
    (hsq : ∀ i : Fin n, g i * g i = φ.toFun (q i))
    (hanti : ∀ i j : Fin n, i ≠ j → g i * g j + g j * g i = 0) :
    RingHom (CliffordAlg F n q) A where
  toFun := fun x => clLiftAux φ g x.raw
  map_one := clLiftAux_one φ g
  map_add := fun x y => clLiftAux_add φ g x.raw y.raw
  map_mul := fun x y => clLiftAux_mul φ hφC q g hsq hanti x.raw y.raw

theorem lift_gamma {n : Nat} {q : Fin n → F}
    (φ : RingHom F A) (hφC : ∀ c : F, IsCentral (φ.toFun c))
    (g : Fin n → A)
    (hsq : ∀ i : Fin n, g i * g i = φ.toFun (q i))
    (hanti : ∀ i j : Fin n, i ≠ j → g i * g j + g j * g i = 0)
    (i : Fin n) :
    (lift (q := q) φ hφC g hsq hanti).toFun (gamma i) = g i := by
  unfold lift gamma
  dsimp only
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases fin_cases_last i with
    | inl hi =>
      rcases hi with ⟨j, rfl⟩
      rw [clGamma_castSucc, clLiftAux_succ, clLiftAux_zero, mul_zero_ring, AssocRing.add_zero]
      exact ih (q := fun k => q (finCastSucc k)) (fun k => g (finCastSucc k))
        (fun k => hsq (finCastSucc k))
        (fun k l hkl => hanti (finCastSucc k) (finCastSucc l) (fun hc => hkl (finCastSucc_inj hc))) j
    | inr hi =>
      subst hi
      rw [clGamma_last, clLiftAux_succ, clLiftAux_zero, clLiftAux_one,
          AssocRing.mul_one, AssocRing.zero_add]

theorem lift_ofScalar {n : Nat} {q : Fin n → F}
    (φ : RingHom F A) (hφC : ∀ c : F, IsCentral (φ.toFun c))
    (g : Fin n → A)
    (hsq : ∀ i : Fin n, g i * g i = φ.toFun (q i))
    (hanti : ∀ i j : Fin n, i ≠ j → g i * g j + g j * g i = 0)
    (c : F) :
    (lift (q := q) φ hφC g hsq hanti).toFun (ofScalar c) = φ.toFun c := by
  unfold lift ofScalar
  dsimp only
  rw [clLiftAux_scale φ hφC, clLiftAux_one, AssocRing.mul_one]

/-- Uniqueness half of the Universal Property: any two unital ring homomorphisms out of
    `CliffordAlg F n q` that agree on scalars and on all generators `γ_i` are identical! -/
theorem hom_unique {n : Nat} {q : Fin n → F}
    (Ψ₁ Ψ₂ : RingHom (CliffordAlg F n q) A)
    (hscalar : ∀ c : F, Ψ₁.toFun (ofScalar c) = Ψ₂.toFun (ofScalar c))
    (hgamma : ∀ i : Fin n, Ψ₁.toFun (gamma i) = Ψ₂.toFun (gamma i)) :
    Ψ₁.toFun = Ψ₂.toFun := by
  funext x
  rcases x with ⟨r⟩
  induction n with
  | zero =>
    have hs := hscalar r
    change Ψ₁.toFun ⟨r * 1⟩ = Ψ₂.toFun ⟨r * 1⟩ at hs
    rw [AssocRing.mul_one] at hs
    exact hs
  | succ m ih =>
    rcases r with ⟨a, b⟩
    let qi : Fin m → F := fun j => q (finCastSucc j)
    let incl : RingHom (CliffordAlg F m qi) (CliffordAlg F (m + 1) q) := {
      toFun := fun y => ⟨(y.raw, clZero m)⟩
      map_one := rfl
      map_add := fun y1 y2 => ext (Prod.ext rfl (clAdd_zero (clZero m)).symm)
      map_mul := fun y1 y2 => by
        apply ext
        show (clMul qi y1.raw y2.raw, clZero m) =
          clMul q (y1.raw, clZero m) (y2.raw, clZero m)
        simp only [clMul_succ, clInvol_zero, clMul_zero_left, clMul_zero_right,
                   clScale_zero, clAdd_zero, clZero_add]
        rfl
    }
    let Ψ₁' : RingHom (CliffordAlg F m qi) A := {
      toFun := fun y => Ψ₁.toFun (incl.toFun y)
      map_one := by rw [incl.map_one, Ψ₁.map_one]
      map_add := fun y1 y2 => by rw [incl.map_add, Ψ₁.map_add]
      map_mul := fun y1 y2 => by rw [incl.map_mul, Ψ₁.map_mul]
    }
    let Ψ₂' : RingHom (CliffordAlg F m qi) A := {
      toFun := fun y => Ψ₂.toFun (incl.toFun y)
      map_one := by rw [incl.map_one, Ψ₂.map_one]
      map_add := fun y1 y2 => by rw [incl.map_add, Ψ₂.map_add]
      map_mul := fun y1 y2 => by rw [incl.map_mul, Ψ₂.map_mul]
    }
    have hsc' : ∀ c : F, Ψ₁'.toFun (ofScalar c) = Ψ₂'.toFun (ofScalar c) := by
      intro c
      have hinc : incl.toFun (ofScalar c) = (ofScalar c : CliffordAlg F (m + 1) q) := by
        apply ext
        show (clScale c (clOne m), clZero m) = (clScale c (clOne m), clScale c (clZero m))
        rw [clScale_zero]
      show Ψ₁.toFun (incl.toFun (ofScalar c)) = Ψ₂.toFun (incl.toFun (ofScalar c))
      rw [hinc]
      exact hscalar c
    have hgm' : ∀ j : Fin m, Ψ₁'.toFun (gamma j) = Ψ₂'.toFun (gamma j) := by
      intro j
      have hinc : incl.toFun (gamma j) = (gamma (finCastSucc j) : CliffordAlg F (m + 1) q) := by
        apply ext
        unfold gamma
        exact (clGamma_castSucc j).symm
      show Ψ₁.toFun (incl.toFun (gamma j)) = Ψ₂.toFun (incl.toFun (gamma j))
      rw [hinc]
      exact hgamma (finCastSucc j)
    have h_eq' := ih (q := qi) Ψ₁' Ψ₂' hsc' hgm'
    have hdecomp :
        (⟨(a, b)⟩ : CliffordAlg F (m + 1) q) =
        incl.toFun ⟨a⟩ + gamma (finLast m) * incl.toFun ⟨b⟩ := by
      apply ext
      show (a, b) = clAdd (n := m + 1) (a, clZero m) (clMul q (clGamma (finLast m)) (b, clZero m))
      simp only [clGamma_last, clMul_succ, clAdd_succ,
                 clInvol_zero, clInvol_one, clMul_zero_left, clMul_zero_right,
                 clOne_mul, clScale_zero, clAdd_zero, clZero_add]
    rw [hdecomp, Ψ₁.map_add, Ψ₁.map_mul, Ψ₂.map_add, Ψ₂.map_mul,
        hgamma (finLast m)]
    have ha : Ψ₁.toFun (incl.toFun ⟨a⟩) = Ψ₂.toFun (incl.toFun ⟨a⟩) := h_eq' a
    have hb : Ψ₁.toFun (incl.toFun ⟨b⟩) = Ψ₂.toFun (incl.toFun ⟨b⟩) := h_eq' b
    rw [ha, hb]

end UniversalProperty

end CliffordAlg

end Conjecture00000007620
