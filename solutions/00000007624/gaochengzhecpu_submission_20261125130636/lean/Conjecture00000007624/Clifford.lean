/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
General `2^n`-dimensional Clifford superalgebra `Cl R g` constructed inductively via
graded Clifford doubling over an arbitrary commutative ring `R`, together with full
`AssocRing` proofs, canonical scalar and grade-1 vector embeddings, the fundamental
Clifford relation `embedVec v * embedVec v = scalar g (quadForm g v)`, and the
grade-1 nilpotent–isotropic equivalence theorem.
-/
import Conjecture00000007624.QuadraticForm

namespace Conjecture00000007624

/-- Inductive `2^n`-dimensional Clifford algebra `Cl R g` associated to `g : List R`.
    For `g = c :: gs`, `(x, y)` represents `x + y * e_0` where `e_0^2 = c` and
    `e_0 * z = clInvol z * e_0` for all `z : Cl R gs`. -/
def Cl (R : Type u) : List R → Type u
  | [] => R
  | _ :: gs => Cl R gs × Cl R gs

section CliffordRing

variable {R : Type u} [CommRing R]

def clZero : (g : List R) → Cl R g
  | [] => show R from 0
  | _ :: gs => (clZero gs, clZero gs)

def clOne : (g : List R) → Cl R g
  | [] => show R from 1
  | _ :: gs => (clOne gs, clZero gs)

def clAdd : {g : List R} → Cl R g → Cl R g → Cl R g
  | [], a, b => show R from (show R from a) + (show R from b)
  | _ :: _, (x1, y1), (x2, y2) => (clAdd x1 x2, clAdd y1 y2)

def clNeg : {g : List R} → Cl R g → Cl R g
  | [], a => show R from -(show R from a)
  | _ :: _, (x, y) => (clNeg x, clNeg y)

def clSub : {g : List R} → Cl R g → Cl R g → Cl R g
  | [], a, b => show R from (show R from a) - (show R from b)
  | _ :: _, (x1, y1), (x2, y2) => (clSub x1 x2, clSub y1 y2)

def clSmul : {g : List R} → R → Cl R g → Cl R g
  | [], r, a => show R from r * (show R from a)
  | _ :: _, r, (x, y) => (clSmul r x, clSmul r y)

/-- Grade involution `α` sending even blades `z ↦ z` and odd blades `z ↦ -z`. -/
def clInvol : {g : List R} → Cl R g → Cl R g
  | [], a => a
  | _ :: _, (x, y) => (clInvol x, clNeg (clInvol y))

/-- Graded Clifford product on `Cl R g`. -/
def clMul : {g : List R} → Cl R g → Cl R g → Cl R g
  | [], a, b => show R from (show R from a) * (show R from b)
  | c :: _, (x1, y1), (x2, y2) =>
    (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))),
     clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))

/-! ### Step 1: Abelian group laws on `Cl R g` -/

private theorem clAdd_assoc : ∀ {g : List R} (a b d : Cl R g),
    clAdd (clAdd a b) d = clAdd a (clAdd b d)
  | [], a, b, d => AssocRing.add_assoc (A := R) a b d
  | _ :: _, (x1, y1), (x2, y2), (x3, y3) =>
    Prod.ext (clAdd_assoc x1 x2 x3) (clAdd_assoc y1 y2 y3)

private theorem clAdd_comm : ∀ {g : List R} (a b : Cl R g),
    clAdd a b = clAdd b a
  | [], a, b => AssocRing.add_comm (A := R) a b
  | _ :: _, (x1, y1), (x2, y2) =>
    Prod.ext (clAdd_comm x1 x2) (clAdd_comm y1 y2)

private theorem clZero_add : ∀ {g : List R} (a : Cl R g),
    clAdd (clZero g) a = a
  | [], a => zero_add_eq (A := R) a
  | _ :: _, (x, y) => Prod.ext (clZero_add x) (clZero_add y)

private theorem clAdd_zero : ∀ {g : List R} (a : Cl R g),
    clAdd a (clZero g) = a
  | [], a => add_zero_eq (A := R) a
  | _ :: _, (x, y) => Prod.ext (clAdd_zero x) (clAdd_zero y)

private theorem clNeg_add_cancel : ∀ {g : List R} (a : Cl R g),
    clAdd (clNeg a) a = clZero g
  | [], a => neg_add_cancel_eq (A := R) a
  | _ :: _, (x, y) => Prod.ext (clNeg_add_cancel x) (clNeg_add_cancel y)

private theorem clSub_eq_add_neg : ∀ {g : List R} (a b : Cl R g),
    clSub a b = clAdd a (clNeg b)
  | [], a, b => AssocRing.sub_eq_add_neg (A := R) a b
  | _ :: _, (x1, y1), (x2, y2) =>
    Prod.ext (clSub_eq_add_neg x1 x2) (clSub_eq_add_neg y1 y2)

private theorem clNeg_zero : ∀ (g : List R), clNeg (clZero g) = clZero g
  | [] => neg_zero_eq (A := R)
  | _ :: gs => Prod.ext (clNeg_zero gs) (clNeg_zero gs)

private theorem clNeg_neg : ∀ {g : List R} (a : Cl R g), clNeg (clNeg a) = a
  | [], a => neg_neg_eq (A := R) a
  | _ :: _, (x, y) => Prod.ext (clNeg_neg x) (clNeg_neg y)

private theorem clNeg_add : ∀ {g : List R} (a b : Cl R g),
    clNeg (clAdd a b) = clAdd (clNeg a) (clNeg b)
  | [], a, b => neg_add_distrib (A := R) a b
  | _ :: _, (x1, y1), (x2, y2) => Prod.ext (clNeg_add x1 x2) (clNeg_add y1 y2)

/-! ### Step 2: Scalar action `clSmul` and grade involution `clInvol` -/

private theorem clSmul_zero_right : ∀ (g : List R) (r : R),
    clSmul r (clZero g) = clZero g
  | [], r => (mul_zero_eq r : r * 0 = 0)
  | _ :: gs, r => Prod.ext (clSmul_zero_right gs r) (clSmul_zero_right gs r)

private theorem clSmul_add : ∀ {g : List R} (r : R) (a b : Cl R g),
    clSmul r (clAdd a b) = clAdd (clSmul r a) (clSmul r b)
  | [], r, a, b => AssocRing.left_distrib r (a : R) (b : R)
  | _ :: _, r, (x1, y1), (x2, y2) =>
    Prod.ext (clSmul_add r x1 x2) (clSmul_add r y1 y2)

private theorem clAdd_smul : ∀ {g : List R} (r s : R) (a : Cl R g),
    clSmul (r + s) a = clAdd (clSmul r a) (clSmul s a)
  | [], r, s, a => AssocRing.right_distrib r s (a : R)
  | _ :: _, r, s, (x, y) =>
    Prod.ext (clAdd_smul r s x) (clAdd_smul r s y)

private theorem clSmul_neg : ∀ {g : List R} (r : R) (a : Cl R g),
    clSmul r (clNeg a) = clNeg (clSmul r a)
  | [], r, a => mul_neg_eq r (a : R)
  | _ :: _, r, (x, y) => Prod.ext (clSmul_neg r x) (clSmul_neg r y)

private theorem clSmul_smul : ∀ {g : List R} (r s : R) (a : Cl R g),
    clSmul (r * s) a = clSmul r (clSmul s a)
  | [], r, s, a => AssocRing.mul_assoc r s (a : R)
  | _ :: _, r, s, (x, y) => Prod.ext (clSmul_smul r s x) (clSmul_smul r s y)

private theorem clSmul_comm : ∀ {g : List R} (r s : R) (a : Cl R g),
    clSmul r (clSmul s a) = clSmul s (clSmul r a) := by
  intro g r s a
  rw [← clSmul_smul, CommRing.mul_comm r s, clSmul_smul]

theorem clInvol_zero : ∀ (g : List R), clInvol (clZero g) = clZero g
  | [] => rfl
  | _ :: gs => Prod.ext (clInvol_zero gs) (by
      change clNeg (clInvol (clZero gs)) = clZero gs
      rw [clInvol_zero gs, clNeg_zero gs])

theorem clInvol_one : ∀ (g : List R), clInvol (clOne g) = clOne g
  | [] => rfl
  | _ :: gs => Prod.ext (clInvol_one gs) (by
      change clNeg (clInvol (clZero gs)) = clZero gs
      rw [clInvol_zero gs, clNeg_zero gs])

theorem clInvol_add : ∀ {g : List R} (a b : Cl R g),
    clInvol (clAdd a b) = clAdd (clInvol a) (clInvol b)
  | [], _, _ => rfl
  | _ :: _, (x1, y1), (x2, y2) =>
    Prod.ext (clInvol_add x1 x2) (by
      change clNeg (clInvol (clAdd y1 y2)) = clAdd (clNeg (clInvol y1)) (clNeg (clInvol y2))
      rw [clInvol_add y1 y2, clNeg_add])

theorem clInvol_neg : ∀ {g : List R} (a : Cl R g),
    clInvol (clNeg a) = clNeg (clInvol a)
  | [], _ => rfl
  | _ :: _, (x, y) => Prod.ext (clInvol_neg x) (by
      change clNeg (clInvol (clNeg y)) = clNeg (clNeg (clInvol y))
      rw [clInvol_neg y])

theorem clInvol_invol : ∀ {g : List R} (a : Cl R g),
    clInvol (clInvol a) = a
  | [], _ => rfl
  | _ :: _, (x, y) =>
    Prod.ext (clInvol_invol x) (by
      change clNeg (clInvol (clNeg (clInvol y))) = y
      rw [clInvol_neg, clNeg_neg, clInvol_invol y])

private theorem clInvol_smul : ∀ {g : List R} (r : R) (a : Cl R g),
    clInvol (clSmul r a) = clSmul r (clInvol a)
  | [], _, _ => rfl
  | _ :: _, r, (x, y) =>
    Prod.ext (clInvol_smul r x) (by
      change clNeg (clInvol (clSmul r y)) = clSmul r (clNeg (clInvol y))
      rw [clInvol_smul r y, clSmul_neg])

/-! ### Step 3: Multiplicative zero, identity, distributivity, and scalar bilinearity -/

private theorem clMul_zero : ∀ {g : List R} (a : Cl R g),
    clMul a (clZero g) = clZero g
  | [], a => mul_zero_eq (A := R) a
  | c :: gs, (x, y) => by
    change (clAdd (clMul x (clZero gs)) (clSmul c (clMul y (clInvol (clZero gs)))),
            clAdd (clMul x (clZero gs)) (clMul y (clInvol (clZero gs)))) =
           (clZero gs, clZero gs)
    rw [clInvol_zero gs, clMul_zero x, clMul_zero y, clSmul_zero_right gs c, clZero_add]

private theorem clZero_mul : ∀ {g : List R} (a : Cl R g),
    clMul (clZero g) a = clZero g
  | [], a => zero_mul_eq (A := R) a
  | c :: gs, (x, y) => by
    change (clAdd (clMul (clZero gs) x) (clSmul c (clMul (clZero gs) (clInvol y))),
            clAdd (clMul (clZero gs) y) (clMul (clZero gs) (clInvol x))) =
           (clZero gs, clZero gs)
    rw [clZero_mul x, clZero_mul y, clZero_mul (clInvol y), clZero_mul (clInvol x),
        clSmul_zero_right gs c, clZero_add]

private theorem clOne_mul : ∀ {g : List R} (a : Cl R g),
    clMul (clOne g) a = a
  | [], a => one_mul_eq (A := R) a
  | c :: gs, (x, y) => by
    change (clAdd (clMul (clOne gs) x) (clSmul c (clMul (clZero gs) (clInvol y))),
            clAdd (clMul (clOne gs) y) (clMul (clZero gs) (clInvol x))) = (x, y)
    rw [clOne_mul x, clOne_mul y, clZero_mul, clZero_mul, clSmul_zero_right gs c,
        clAdd_zero, clAdd_zero]

private theorem clMul_one : ∀ {g : List R} (a : Cl R g),
    clMul a (clOne g) = a
  | [], a => mul_one_eq (A := R) a
  | c :: gs, (x, y) => by
    change (clAdd (clMul x (clOne gs)) (clSmul c (clMul y (clInvol (clZero gs)))),
            clAdd (clMul x (clZero gs)) (clMul y (clInvol (clOne gs)))) = (x, y)
    rw [clInvol_zero gs, clInvol_one gs, clMul_one x, clMul_one y,
        clMul_zero, clMul_zero, clSmul_zero_right gs c, clAdd_zero, clZero_add]

private theorem clAdd_four_swap {g : List R} (a b d e : Cl R g) :
    clAdd (clAdd a b) (clAdd d e) = clAdd (clAdd a d) (clAdd b e) := by
  calc
    clAdd (clAdd a b) (clAdd d e)
      = clAdd a (clAdd b (clAdd d e)) := clAdd_assoc a b (clAdd d e)
    _ = clAdd a (clAdd (clAdd b d) e) := by rw [← clAdd_assoc b d e]
    _ = clAdd a (clAdd (clAdd d b) e) := by rw [clAdd_comm b d]
    _ = clAdd a (clAdd d (clAdd b e)) := by rw [clAdd_assoc d b e]
    _ = clAdd (clAdd a d) (clAdd b e) := by rw [← clAdd_assoc a d (clAdd b e)]

private theorem clLeft_distrib : ∀ {g : List R} (a b d : Cl R g),
    clMul a (clAdd b d) = clAdd (clMul a b) (clMul a d)
  | [], a, b, d => AssocRing.left_distrib (A := R) a b d
  | c :: _, (x1, y1), (x2, y2), (x3, y3) => by
    apply Prod.ext
    · change clAdd (clMul x1 (clAdd x2 x3)) (clSmul c (clMul y1 (clInvol (clAdd y2 y3)))) =
        clAdd (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))))
              (clAdd (clMul x1 x3) (clSmul c (clMul y1 (clInvol y3))))
      rw [clInvol_add, clLeft_distrib x1, clLeft_distrib y1, clSmul_add, clAdd_four_swap]
    · change clAdd (clMul x1 (clAdd y2 y3)) (clMul y1 (clInvol (clAdd x2 x3))) =
        clAdd (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))
              (clAdd (clMul x1 y3) (clMul y1 (clInvol x3)))
      rw [clInvol_add, clLeft_distrib x1, clLeft_distrib y1, clAdd_four_swap]

private theorem clRight_distrib : ∀ {g : List R} (a b d : Cl R g),
    clMul (clAdd a b) d = clAdd (clMul a d) (clMul b d)
  | [], a, b, d => AssocRing.right_distrib (A := R) a b d
  | c :: _, (x1, y1), (x2, y2), (x3, y3) => by
    apply Prod.ext
    · change clAdd (clMul (clAdd x1 x2) x3) (clSmul c (clMul (clAdd y1 y2) (clInvol y3))) =
        clAdd (clAdd (clMul x1 x3) (clSmul c (clMul y1 (clInvol y3))))
              (clAdd (clMul x2 x3) (clSmul c (clMul y2 (clInvol y3))))
      rw [clRight_distrib x1 x2 x3, clRight_distrib y1 y2, clSmul_add, clAdd_four_swap]
    · change clAdd (clMul (clAdd x1 x2) y3) (clMul (clAdd y1 y2) (clInvol x3)) =
        clAdd (clAdd (clMul x1 y3) (clMul y1 (clInvol x3)))
              (clAdd (clMul x2 y3) (clMul y2 (clInvol x3)))
      rw [clRight_distrib x1 x2 y3, clRight_distrib y1 y2, clAdd_four_swap]

private theorem clMul_neg : ∀ {g : List R} (a b : Cl R g),
    clMul a (clNeg b) = clNeg (clMul a b)
  | [], a, b => mul_neg_eq (A := R) a b
  | c :: _, (x1, y1), (x2, y2) => by
    apply Prod.ext
    · change clAdd (clMul x1 (clNeg x2)) (clSmul c (clMul y1 (clInvol (clNeg y2)))) =
        clNeg (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))))
      rw [clInvol_neg, clMul_neg x1 x2, clMul_neg y1, clSmul_neg, clNeg_add]
    · change clAdd (clMul x1 (clNeg y2)) (clMul y1 (clInvol (clNeg x2))) =
        clNeg (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))
      rw [clInvol_neg, clMul_neg x1 y2, clMul_neg y1, clNeg_add]

private theorem clNeg_mul : ∀ {g : List R} (a b : Cl R g),
    clMul (clNeg a) b = clNeg (clMul a b)
  | [], a, b => neg_mul_eq (A := R) a b
  | c :: _, (x1, y1), (x2, y2) => by
    apply Prod.ext
    · change clAdd (clMul (clNeg x1) x2) (clSmul c (clMul (clNeg y1) (clInvol y2))) =
        clNeg (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))))
      rw [clNeg_mul x1 x2, clNeg_mul y1, clSmul_neg, clNeg_add]
    · change clAdd (clMul (clNeg x1) y2) (clMul (clNeg y1) (clInvol x2)) =
        clNeg (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))
      rw [clNeg_mul x1 y2, clNeg_mul y1, clNeg_add]

private theorem clNeg_mul_neg {g : List R} (a b : Cl R g) :
    clMul (clNeg a) (clNeg b) = clMul a b := by
  rw [clNeg_mul, clMul_neg, clNeg_neg]

private theorem clSmul_mul_left : ∀ {g : List R} (r : R) (a b : Cl R g),
    clMul (clSmul r a) b = clSmul r (clMul a b)
  | [], r, a, b => AssocRing.mul_assoc (A := R) r a b
  | c :: _, r, (x1, y1), (x2, y2) => by
    apply Prod.ext
    · change clAdd (clMul (clSmul r x1) x2) (clSmul c (clMul (clSmul r y1) (clInvol y2))) =
        clSmul r (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))))
      rw [clSmul_mul_left r x1 x2, clSmul_mul_left r y1, clSmul_comm c r, clSmul_add]
    · change clAdd (clMul (clSmul r x1) y2) (clMul (clSmul r y1) (clInvol x2)) =
        clSmul r (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))
      rw [clSmul_mul_left r x1 y2, clSmul_mul_left r y1, clSmul_add]

private theorem clSmul_mul_right : ∀ {g : List R} (r : R) (a b : Cl R g),
    clMul a (clSmul r b) = clSmul r (clMul a b)
  | [], r, a, b => by
    let a' : R := a
    let b' : R := b
    change a' * (r * b') = r * (a' * b')
    rw [← AssocRing.mul_assoc, CommRing.mul_comm a' r, AssocRing.mul_assoc]
  | c :: _, r, (x1, y1), (x2, y2) => by
    apply Prod.ext
    · change clAdd (clMul x1 (clSmul r x2)) (clSmul c (clMul y1 (clInvol (clSmul r y2)))) =
        clSmul r (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2))))
      rw [clInvol_smul, clSmul_mul_right r x1 x2, clSmul_mul_right r y1,
          clSmul_comm c r, clSmul_add]
    · change clAdd (clMul x1 (clSmul r y2)) (clMul y1 (clInvol (clSmul r x2))) =
        clSmul r (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))
      rw [clInvol_smul, clSmul_mul_right r x1 y2, clSmul_mul_right r y1, clSmul_add]

/-! ### Step 4: `clInvol` is a superalgebra automorphism and `clMul` is associative -/

private theorem clInvol_mul : ∀ {g : List R} (a b : Cl R g),
    clInvol (clMul a b) = clMul (clInvol a) (clInvol b)
  | [], _, _ => rfl
  | c :: _, (x1, y1), (x2, y2) => by
    apply Prod.ext
    · change clInvol (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2)))) =
        clAdd (clMul (clInvol x1) (clInvol x2))
              (clSmul c (clMul (clNeg (clInvol y1)) (clInvol (clNeg (clInvol y2)))))
      rw [clInvol_add, clInvol_smul, clInvol_mul x1 x2, clInvol_mul y1 (clInvol y2),
          clInvol_neg, clNeg_mul_neg]
    · change clNeg (clInvol (clAdd (clMul x1 y2) (clMul y1 (clInvol x2)))) =
        clAdd (clMul (clInvol x1) (clNeg (clInvol y2)))
              (clMul (clNeg (clInvol y1)) (clInvol (clInvol x2)))
      rw [clInvol_add, clInvol_mul x1 y2, clInvol_mul y1 (clInvol x2),
          clMul_neg, clNeg_mul, clNeg_add]

private theorem clMul_assoc : ∀ {g : List R} (a b d : Cl R g),
    clMul (clMul a b) d = clMul a (clMul b d)
  | [], a, b, d => AssocRing.mul_assoc (A := R) a b d
  | c :: _, (x1, y1), (x2, y2), (x3, y3) => by
    apply Prod.ext
    · change clAdd (clMul (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2)))) x3)
                   (clSmul c (clMul (clAdd (clMul x1 y2) (clMul y1 (clInvol x2))) (clInvol y3))) =
             clAdd (clMul x1 (clAdd (clMul x2 x3) (clSmul c (clMul y2 (clInvol y3)))))
                   (clSmul c (clMul y1 (clInvol (clAdd (clMul x2 y3) (clMul y2 (clInvol x3))))))
      rw [clRight_distrib, clRight_distrib, clSmul_add,
          clLeft_distrib, clInvol_add, clLeft_distrib, clSmul_add,
          clInvol_mul x2 y3, clInvol_mul y2 (clInvol x3), clInvol_invol x3,
          clSmul_mul_left, clSmul_mul_right,
          clMul_assoc x1 x2 x3, clMul_assoc y1 (clInvol y2) x3,
          clMul_assoc x1 y2 (clInvol y3), clMul_assoc y1 (clInvol x2) (clInvol y3)]
      -- LHS is `(A + B) + (C + D)`, RHS is `(A + C) + (D + B)`:
      let A := clMul x1 (clMul x2 x3)
      let B := clSmul c (clMul y1 (clMul (clInvol y2) x3))
      let C := clSmul c (clMul x1 (clMul y2 (clInvol y3)))
      let D := clSmul c (clMul y1 (clMul (clInvol x2) (clInvol y3)))
      change clAdd (clAdd A B) (clAdd C D) = clAdd (clAdd A C) (clAdd D B)
      rw [clAdd_four_swap A B C D, clAdd_comm B D]
    · change clAdd (clMul (clAdd (clMul x1 x2) (clSmul c (clMul y1 (clInvol y2)))) y3)
                   (clMul (clAdd (clMul x1 y2) (clMul y1 (clInvol x2))) (clInvol x3)) =
             clAdd (clMul x1 (clAdd (clMul x2 y3) (clMul y2 (clInvol x3))))
                   (clMul y1 (clInvol (clAdd (clMul x2 x3) (clSmul c (clMul y2 (clInvol y3))))))
      rw [clRight_distrib, clRight_distrib,
          clLeft_distrib, clInvol_add, clInvol_smul, clInvol_mul x2 x3,
          clInvol_mul y2 (clInvol y3), clInvol_invol y3, clLeft_distrib,
          clSmul_mul_left, clSmul_mul_right,
          clMul_assoc x1 x2 y3, clMul_assoc y1 (clInvol y2) y3,
          clMul_assoc x1 y2 (clInvol x3), clMul_assoc y1 (clInvol x2) (clInvol x3)]
      -- LHS is `(A + B) + (C + D)`, RHS is `(A + C) + (D + B)`:
      let A := clMul x1 (clMul x2 y3)
      let B := clSmul c (clMul y1 (clMul (clInvol y2) y3))
      let C := clMul x1 (clMul y2 (clInvol x3))
      let D := clMul y1 (clMul (clInvol x2) (clInvol x3))
      change clAdd (clAdd A B) (clAdd C D) = clAdd (clAdd A C) (clAdd D B)
      rw [clAdd_four_swap A B C D, clAdd_comm B D]

/-- Full associative unital ring structure on `Cl R g` for any commutative ring `R`. -/
instance instAssocRingCl (g : List R) : AssocRing (Cl R g) where
  zero := clZero g
  one := clOne g
  add := clAdd
  mul := clMul
  neg := clNeg
  sub := clSub
  add_assoc := clAdd_assoc
  add_comm := clAdd_comm
  zero_add := clZero_add
  add_zero := clAdd_zero
  neg_add_cancel := clNeg_add_cancel
  sub_eq_add_neg := clSub_eq_add_neg
  mul_assoc := clMul_assoc
  one_mul := clOne_mul
  mul_one := clMul_one
  left_distrib := clLeft_distrib
  right_distrib := clRight_distrib

/-! ### Step 5: Scalar embedding `scalar`, grade-1 embedding `embedVec`, and projections -/

/-- Canonical central scalar embedding `R ↪ Cl R g`. -/
def scalar (g : List R) (r : R) : Cl R g := clSmul r (clOne g)

/-- Scalar (grade-0) projection `Cl R g → R`. -/
def scalarPart : (g : List R) → Cl R g → R
  | [], r => r
  | _ :: gs, (x, _) => scalarPart gs x

theorem scalar_cons (c : R) (gs : List R) (r : R) :
    scalar (c :: gs) r = (scalar gs r, clZero gs) := by
  change (clSmul r (clOne gs), clSmul r (clZero gs)) = (scalar gs r, clZero gs)
  rw [clSmul_zero_right]
  rfl

theorem scalarPart_zero : ∀ (g : List R), scalarPart g 0 = 0
  | [] => rfl
  | _ :: gs => scalarPart_zero gs

theorem scalarPart_scalar : ∀ (g : List R) (r : R), scalarPart g (scalar g r) = r
  | [], r => (mul_one_eq r : r * 1 = r)
  | c :: gs, r => by
    rw [scalar_cons]
    exact scalarPart_scalar gs r

theorem scalar_injective {g : List R} {r s : R} (h : scalar g r = scalar g s) : r = s := by
  have h1 := congrArg (scalarPart g) h
  rw [scalarPart_scalar, scalarPart_scalar] at h1
  exact h1

theorem scalar_zero (g : List R) : scalar g 0 = 0 := by
  induction g with
  | nil => exact (zero_mul_eq (1 : R) : (0 : R) * 1 = 0)
  | cons c gs ih =>
    rw [scalar_cons, ih]
    rfl

theorem scalar_one (g : List R) : scalar g 1 = 1 := by
  induction g with
  | nil => exact (one_mul_eq (1 : R) : (1 : R) * 1 = 1)
  | cons c gs ih =>
    rw [scalar_cons, ih]
    rfl

theorem scalar_eq_zero_iff (g : List R) (r : R) : scalar g r = 0 ↔ r = 0 := by
  constructor
  · intro h
    rw [← scalar_zero g] at h
    exact scalar_injective h
  · intro h
    rw [h, scalar_zero]

theorem scalar_add (g : List R) (r s : R) :
    scalar g (r + s) = scalar g r + scalar g s :=
  clAdd_smul r s (clOne g)

theorem scalar_mul_cl (g : List R) (r : R) (z : Cl R g) :
    scalar g r * z = clSmul r z := by
  change clMul (clSmul r (clOne g)) z = clSmul r z
  rw [clSmul_mul_left, clOne_mul]

theorem cl_mul_scalar (g : List R) (z : Cl R g) (r : R) :
    z * scalar g r = clSmul r z := by
  change clMul z (clSmul r (clOne g)) = clSmul r z
  rw [clSmul_mul_right, clMul_one]

theorem scalar_mul (g : List R) (r s : R) :
    scalar g (r * s) = scalar g r * scalar g s := by
  rw [scalar_mul_cl]
  exact clSmul_smul r s (clOne g)

theorem clInvol_scalar (g : List R) (r : R) :
    clInvol (scalar g r) = scalar g r := by
  unfold scalar
  rw [clInvol_smul, clInvol_one]

theorem apow_scalar (g : List R) (r : R) : ∀ k : Nat,
    apow (scalar g r) k = scalar g (apow r k)
  | 0 => (scalar_one g).symm
  | k + 1 => by
    change apow (scalar g r) k * scalar g r = scalar g (apow r k * r)
    rw [apow_scalar g r k, scalar_mul]

theorem scalarPart_smul : ∀ (g : List R) (r : R) (z : Cl R g),
    scalarPart g (clSmul r z) = r * scalarPart g z
  | [], _, _ => rfl
  | _ :: gs, r, (x, _) => scalarPart_smul gs r x

/-- Canonical grade-1 linear embedding `Vec R g ↪ Cl R g`. -/
def embedVec : {g : List R} → Vec R g → Cl R g
  | [], _ => 0
  | _ :: gs, (x, v) => (embedVec v, scalar gs x)

/-- Grade-1 projection `Cl R g → Vec R g` serving as left inverse to `embedVec`. -/
def vecPart : (g : List R) → Cl R g → Vec R g
  | [], _ => PUnit.unit
  | _ :: gs, (x, y) => (scalarPart gs y, vecPart gs x)

theorem vecPart_zero : ∀ (g : List R), vecPart g 0 = 0
  | [] => rfl
  | _ :: gs => Prod.ext (scalarPart_zero gs) (vecPart_zero gs)

theorem vecPart_embedVec : ∀ {g : List R} (v : Vec R g), vecPart g (embedVec v) = v
  | [], PUnit.unit => rfl
  | _ :: gs, (x, v) => Prod.ext (scalarPart_scalar gs x) (vecPart_embedVec v)

theorem vecPart_smul : ∀ (g : List R) (r : R) (z : Cl R g),
    vecPart g (clSmul r z) = vsmul r (vecPart g z)
  | [], _, _ => rfl
  | _ :: gs, r, (x, y) => Prod.ext (scalarPart_smul gs r y) (vecPart_smul gs r x)

theorem embedVec_zero : ∀ (g : List R), embedVec (0 : Vec R g) = 0
  | [] => rfl
  | _ :: gs => Prod.ext (embedVec_zero gs) (scalar_zero gs)

theorem embedVec_injective {g : List R} {u w : Vec R g} (h : embedVec u = embedVec w) :
    u = w := by
  have h1 := congrArg (vecPart g) h
  rw [vecPart_embedVec, vecPart_embedVec] at h1
  exact h1

theorem embedVec_eq_zero_iff {g : List R} (v : Vec R g) :
    embedVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [← embedVec_zero g] at h
    exact embedVec_injective h
  · intro h
    rw [h, embedVec_zero]

theorem embedVec_add : ∀ {g : List R} (u w : Vec R g),
    embedVec (u + w) = embedVec u + embedVec w
  | [], _, _ => (zero_add_eq (0 : Cl R [])).symm
  | _ :: gs, (x, u), (y, w) => Prod.ext (embedVec_add u w) (scalar_add gs x y)

theorem clInvol_embedVec : ∀ {g : List R} (v : Vec R g),
    clInvol (embedVec v) = -(embedVec v)
  | [], _ => (neg_zero_eq : -(0 : Cl R []) = 0).symm
  | _ :: gs, (x, v) =>
    Prod.ext (clInvol_embedVec v) (by change clNeg (clInvol (scalar gs x)) = _; rw [clInvol_scalar]; rfl)

/-- **Fundamental Clifford Relation (`v^2 = Q_g(v) · 1`):**
    Every grade-1 vector `v : Vec R g` squares in `Cl R g` to the central scalar `quadForm g v`. -/
theorem embedVec_sq : ∀ {g : List R} (v : Vec R g),
    embedVec v * embedVec v = scalar g (quadForm g v)
  | [], PUnit.unit => by
    change (0 : Cl R []) * (0 : Cl R []) = scalar [] 0
    rw [zero_mul_eq, scalar_zero]
  | c :: gs, (x, v) => by
    rw [scalar_cons]
    apply Prod.ext
    · change (embedVec v * embedVec v) +
             clSmul c (scalar gs x * clInvol (scalar gs x)) =
             scalar gs (c * (x * x) + quadForm gs v)
      rw [embedVec_sq v, clInvol_scalar, ← scalar_mul, ← scalar_mul_cl, ← scalar_mul,
          ← scalar_add, AssocRing.add_comm]
    · change (embedVec v * scalar gs x) +
             (scalar gs x * clInvol (embedVec v)) = (0 : Cl R gs)
      rw [clInvol_embedVec, cl_mul_scalar, scalar_mul_cl]
      change clSmul x (embedVec v) + clSmul x (clNeg (embedVec v)) = 0
      rw [clSmul_neg]
      exact add_neg_cancel (clSmul x (embedVec v))

/-- **Clifford Anticommutator Identity (`u * w + w * u = 2 B_g(u, w) · 1`):**
    Derived directly from `embedVec_sq` and `polarization_identity`. -/
theorem embedVec_anticomm {g : List R} (u w : Vec R g) :
    embedVec u * embedVec w + embedVec w * embedVec u =
    scalar g ((1 + 1) * polarForm g u w) := by
  have h1 : embedVec (u + w) * embedVec (u + w) = scalar g (quadForm g (u + w)) :=
    embedVec_sq (u + w)
  rw [polarization_identity, scalar_add, scalar_add, embedVec_add] at h1
  have hexpand : (embedVec u + embedVec w) * (embedVec u + embedVec w) =
      (scalar g (quadForm g u) + scalar g (quadForm g w)) +
      (embedVec u * embedVec w + embedVec w * embedVec u) := by
    calc
      (embedVec u + embedVec w) * (embedVec u + embedVec w)
        = (embedVec u * embedVec u + embedVec u * embedVec w) +
          (embedVec w * embedVec u + embedVec w * embedVec w) := by
            rw [AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib]
      _ = (embedVec u * embedVec u + embedVec w * embedVec w) +
          (embedVec u * embedVec w + embedVec w * embedVec u) := by
            let A := embedVec u * embedVec u
            let B := embedVec u * embedVec w
            let C := embedVec w * embedVec u
            let D := embedVec w * embedVec w
            change clAdd (clAdd A B) (clAdd C D) = clAdd (clAdd A D) (clAdd B C)
            rw [clAdd_comm C D, clAdd_four_swap A B D C]
      _ = (scalar g (quadForm g u) + scalar g (quadForm g w)) +
          (embedVec u * embedVec w + embedVec w * embedVec u) := by
            rw [embedVec_sq u, embedVec_sq w]
  rw [hexpand] at h1
  exact add_left_cancel h1

/-- **Subalgebra Inclusion:** `z ↦ (z, 0)` embeds `Cl R gs` injectively as a subring of `Cl R (c :: gs)`. -/
def embedSub (c : R) {gs : List R} (z : Cl R gs) : Cl R (c :: gs) :=
  (z, 0)

theorem embedSub_ne_zero {c : R} {gs : List R} {z : Cl R gs} (hz : z ≠ 0) :
    embedSub c z ≠ 0 := by
  intro h0
  injection h0 with hz0 _
  exact hz hz0

theorem embedSub_mul (c : R) {gs : List R} (z w : Cl R gs) :
    embedSub c z * embedSub c w = embedSub c (z * w) := by
  apply Prod.ext
  · change clAdd (z * w) (clSmul c (clMul (clZero gs) (clInvol (clZero gs)))) = z * w
    rw [clZero_mul, clSmul_zero_right, clAdd_zero]
  · change clAdd (clMul z (clZero gs)) (clMul (clZero gs) (clInvol w)) = clZero gs
    rw [clMul_zero, clZero_mul, clAdd_zero]

theorem embedSub_sq_zero {c : R} {gs : List R} {z : Cl R gs} (hz : IsSqZero z) :
    IsSqZero (embedSub c z) := by
  unfold IsSqZero at *
  rw [embedSub_mul, hz]
  rfl

end CliffordRing

section Grade1PositiveTheorems

variable {R : Type u} [IntegralDomain R]

private theorem apow_embedVec_even {g : List R} (v : Vec R g) : ∀ m : Nat,
    apow (embedVec v) (2 * m) = scalar g (apow (quadForm g v) m)
  | 0 => (scalar_one g).symm
  | m + 1 => by
    have hsplit : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hsplit, apow_add, apow_two, apow_embedVec_even v m, embedVec_sq, ← scalar_mul]
    rfl

private theorem apow_embedVec_odd {g : List R} (v : Vec R g) : ∀ m : Nat,
    apow (embedVec v) (2 * m + 1) = clSmul (apow (quadForm g v) m) (embedVec v)
  | m => by
    rw [apow_add, apow_one, apow_embedVec_even v m, scalar_mul_cl]

/-- **Positive Theorem 1A (Grade-1 Square-Zero ↔ Isotropic):**
    Over any integral domain `R` and any quadratic form `g`, a grade-1 Clifford vector
    `embedVec v` is nonzero and square-zero if and only if `v` is a nonzero isotropic vector. -/
theorem grade1_sq_zero_iff {g : List R} (v : Vec R g) :
    (embedVec v ≠ 0 ∧ IsSqZero (embedVec v)) ↔ IsIsotropic g v := by
  unfold IsSqZero IsIsotropic
  rw [embedVec_sq, scalar_eq_zero_iff]
  constructor
  · intro ⟨hev, hq⟩
    exact ⟨fun hv0 => hev ((embedVec_eq_zero_iff v).mpr hv0), hq⟩
  · intro ⟨hv, hq⟩
    exact ⟨fun hev0 => hv ((embedVec_eq_zero_iff v).mp hev0), hq⟩

/-- **Positive Theorem 1B (Grade-1 Nilpotent of Arbitrary Index `k ≥ 1` ↔ Isotropic):**
    Over any integral domain `R`, even higher-index nilpotency `(embedVec v)^k = 0` (`k ≥ 1`)
    for a nonzero grade-1 vector `v` collapses to `Q_g(v) = 0`. -/
theorem grade1_nilpotent_iff {g : List R} (v : Vec R g) :
    (embedVec v ≠ 0 ∧ IsNilpotent (embedVec v)) ↔ IsIsotropic g v := by
  constructor
  · intro ⟨hev, k, hk1, hpow⟩
    have hv : v ≠ 0 := fun hv0 => hev ((embedVec_eq_zero_iff v).mpr hv0)
    refine ⟨hv, ?_⟩
    by_cases hpar : k % 2 = 0
    · let m := k / 2
      have hm_eq : k = 2 * m := by omega
      have hm_ge : m ≥ 1 := by omega
      rw [hm_eq, apow_embedVec_even] at hpow
      have hqm : apow (quadForm g v) m = 0 := (scalar_eq_zero_iff g _).mp hpow
      exact (apow_eq_zero_iff (quadForm g v) hm_ge).mp hqm
    · let m := k / 2
      have hm_eq : k = 2 * m + 1 := by omega
      rw [hm_eq, apow_embedVec_odd] at hpow
      have hvp := congrArg (vecPart g) hpow
      rw [vecPart_smul, vecPart_embedVec, vecPart_zero] at hvp
      have hqm : apow (quadForm g v) m = 0 := vsmul_eq_zero_of_ne_zero hv hvp
      match m with
      | 0 =>
        change (1 : R) = 0 at hqm
        exact False.elim (IntegralDomain.zero_ne_one hqm.symm)
      | m' + 1 =>
        exact (apow_eq_zero_iff (quadForm g v) (by omega)).mp hqm
  · intro hiso
    have ⟨hev, hsq⟩ := (grade1_sq_zero_iff v).mpr hiso
    exact ⟨hev, isNilpotent_of_isSqZero hsq⟩

/-- Under the opposite Clifford sign convention `v^2 = -Q_g(v) · 1` (modeled by `negSig g`),
    grade-1 nilpotency is still equivalent to `v` being `Q_g`-isotropic. -/
theorem grade1_nilpotent_negSig_iff {g : List R} (v : Vec R g) :
    (embedVec (toNegSig v) ≠ 0 ∧ IsNilpotent (embedVec (toNegSig v))) ↔ IsIsotropic g v := by
  rw [grade1_nilpotent_iff]
  unfold IsIsotropic
  rw [quadForm_negSig]
  constructor
  · intro ⟨hne, hnq⟩
    refine ⟨fun hv0 => hne (by rw [hv0, toNegSig_zero]), eq_zero_of_neg_eq_zero hnq⟩
  · intro ⟨hv, hq⟩
    refine ⟨fun h0 => hv (toNegSig_injective (by rw [h0, ← toNegSig_zero g])), ?_⟩
    rw [hq, neg_zero_eq]

end Grade1PositiveTheorems

/-- **Combined Grade-1 Signature Theorem:**
    Over any ordered integral domain `R`, `Cl_{p,q}(R)` admits a nonzero **grade-1** nilpotent
    element if and only if the signature `(p, q)` is indefinite (`p ≥ 1 ∧ q ≥ 1`). -/
theorem grade1_nilpotent_exists_iff_indefinite {R : Type u} [OrderedDomain R] (p q : Nat) :
    (∃ v : Vec R (sigList R p q), embedVec v ≠ 0 ∧ IsNilpotent (embedVec v)) ↔
    (p ≥ 1 ∧ q ≥ 1) := by
  rw [← hasIsotropic_sigList_iff (R := R) p q]
  unfold HasIsotropic
  constructor
  · intro ⟨v, hv⟩
    exact ⟨v, (grade1_nilpotent_iff v).mp hv⟩
  · intro ⟨v, hv⟩
    exact ⟨v, (grade1_nilpotent_iff v).mpr hv⟩

end Conjecture00000007624
