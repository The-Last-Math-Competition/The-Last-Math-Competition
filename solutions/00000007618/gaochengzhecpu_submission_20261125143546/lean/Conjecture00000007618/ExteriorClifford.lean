/-
  Conjecture 00000007618 — Constructive 2^n-Dimensional Exterior & Clifford Algebra
  Core Lean 4.19.0 only (zero external dependencies).

  Constructs `Cl R n` recursively over any commutative ring `CRing R` and orthogonal
  quadratic form `q : Fin n → R`:
    Cl R 0       = R
    Cl R (n + 1) = Cl R n × Cl R n   (representing `a + b · e_n`)
  Establishes associative unital ring laws, exterior wedge product `wedge`,
  grade involution `invol`, Clifford reversion `rev`, homogeneous grading `HasGrade`,
  action of `invol` and `rev` on homogeneous grades, and graded anticommutativity
  `B ∧ A = (-1)^{r s} (A ∧ B)` for all `n, r, s : Nat`.
-/

import Conjecture00000007618.Ring

namespace Conjecture00000007618

/-- Underlying `2^n`-dimensional module of the Clifford and exterior algebras over `R`. -/
abbrev Cl (R : Type) : Nat → Type
  | 0 => R
  | n + 1 => Cl R n × Cl R n

/-- Restrict a metric on `Fin (n + 1)` to the first `n` coordinates. -/
def initMetric {R : Type} {n : Nat} (q : Fin (n + 1) → R) : Fin n → R :=
  fun i => q ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- Last coordinate `q(n)` of a metric on `Fin (n + 1)`. -/
def lastMetric {R : Type} {n : Nat} (q : Fin (n + 1) → R) : R :=
  q ⟨n, Nat.lt_succ_self n⟩

namespace Cl

section AlgebraOps
variable {R : Type} [CRing R]

def zero : (n : Nat) → Cl R n
  | 0 => CRing.zero
  | n + 1 => (zero n, zero n)

def one : (n : Nat) → Cl R n
  | 0 => CRing.one
  | n + 1 => (one n, zero n)

/-- Canonical oriented basis volume blade `ω_n = e_0 ∧ e_1 ∧ ... ∧ e_{n-1}`. -/
def omega : (n : Nat) → Cl R n
  | 0 => CRing.one
  | n + 1 => (zero n, omega n)

def add : (n : Nat) → Cl R n → Cl R n → Cl R n
  | 0, a, b => CRing.add a b
  | n + 1, x, y => (add n x.1 y.1, add n x.2 y.2)

def neg : (n : Nat) → Cl R n → Cl R n
  | 0, a => CRing.neg a
  | n + 1, x => (neg n x.1, neg n x.2)

def sub (n : Nat) (x y : Cl R n) : Cl R n :=
  add n x (neg n y)

def smul : (n : Nat) → R → Cl R n → Cl R n
  | 0, r, a => CRing.mul r a
  | n + 1, r, x => (smul n r x.1, smul n r x.2)

/-- Grade involution `x̂` (`(-1)^k` on grade `k`). -/
def invol : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, x => (invol n x.1, neg n (invol n x.2))

/-- Clifford reversion `x̃` (`(-1)^{k(k-1)/2}` on grade `k`). -/
def rev : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, x => (rev n x.1, invol n (rev n x.2))

/-- Geometric product in `Cl(R^n, q)` for orthogonal quadratic form `q : Fin n → R`. -/
def mul : {n : Nat} → (Fin n → R) → Cl R n → Cl R n → Cl R n
  | 0, _, a, c => CRing.mul a c
  | n + 1, q, x, y =>
      let q' := initMetric q
      let qn := lastMetric q
      ( add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2))),
        add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)) )

/-- Identically zero metric giving the exterior algebra `Λ(R^n) = Cl(R^n, 0)`. -/
def zeroMetric (n : Nat) : Fin n → R :=
  fun _ => CRing.zero

/-- Standard positive-definite Euclidean metric `q_i = 1`. -/
def euclMetric (n : Nat) : Fin n → R :=
  fun _ => CRing.one

/-- Exterior wedge (join) product `x ∧ y`, realized as the `q = 0` Clifford product. -/
def wedge (n : Nat) (x y : Cl R n) : Cl R n :=
  mul (zeroMetric (R := R) n) x y

/-- Induced determinant bilinear form `⟨x, y⟩_q` on `Λ(R^n) ≅ Cl(R^n, q)`. -/
def inner : {n : Nat} → (Fin n → R) → Cl R n → Cl R n → R
  | 0, _, a, c => CRing.mul a c
  | _ + 1, q, x, y =>
      CRing.add (inner (initMetric q) x.1 y.1)
        (CRing.mul (lastMetric q) (inner (initMetric q) x.2 y.2))

/-- Discriminant product `∏_{i=0}^{n-1} q(i)`. -/
def prodMetric : {n : Nat} → (Fin n → R) → R
  | 0, _ => CRing.one
  | _ + 1, q => CRing.mul (prodMetric (initMetric q)) (lastMetric q)

/-- Standard basis vector `e_i ∈ Λ^1(R^n)`. -/
def basisVec : (n : Nat) → Fin n → Cl R n
  | 0, i => Fin.elim0 i
  | n + 1, ⟨k, _⟩ =>
      if h : k < n then
        (basisVec n ⟨k, h⟩, zero n)
      else
        (zero n, one n)

/-- Scalar (grade-0) part extraction. -/
def scalarPart : (n : Nat) → Cl R n → R
  | 0, a => a
  | n + 1, x => scalarPart n x.1

/-- Top-grade (`ω_n` bracket) coefficient extraction. -/
def topPart : (n : Nat) → Cl R n → R
  | 0, a => a
  | n + 1, x => topPart n x.2

/-- Homogeneous grade predicate `x ∈ Λ^k(R^n)`. -/
def HasGrade : (n : Nat) → Nat → Cl R n → Prop
  | 0, 0, _ => True
  | 0, _ + 1, x => x = CRing.zero
  | n + 1, 0, (a, b) => HasGrade n 0 a ∧ b = zero n
  | n + 1, k + 1, (a, b) => HasGrade n (k + 1) a ∧ HasGrade n k b

/-! ### Module Laws -/

theorem add_assoc : ∀ (n : Nat) (x y z : Cl R n), add n (add n x y) z = add n x (add n y z)
  | 0, x, y, z => CRing.add_assoc x y z
  | n + 1, (_, _), (_, _), (_, _) => Prod.ext (add_assoc n _ _ _) (add_assoc n _ _ _)

theorem add_comm : ∀ (n : Nat) (x y : Cl R n), add n x y = add n y x
  | 0, x, y => CRing.add_comm x y
  | n + 1, (_, _), (_, _) => Prod.ext (add_comm n _ _) (add_comm n _ _)

theorem zero_add : ∀ (n : Nat) (x : Cl R n), add n (zero n) x = x
  | 0, x => CRing.zero_add x
  | n + 1, (_, _) => Prod.ext (zero_add n _) (zero_add n _)

theorem add_zero (n : Nat) (x : Cl R n) : add n x (zero n) = x := by
  rw [add_comm, zero_add]

theorem add_left_neg : ∀ (n : Nat) (x : Cl R n), add n (neg n x) x = zero n
  | 0, x => CRing.add_left_neg x
  | n + 1, (_, _) => Prod.ext (add_left_neg n _) (add_left_neg n _)

theorem add_right_neg (n : Nat) (x : Cl R n) : add n x (neg n x) = zero n := by
  rw [add_comm, add_left_neg]

theorem add_left_cancel {n : Nat} {x y z : Cl R n} (h : add n x y = add n x z) : y = z := by
  have h1 : add n (neg n x) (add n x y) = add n (neg n x) (add n x z) := congrArg (add n (neg n x)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem sub_eq_zero {n : Nat} {x y : Cl R n} : sub n x y = zero n ↔ x = y := by
  constructor
  · intro h
    apply add_left_cancel (x := neg n y)
    rw [add_comm n (neg n y) x, add_left_neg]
    exact h
  · intro h
    subst h
    exact add_right_neg n x

theorem neg_zero : ∀ (n : Nat), neg n (zero (R := R) n) = zero n
  | 0 => CRing.neg_zero
  | n + 1 => Prod.ext (neg_zero n) (neg_zero n)

theorem neg_neg : ∀ (n : Nat) (x : Cl R n), neg n (neg n x) = x
  | 0, x => CRing.neg_neg x
  | n + 1, (_, _) => Prod.ext (neg_neg n _) (neg_neg n _)

theorem neg_add : ∀ (n : Nat) (x y : Cl R n), neg n (add n x y) = add n (neg n x) (neg n y)
  | 0, x, y => CRing.neg_add x y
  | n + 1, (_, _), (_, _) => Prod.ext (neg_add n _ _) (neg_add n _ _)

theorem add_add_add_comm (n : Nat) (a b c d : Cl R n) :
    add n (add n a b) (add n c d) = add n (add n a c) (add n b d) := by
  rw [add_assoc, add_assoc, ← add_assoc n b c d, add_comm n b c, add_assoc n c b d]

theorem smul_zero : ∀ (n : Nat) (r : R), smul n r (zero n) = zero n
  | 0, r => CRing.mul_zero r
  | n + 1, r => Prod.ext (smul_zero n r) (smul_zero n r)

theorem zero_smul : ∀ (n : Nat) (x : Cl R n), smul n CRing.zero x = zero n
  | 0, x => CRing.zero_mul x
  | n + 1, (_, _) => Prod.ext (zero_smul n _) (zero_smul n _)

theorem one_smul : ∀ (n : Nat) (x : Cl R n), smul n CRing.one x = x
  | 0, x => CRing.one_mul x
  | n + 1, (_, _) => Prod.ext (one_smul n _) (one_smul n _)

theorem neg_one_smul : ∀ (n : Nat) (x : Cl R n), smul n (CRing.neg CRing.one) x = neg n x
  | 0, x => by show CRing.mul (CRing.neg CRing.one) x = CRing.neg x; rw [CRing.neg_mul, CRing.one_mul]
  | n + 1, (_, _) => Prod.ext (neg_one_smul n _) (neg_one_smul n _)

theorem smul_add : ∀ (n : Nat) (r : R) (x y : Cl R n),
    smul n r (add n x y) = add n (smul n r x) (smul n r y)
  | 0, r, x, y => CRing.left_distrib r x y
  | n + 1, r, (_, _), (_, _) => Prod.ext (smul_add n r _ _) (smul_add n r _ _)

theorem add_smul : ∀ (n : Nat) (r s : R) (x : Cl R n),
    smul n (CRing.add r s) x = add n (smul n r x) (smul n s x)
  | 0, r, s, x => CRing.right_distrib r s x
  | n + 1, r, s, (_, _) => Prod.ext (add_smul n r s _) (add_smul n r s _)

theorem smul_smul : ∀ (n : Nat) (r s : R) (x : Cl R n),
    smul n r (smul n s x) = smul n (CRing.mul r s) x
  | 0, r, s, x => (CRing.mul_assoc r s x).symm
  | n + 1, r, s, (_, _) => Prod.ext (smul_smul n r s _) (smul_smul n r s _)

theorem smul_neg : ∀ (n : Nat) (r : R) (x : Cl R n),
    smul n r (neg n x) = neg n (smul n r x)
  | 0, r, x => CRing.mul_neg r x
  | n + 1, r, (_, _) => Prod.ext (smul_neg n r _) (smul_neg n r _)

theorem neg_smul : ∀ (n : Nat) (r : R) (x : Cl R n),
    smul n (CRing.neg r) x = neg n (smul n r x)
  | 0, r, x => CRing.neg_mul r x
  | n + 1, r, (_, _) => Prod.ext (neg_smul n r _) (neg_smul n r _)

/-! ### Involution & Reversion Laws -/

theorem invol_zero : ∀ (n : Nat), invol n (zero (R := R) n) = zero n
  | 0 => rfl
  | n + 1 => Prod.ext (invol_zero n) (by show neg n (invol n (zero n)) = zero n; rw [invol_zero, neg_zero])

theorem invol_one : ∀ (n : Nat), invol n (one (R := R) n) = one n
  | 0 => rfl
  | n + 1 => Prod.ext (invol_one n) (by show neg n (invol n (zero n)) = zero n; rw [invol_zero, neg_zero])

theorem invol_add : ∀ (n : Nat) (x y : Cl R n),
    invol n (add n x y) = add n (invol n x) (invol n y)
  | 0, _, _ => rfl
  | n + 1, (a, b), (c, d) =>
      Prod.ext (invol_add n a c)
        (by show neg n (invol n (add n b d)) = add n (neg n (invol n b)) (neg n (invol n d))
            rw [invol_add n b d, neg_add])

theorem invol_neg : ∀ (n : Nat) (x : Cl R n), invol n (neg n x) = neg n (invol n x)
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (invol_neg n a)
        (by show neg n (invol n (neg n b)) = neg n (neg n (invol n b))
            rw [invol_neg n b])

theorem invol_smul : ∀ (n : Nat) (r : R) (x : Cl R n),
    invol n (smul n r x) = smul n r (invol n x)
  | 0, _, _ => rfl
  | n + 1, r, (a, b) =>
      Prod.ext (invol_smul n r a)
        (by show neg n (invol n (smul n r b)) = smul n r (neg n (invol n b))
            rw [invol_smul n r b, smul_neg])

theorem invol_invol : ∀ (n : Nat) (x : Cl R n), invol n (invol n x) = x
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (invol_invol n a)
        (by show neg n (invol n (neg n (invol n b))) = b
            rw [invol_neg, neg_neg, invol_invol])

theorem rev_zero : ∀ (n : Nat), rev n (zero (R := R) n) = zero n
  | 0 => rfl
  | n + 1 => Prod.ext (rev_zero n) (by show invol n (rev n (zero n)) = zero n; rw [rev_zero, invol_zero])

theorem rev_one : ∀ (n : Nat), rev n (one (R := R) n) = one n
  | 0 => rfl
  | n + 1 => Prod.ext (rev_one n) (by show invol n (rev n (zero n)) = zero n; rw [rev_zero, invol_zero])

theorem rev_add : ∀ (n : Nat) (x y : Cl R n),
    rev n (add n x y) = add n (rev n x) (rev n y)
  | 0, _, _ => rfl
  | n + 1, (a, b), (c, d) =>
      Prod.ext (rev_add n a c)
        (by show invol n (rev n (add n b d)) = add n (invol n (rev n b)) (invol n (rev n d))
            rw [rev_add n b d, invol_add])

theorem rev_neg : ∀ (n : Nat) (x : Cl R n), rev n (neg n x) = neg n (rev n x)
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (rev_neg n a)
        (by show invol n (rev n (neg n b)) = neg n (invol n (rev n b))
            rw [rev_neg n b, invol_neg])

theorem rev_smul : ∀ (n : Nat) (r : R) (x : Cl R n),
    rev n (smul n r x) = smul n r (rev n x)
  | 0, _, _ => rfl
  | n + 1, r, (a, b) =>
      Prod.ext (rev_smul n r a)
        (by show invol n (rev n (smul n r b)) = smul n r (invol n (rev n b))
            rw [rev_smul n r b, invol_smul])

theorem rev_invol : ∀ (n : Nat) (x : Cl R n), rev n (invol n x) = invol n (rev n x)
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (rev_invol n a)
        (by show invol n (rev n (neg n (invol n b))) = neg n (invol n (invol n (rev n b)))
            rw [rev_neg, rev_invol n b, invol_neg])

theorem rev_rev : ∀ (n : Nat) (x : Cl R n), rev n (rev n x) = x
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (rev_rev n a)
        (by show invol n (rev n (invol n (rev n b))) = b
            rw [rev_invol, invol_invol, rev_rev])

/-! ### Ring & Exterior Multiplication Laws -/

theorem zero_mul : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q (zero n) x = zero n
  | 0, _, x => CRing.zero_mul x
  | n + 1, q, (c, d) => by
      show (add n (mul (initMetric q) (zero n) c)
                  (smul n (lastMetric q) (mul (initMetric q) (zero n) (invol n d))),
            add n (mul (initMetric q) (zero n) d)
                  (mul (initMetric q) (zero n) (invol n c))) = (zero n, zero n)
      rw [zero_mul, zero_mul, smul_zero, add_zero, zero_mul, zero_mul, add_zero]

theorem mul_zero : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q x (zero n) = zero n
  | 0, _, x => CRing.mul_zero x
  | n + 1, q, (a, b) => by
      show (add n (mul (initMetric q) a (zero n))
                  (smul n (lastMetric q) (mul (initMetric q) b (invol n (zero n)))),
            add n (mul (initMetric q) a (zero n))
                  (mul (initMetric q) b (invol n (zero n)))) = (zero n, zero n)
      rw [invol_zero, mul_zero, mul_zero, smul_zero, add_zero]

theorem one_mul : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q (one n) x = x
  | 0, _, x => CRing.one_mul x
  | n + 1, q, (c, d) => by
      show (add n (mul (initMetric q) (one n) c)
                  (smul n (lastMetric q) (mul (initMetric q) (zero n) (invol n d))),
            add n (mul (initMetric q) (one n) d)
                  (mul (initMetric q) (zero n) (invol n c))) = (c, d)
      rw [one_mul, zero_mul, smul_zero, add_zero, one_mul, zero_mul, add_zero]

theorem mul_one : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q x (one n) = x
  | 0, _, x => CRing.mul_one x
  | n + 1, q, (a, b) => by
      show (add n (mul (initMetric q) a (one n))
                  (smul n (lastMetric q) (mul (initMetric q) b (invol n (zero n)))),
            add n (mul (initMetric q) a (zero n))
                  (mul (initMetric q) b (invol n (one n)))) = (a, b)
      rw [invol_zero, invol_one, mul_one, mul_zero, mul_zero, smul_zero, add_zero, zero_add, mul_one]

theorem left_distrib : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q x (add n y z) = add n (mul q x y) (mul q x z)
  | 0, _, x, y, z => CRing.left_distrib x y z
  | n + 1, q, (a, b), (c, d), (e, f) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show add n (mul q' a (add n c e)) (smul n qn (mul q' b (invol n (add n d f)))) =
             add n (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
                   (add n (mul q' a e) (smul n qn (mul q' b (invol n f))))
        rw [invol_add, left_distrib q', left_distrib q', smul_add, add_add_add_comm]
      · show add n (mul q' a (add n d f)) (mul q' b (invol n (add n c e))) =
             add n (add n (mul q' a d) (mul q' b (invol n c)))
                   (add n (mul q' a f) (mul q' b (invol n e)))
        rw [invol_add, left_distrib q', left_distrib q', add_add_add_comm]

theorem right_distrib : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q (add n x y) z = add n (mul q x z) (mul q y z)
  | 0, _, x, y, z => CRing.right_distrib x y z
  | n + 1, q, (a, b), (c, d), (e, f) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show add n (mul q' (add n a c) e) (smul n qn (mul q' (add n b d) (invol n f))) =
             add n (add n (mul q' a e) (smul n qn (mul q' b (invol n f))))
                   (add n (mul q' c e) (smul n qn (mul q' d (invol n f))))
        rw [right_distrib q', right_distrib q', smul_add, add_add_add_comm]
      · show add n (mul q' (add n a c) f) (mul q' (add n b d) (invol n e)) =
             add n (add n (mul q' a f) (mul q' b (invol n e)))
                   (add n (mul q' c f) (mul q' d (invol n e)))
        rw [right_distrib q', right_distrib q', add_add_add_comm]

theorem smul_mul : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    mul q (smul n r x) y = smul n r (mul q x y)
  | 0, _, r, x, y => CRing.mul_assoc r x y
  | n + 1, q, r, (a, b), (c, d) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show add n (mul q' (smul n r a) c) (smul n qn (mul q' (smul n r b) (invol n d))) =
             smul n r (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
        rw [smul_mul q', smul_mul q', smul_add, smul_smul, smul_smul, CRing.mul_comm qn r]
      · show add n (mul q' (smul n r a) d) (mul q' (smul n r b) (invol n c)) =
             smul n r (add n (mul q' a d) (mul q' b (invol n c)))
        rw [smul_mul q', smul_mul q', smul_add]

theorem mul_smul : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    mul q x (smul n r y) = smul n r (mul q x y)
  | 0, _, r, x, y => by
      show CRing.mul x (CRing.mul r y) = CRing.mul r (CRing.mul x y)
      rw [← CRing.mul_assoc, CRing.mul_comm x r, CRing.mul_assoc]
  | n + 1, q, r, (a, b), (c, d) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show add n (mul q' a (smul n r c)) (smul n qn (mul q' b (invol n (smul n r d)))) =
             smul n r (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
        rw [invol_smul, mul_smul q', mul_smul q', smul_add, smul_smul, smul_smul, CRing.mul_comm qn r]
      · show add n (mul q' a (smul n r d)) (mul q' b (invol n (smul n r c))) =
             smul n r (add n (mul q' a d) (mul q' b (invol n c)))
        rw [invol_smul, mul_smul q', mul_smul q', smul_add]

theorem mul_neg : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    mul q x (neg n y) = neg n (mul q x y) := by
  intro n q x y
  rw [← neg_one_smul n y, mul_smul, neg_one_smul]

theorem neg_mul : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    mul q (neg n x) y = neg n (mul q x y) := by
  intro n q x y
  rw [← neg_one_smul n x, smul_mul, neg_one_smul]

theorem invol_mul : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    invol n (mul q x y) = mul q (invol n x) (invol n y)
  | 0, _, _, _ => rfl
  | n + 1, q, (a, b), (c, d) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show invol n (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) =
             add n (mul q' (invol n a) (invol n c))
                   (smul n qn (mul q' (neg n (invol n b)) (invol n (neg n (invol n d)))))
        rw [invol_add, invol_smul, invol_mul q', invol_mul q', invol_neg, neg_mul, mul_neg, neg_neg]
      · show neg n (invol n (add n (mul q' a d) (mul q' b (invol n c)))) =
             add n (mul q' (invol n a) (neg n (invol n d)))
                   (mul q' (neg n (invol n b)) (invol n (invol n c)))
        rw [invol_add, neg_add, invol_mul q', invol_mul q', mul_neg, neg_mul]

theorem mul_assoc : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q (mul q x y) z = mul q x (mul q y z)
  | 0, _, x, y, z => CRing.mul_assoc x y z
  | n + 1, q, (a, b), (c, d), (e, f) => by
      let q' := initMetric q
      let qn := lastMetric q
      apply Prod.ext
      · show add n (mul q' (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) e)
                   (smul n qn (mul q' (add n (mul q' a d) (mul q' b (invol n c))) (invol n f))) =
             add n (mul q' a (add n (mul q' c e) (smul n qn (mul q' d (invol n f)))))
                   (smul n qn (mul q' b (invol n (add n (mul q' c f) (mul q' d (invol n e))))))
        rw [right_distrib q', right_distrib q', smul_add,
            left_distrib q', invol_add, left_distrib q', smul_add,
            smul_mul q', mul_smul q', invol_mul q', invol_mul q', invol_invol,
            mul_assoc q', mul_assoc q', mul_assoc q', mul_assoc q']
        rw [add_assoc, add_assoc,
            ← add_assoc n (smul n qn (mul q' b (mul q' (invol n d) e))) _ _,
            add_comm n (smul n qn (mul q' b (mul q' (invol n d) e)))
                       (smul n qn (mul q' a (mul q' d (invol n f)))),
            add_assoc n (smul n qn (mul q' a (mul q' d (invol n f)))) _ _,
            add_comm n (smul n qn (mul q' b (mul q' (invol n d) e)))
                       (smul n qn (mul q' b (mul q' (invol n c) (invol n f))))]
      · show add n (mul q' (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) f)
                   (mul q' (add n (mul q' a d) (mul q' b (invol n c))) (invol n e)) =
             add n (mul q' a (add n (mul q' c f) (mul q' d (invol n e))))
                   (mul q' b (invol n (add n (mul q' c e) (smul n qn (mul q' d (invol n f))))))
        rw [right_distrib q', right_distrib q', left_distrib q',
            invol_add, invol_smul, left_distrib q',
            smul_mul q', mul_smul q', invol_mul q', invol_mul q', invol_invol,
            mul_assoc q', mul_assoc q', mul_assoc q', mul_assoc q']
        rw [add_assoc, add_assoc,
            ← add_assoc n (smul n qn (mul q' b (mul q' (invol n d) f))) _ _,
            add_comm n (smul n qn (mul q' b (mul q' (invol n d) f)))
                       (mul q' a (mul q' d (invol n e))),
            add_assoc n (mul q' a (mul q' d (invol n e))) _ _,
            add_comm n (smul n qn (mul q' b (mul q' (invol n d) f)))
                       (mul q' b (mul q' (invol n c) (invol n e)))]

/-! ### Exterior Wedge Specializations -/

theorem initMetric_zeroMetric (n : Nat) :
    initMetric (zeroMetric (R := R) (n + 1)) = zeroMetric n := rfl

theorem wedge_step (n : Nat) (a b c d : Cl R n) :
    wedge (n + 1) (a, b) (c, d) =
      (wedge n a c, add n (wedge n a d) (wedge n b (invol n c))) := by
  unfold wedge
  show (add n (mul (zeroMetric n) a c) (smul n CRing.zero (mul (zeroMetric n) b (invol n d))),
        add n (mul (zeroMetric n) a d) (mul (zeroMetric n) b (invol n c))) = _
  rw [zero_smul, add_zero]

theorem zero_wedge (n : Nat) (x : Cl R n) : wedge n (zero n) x = zero n :=
  zero_mul (zeroMetric n) x

theorem wedge_zero (n : Nat) (x : Cl R n) : wedge n x (zero n) = zero n :=
  mul_zero (zeroMetric n) x

theorem one_wedge (n : Nat) (x : Cl R n) : wedge n (one n) x = x :=
  one_mul (zeroMetric n) x

theorem wedge_one (n : Nat) (x : Cl R n) : wedge n x (one n) = x :=
  mul_one (zeroMetric n) x

theorem wedge_add_left (n : Nat) (x y z : Cl R n) :
    wedge n (add n x y) z = add n (wedge n x z) (wedge n y z) :=
  right_distrib (zeroMetric n) x y z

theorem wedge_add_right (n : Nat) (x y z : Cl R n) :
    wedge n x (add n y z) = add n (wedge n x y) (wedge n x z) :=
  left_distrib (zeroMetric n) x y z

theorem smul_wedge (n : Nat) (r : R) (x y : Cl R n) :
    wedge n (smul n r x) y = smul n r (wedge n x y) :=
  smul_mul (zeroMetric n) r x y

theorem wedge_smul (n : Nat) (r : R) (x y : Cl R n) :
    wedge n x (smul n r y) = smul n r (wedge n x y) :=
  mul_smul (zeroMetric n) r x y

theorem wedge_assoc (n : Nat) (x y z : Cl R n) :
    wedge n (wedge n x y) z = wedge n x (wedge n y z) :=
  mul_assoc (zeroMetric n) x y z

/-! ### Grading, Involution Action, Reversion Action & Graded Anticommutativity -/

theorem hasGrade_zero : ∀ (n k : Nat), HasGrade n k (zero (R := R) n)
  | 0, 0 => trivial
  | 0, _ + 1 => rfl
  | n + 1, 0 => ⟨hasGrade_zero n 0, rfl⟩
  | n + 1, k + 1 => ⟨hasGrade_zero n (k + 1), hasGrade_zero n k⟩

theorem hasGrade_one : ∀ (n : Nat), HasGrade n 0 (one (R := R) n)
  | 0 => trivial
  | n + 1 => ⟨hasGrade_one n, rfl⟩

theorem hasGrade_gt_zero : ∀ (n k : Nat), n < k → ∀ (x : Cl R n), HasGrade n k x → x = zero n
  | 0, 0, hlt, _, _ => absurd hlt (Nat.lt_irrefl 0)
  | 0, _ + 1, _, _, hx => hx
  | _ + 1, 0, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, k + 1, hlt, (a, b), ⟨ha, hb⟩ => by
      have hk : n < k := Nat.lt_of_succ_lt_succ hlt
      have hk1 : n < k + 1 := Nat.lt_succ_of_lt hk
      exact Prod.ext (hasGrade_gt_zero n (k + 1) hk1 a ha) (hasGrade_gt_zero n k hk b hb)

theorem hasGrade_omega : ∀ (n : Nat), HasGrade n n (omega (R := R) n)
  | 0 => trivial
  | n + 1 => ⟨hasGrade_zero n (n + 1), hasGrade_omega n⟩

theorem hasGrade_basisVec : ∀ (n : Nat) (i : Fin n), HasGrade n 1 (basisVec (R := R) n i)
  | 0, i => Fin.elim0 i
  | n + 1, ⟨k, hk⟩ => by
      unfold basisVec
      split
      · next hlt => exact ⟨hasGrade_basisVec n ⟨k, hlt⟩, hasGrade_zero n 0⟩
      · exact ⟨hasGrade_zero n 1, hasGrade_one n⟩

theorem hasGrade_add : ∀ (n k : Nat) {x y : Cl R n},
    HasGrade n k x → HasGrade n k y → HasGrade n k (add n x y)
  | 0, 0, _, _, _, _ => trivial
  | 0, _ + 1, _, _, hx, hy => by rw [hx, hy]; exact CRing.zero_add CRing.zero
  | n + 1, 0, (_, _), (_, _), ⟨ha, hb⟩, ⟨hc, hd⟩ =>
      ⟨hasGrade_add n 0 ha hc, by rw [hb, hd, add_zero]⟩
  | n + 1, k + 1, (_, _), (_, _), ⟨ha, hb⟩, ⟨hc, hd⟩ =>
      ⟨hasGrade_add n (k + 1) ha hc, hasGrade_add n k hb hd⟩

theorem hasGrade_neg : ∀ (n k : Nat) {x : Cl R n},
    HasGrade n k x → HasGrade n k (neg n x)
  | 0, 0, _, _ => trivial
  | 0, _ + 1, _, hx => by rw [hx]; exact CRing.neg_zero
  | n + 1, 0, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_neg n 0 ha, by rw [hb, neg_zero]⟩
  | n + 1, k + 1, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_neg n (k + 1) ha, hasGrade_neg n k hb⟩

theorem hasGrade_smul : ∀ (n k : Nat) (r : R) {x : Cl R n},
    HasGrade n k x → HasGrade n k (smul n r x)
  | 0, 0, _, _, _ => trivial
  | 0, _ + 1, r, _, hx => by rw [hx]; exact CRing.mul_zero r
  | n + 1, 0, r, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_smul n 0 r ha, by rw [hb, smul_zero]⟩
  | n + 1, k + 1, r, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_smul n (k + 1) r ha, hasGrade_smul n k r hb⟩

theorem hasGrade_invol : ∀ (n k : Nat) {x : Cl R n},
    HasGrade n k x → HasGrade n k (invol n x)
  | 0, 0, _, _ => trivial
  | 0, _ + 1, _, hx => hx
  | n + 1, 0, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_invol n 0 ha, by show neg n (invol n _) = zero n; rw [hb, invol_zero, neg_zero]⟩
  | n + 1, k + 1, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_invol n (k + 1) ha, hasGrade_neg n k (hasGrade_invol n k hb)⟩

/-- Exact grade action of `invol`: on `Λ^k`, `x̂ = (-1)^k · x`. -/
theorem invol_on_grade : ∀ (n k : Nat) {x : Cl R n},
    HasGrade n k x → invol n x = smul n (CRing.ringParitySign k) x
  | 0, 0, x, _ => by
      have h0 : (0 : Nat) % 2 = 0 := rfl
      rw [CRing.ringParitySign_even h0, one_smul]
      rfl
  | 0, _ + 1, _, hx => by
      rw [hx]
      exact (smul_zero 0 _).symm
  | n + 1, 0, (a, b), ⟨ha, hb⟩ => by
      have h0 : (0 : Nat) % 2 = 0 := rfl
      rw [hb, CRing.ringParitySign_even h0, one_smul]
      exact Prod.ext
        (by show invol n a = a; rw [invol_on_grade n 0 ha, CRing.ringParitySign_even h0, one_smul])
        (by show neg n (invol n (zero n)) = zero n; rw [invol_zero, neg_zero])
  | n + 1, k + 1, (a, b), ⟨ha, hb⟩ => by
      apply Prod.ext
      · exact invol_on_grade n (k + 1) ha
      · show neg n (invol n b) = smul n (CRing.ringParitySign (k + 1)) b
        rw [invol_on_grade n k hb, ← neg_smul]
        have hsign : CRing.neg (CRing.ringParitySign (R := R) k) = CRing.ringParitySign (k + 1) := by
          have hk1 : CRing.ringParitySign (R := R) 1 = CRing.neg CRing.one :=
            CRing.ringParitySign_odd rfl
          rw [CRing.ringParitySign_add k 1, hk1, CRing.mul_neg, CRing.mul_one]
        rw [hsign]

/-- Exact grade action of `rev`: on `Λ^k`, `x̃ = (-1)^{k(k-1)/2} · x`. -/
theorem rev_on_grade : ∀ (n k : Nat) {x : Cl R n},
    HasGrade n k x → rev n x = smul n (CRing.ringParitySign (k * (k - 1) / 2)) x
  | 0, 0, x, _ => by
      have h0 : (0 * (0 - 1) / 2) % 2 = 0 := rfl
      rw [CRing.ringParitySign_even h0, one_smul]
      rfl
  | 0, _ + 1, _, hx => by
      rw [hx]
      exact (smul_zero 0 _).symm
  | n + 1, 0, (a, b), ⟨ha, hb⟩ => by
      have h0 : (0 * (0 - 1) / 2) % 2 = 0 := rfl
      rw [hb, CRing.ringParitySign_even h0, one_smul]
      exact Prod.ext
        (by show rev n a = a; rw [rev_on_grade n 0 ha, CRing.ringParitySign_even h0, one_smul])
        (by show invol n (rev n (zero n)) = zero n; rw [rev_zero, invol_zero])
  | n + 1, k + 1, (a, b), ⟨ha, hb⟩ => by
      apply Prod.ext
      · exact rev_on_grade n (k + 1) ha
      · show invol n (rev n b) = smul n (CRing.ringParitySign ((k + 1) * ((k + 1) - 1) / 2)) b
        rw [rev_on_grade n k hb, invol_smul, invol_on_grade n k hb, smul_smul,
            ← CRing.ringParitySign_add]
        have htri : k * (k - 1) / 2 + k = (k + 1) * ((k + 1) - 1) / 2 := by
          cases k with
          | zero => rfl
          | succ m =>
              show (m + 1) * m / 2 + (m + 1) = (m + 2) * (m + 1) / 2
              have hmul : (m + 2) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by
                rw [Nat.add_mul, Nat.mul_comm 2 (m + 1), Nat.mul_comm m (m + 1)]
              rw [hmul, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        rw [htri]

/-- Exterior wedge product is graded: `Λ^r ∧ Λ^s ⊆ Λ^{r+s}` for all `n, r, s : Nat`. -/
theorem wedge_hasGrade : ∀ (n r s : Nat) {A B : Cl R n},
    HasGrade n r A → HasGrade n s B → HasGrade n (r + s) (wedge n A B)
  | 0, 0, 0, _, _, _, _ => trivial
  | 0, 0, _ + 1, A, B, _, hB => by
      show CRing.mul A B = CRing.zero
      rw [hB, CRing.mul_zero]
  | 0, r + 1, s, A, B, hA, _ => by
      have hpos : r + 1 + s = (r + s) + 1 := by omega
      rw [hpos]
      show CRing.mul A B = CRing.zero
      rw [hA, CRing.zero_mul]
  | n + 1, 0, 0, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      rw [wedge_step, ha2, hb2, wedge_zero, zero_wedge, add_zero]
      exact ⟨wedge_hasGrade n 0 0 ha1 hb1, rfl⟩
  | n + 1, 0, s + 1, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have h0s : 0 + (s + 1) = (0 + s) + 1 := by omega
      rw [h0s, wedge_step, ha2, zero_wedge, add_zero]
      exact ⟨by rw [← h0s]; exact wedge_hasGrade n 0 (s + 1) ha1 hb1,
             wedge_hasGrade n 0 s ha1 hb2⟩
  | n + 1, r + 1, 0, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have hr0 : (r + 1) + 0 = (r + 0) + 1 := by omega
      rw [hr0, wedge_step, hb2, wedge_zero, zero_add]
      exact ⟨by rw [← hr0]; exact wedge_hasGrade n (r + 1) 0 ha1 hb1,
             wedge_hasGrade n r 0 ha2 (hasGrade_invol n 0 hb1)⟩
  | n + 1, r + 1, s + 1, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have hrs : (r + 1) + (s + 1) = (r + s + 1) + 1 := by omega
      rw [hrs, wedge_step]
      refine ⟨by rw [← hrs]; exact wedge_hasGrade n (r + 1) (s + 1) ha1 hb1, ?_⟩
      have h1 : HasGrade n (r + s + 1) (wedge n a1 b2) := by
        have heq : (r + 1) + s = r + s + 1 := by omega
        rw [← heq]
        exact wedge_hasGrade n (r + 1) s ha1 hb2
      have h2 : HasGrade n (r + s + 1) (wedge n a2 (invol n b1)) :=
        wedge_hasGrade n r (s + 1) ha2 (hasGrade_invol n (s + 1) hb1)
      exact hasGrade_add n (r + s + 1) h1 h2

/-- Graded anticommutativity of the exterior wedge product:
      `B ∧ A = (-1)^{r s} · (A ∧ B)` for all `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)`. -/
theorem wedge_graded_comm : ∀ (n r s : Nat) {A B : Cl R n},
    HasGrade n r A → HasGrade n s B →
    wedge n B A = smul n (CRing.ringParitySign (r * s)) (wedge n A B)
  | 0, 0, 0, A, B, _, _ => by
      have h0 : (0 * 0) % 2 = 0 := rfl
      rw [CRing.ringParitySign_even h0, one_smul]
      exact CRing.mul_comm B A
  | 0, 0, _ + 1, A, B, _, hB => by
      show CRing.mul B A = CRing.mul _ (CRing.mul A B)
      rw [hB, CRing.zero_mul, CRing.mul_zero, CRing.mul_zero]
  | 0, _ + 1, _, A, B, hA, _ => by
      show CRing.mul B A = CRing.mul _ (CRing.mul A B)
      rw [hA, CRing.zero_mul, CRing.mul_zero, CRing.mul_zero]
  | n + 1, 0, 0, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      rw [wedge_step, wedge_step, ha2, hb2,
          wedge_zero, wedge_zero, zero_wedge, zero_wedge, add_zero]
      exact Prod.ext (wedge_graded_comm n 0 0 ha1 hb1) (smul_zero n _).symm
  | n + 1, 0, s + 1, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have h0 : (0 * (s + 1)) % 2 = 0 := by simp
      rw [CRing.ringParitySign_even h0, one_smul, wedge_step, wedge_step, ha2,
          wedge_zero, zero_wedge, zero_add, add_zero]
      apply Prod.ext
      · have ih1 := wedge_graded_comm n 0 (s + 1) ha1 hb1
        rw [CRing.ringParitySign_even h0, one_smul] at ih1
        exact ih1
      · have hinv : invol n a1 = a1 := by
          rw [invol_on_grade n 0 ha1, CRing.ringParitySign_even rfl, one_smul]
        rw [hinv]
        have ih2 := wedge_graded_comm n 0 s ha1 hb2
        have h0' : (0 * s) % 2 = 0 := by simp
        rw [CRing.ringParitySign_even h0', one_smul] at ih2
        exact ih2
  | n + 1, r + 1, 0, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have h0 : ((r + 1) * 0) % 2 = 0 := by simp
      rw [CRing.ringParitySign_even h0, one_smul, wedge_step, wedge_step, hb2,
          wedge_zero, zero_wedge, zero_add, add_zero]
      apply Prod.ext
      · have ih1 := wedge_graded_comm n (r + 1) 0 ha1 hb1
        rw [CRing.ringParitySign_even h0, one_smul] at ih1
        exact ih1
      · have hinv : invol n b1 = b1 := by
          rw [invol_on_grade n 0 hb1, CRing.ringParitySign_even rfl, one_smul]
        rw [hinv]
        have ih2 := wedge_graded_comm n r 0 ha2 hb1
        have h0' : (r * 0) % 2 = 0 := by simp
        rw [CRing.ringParitySign_even h0', one_smul] at ih2
        exact ih2
  | n + 1, r + 1, s + 1, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      rw [wedge_step, wedge_step]
      apply Prod.ext
      · exact wedge_graded_comm n (r + 1) (s + 1) ha1 hb1
      · show add n (wedge n b1 a2) (wedge n b2 (invol n a1)) =
             smul n (CRing.ringParitySign ((r + 1) * (s + 1)))
               (add n (wedge n a1 b2) (wedge n a2 (invol n b1)))
        rw [smul_add, invol_on_grade n (r + 1) ha1, invol_on_grade n (s + 1) hb1,
            wedge_smul, wedge_smul, smul_smul]
        have ih_b1a2 := wedge_graded_comm n r (s + 1) ha2 hb1
        have ih_b2a1 := wedge_graded_comm n (r + 1) s ha1 hb2
        rw [ih_b1a2, ih_b2a1, smul_smul, ← CRing.ringParitySign_add, ← CRing.ringParitySign_add]
        have heq1 : (r + 1) + (r + 1) * s = (r + 1) * (s + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]
        have heq2 : (r + 1) * (s + 1) + (s + 1) = r * (s + 1) + 2 * (s + 1) := by
          rw [Nat.succ_mul, Nat.add_assoc, ← Nat.two_mul]
        have hmod : ((r + 1) * (s + 1) + (s + 1)) % 2 = (r * (s + 1)) % 2 := by
          rw [heq2]; omega
        rw [heq1, CRing.ringParitySign_of_mod_eq hmod, add_comm]

end AlgebraOps

end Cl
end Conjecture00000007618
