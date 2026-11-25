/-
  Conjecture 00000007616 — Constructive 2^n-Dimensional Clifford & Exterior Algebra
  Core Lean 4.19.0 only (zero external dependencies).

  Constructs `Cl R n` recursively over any commutative ring `CRing R` and orthogonal
  quadratic form `q : Fin n → R`:
    Cl R 0       = R
    Cl R (n + 1) = Cl R n × Cl R n   (representing `a + b · e_n`)
  Proves full associative unital ring laws, exterior algebra (`q = 0`) laws,
  grade involution automorphism `invol`, reversion anti-involution `rev`,
  grading `HasGrade`, and homogeneous-to-full additive extension.
-/

import Conjecture00000007616.Ring

namespace Conjecture00000007616

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

section ModuleOps
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

/-- Clifford conjugation `x̄ = invol (rev x)` (`(-1)^{k(k+1)/2}` on grade `k`). -/
def conj (n : Nat) (x : Cl R n) : Cl R n :=
  invol n (rev n x)

/-- Geometric product in `Cl(R^n, q)` for orthogonal quadratic form `q : Fin n → R`. -/
def mul : {n : Nat} → (Fin n → R) → Cl R n → Cl R n → Cl R n
  | 0, _, a, c => CRing.mul a c
  | n + 1, q, x, y =>
      let q' := initMetric q
      let qn := lastMetric q
      ( add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2))),
        add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)) )

/-- Identically zero quadratic form, giving the exterior algebra `Λ(R^n) = Cl(R^n, 0)`. -/
def zeroMetric (n : Nat) : Fin n → R :=
  fun _ => CRing.zero

/-- Exterior wedge product `x ∧ y`, realized as the `q = 0` Clifford product. -/
def wedge (n : Nat) (x y : Cl R n) : Cl R n :=
  mul (zeroMetric (R := R) n) x y

/-- Induced determinant bilinear form `⟨x, y⟩_q` on `Λ(R^n) ≅ Cl(R^n, q)`. -/
def inner : {n : Nat} → (Fin n → R) → Cl R n → Cl R n → R
  | 0, _, a, c => CRing.mul a c
  | _ + 1, q, x, y =>
      CRing.add (inner (initMetric q) x.1 y.1)
        (CRing.mul (lastMetric q) (inner (initMetric q) x.2 y.2))

/-- Discriminant product `∏_{i=0}^{n-1} q(i) = ⟨ω_n, ω_n⟩_q`. -/
def prodMetric : {n : Nat} → (Fin n → R) → R
  | 0, _ => CRing.one
  | _ + 1, q => CRing.mul (prodMetric (initMetric q)) (lastMetric q)

/-- Standard basis vector `e_i ∈ Λ^1(R^n) ⊂ Cl(R^n, q)`. -/
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

/-- Top-grade (`ω_n`) coefficient extraction. -/
def topPart : (n : Nat) → Cl R n → R
  | 0, a => a
  | n + 1, x => topPart n x.2

/-- Homogeneous grade predicate `x ∈ Λ^k(R^n)`. -/
def HasGrade : (n : Nat) → Nat → Cl R n → Prop
  | 0, 0, _ => True
  | 0, _ + 1, x => x = CRing.zero
  | n + 1, 0, (a, b) => HasGrade n 0 a ∧ b = zero n
  | n + 1, k + 1, (a, b) => HasGrade n (k + 1) a ∧ HasGrade n k b

/-! ### Abelian Group & Module Laws -/

theorem add_assoc : ∀ (n : Nat) (x y z : Cl R n), add n (add n x y) z = add n x (add n y z)
  | 0, x, y, z => CRing.add_assoc x y z
  | n + 1, (_, _), (_, _), (_, _) =>
      Prod.ext (add_assoc n _ _ _) (add_assoc n _ _ _)

theorem add_comm : ∀ (n : Nat) (x y : Cl R n), add n x y = add n y x
  | 0, x, y => CRing.add_comm x y
  | n + 1, (_, _), (_, _) =>
      Prod.ext (add_comm n _ _) (add_comm n _ _)

theorem zero_add : ∀ (n : Nat) (x : Cl R n), add n (zero n) x = x
  | 0, x => CRing.zero_add x
  | n + 1, (_, _) =>
      Prod.ext (zero_add n _) (zero_add n _)

theorem add_zero (n : Nat) (x : Cl R n) : add n x (zero n) = x := by
  rw [add_comm, zero_add]

theorem add_left_neg : ∀ (n : Nat) (x : Cl R n), add n (neg n x) x = zero n
  | 0, x => CRing.add_left_neg x
  | n + 1, (_, _) =>
      Prod.ext (add_left_neg n _) (add_left_neg n _)

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
  | 0, x => by rw [smul, neg, CRing.neg_mul, CRing.one_mul]
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

/-! ### Involution & Reversion Linearity -/

theorem invol_zero : ∀ (n : Nat), invol n (zero (R := R) n) = zero n
  | 0 => rfl
  | n + 1 =>
      Prod.ext (invol_zero n)
        (by show neg n (invol n (zero n)) = zero n; rw [invol_zero n, neg_zero])

theorem invol_one : ∀ (n : Nat), invol n (one (R := R) n) = one n
  | 0 => rfl
  | n + 1 =>
      Prod.ext (invol_one n)
        (by show neg n (invol n (zero n)) = zero n; rw [invol_zero n, neg_zero])

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
  | n + 1 =>
      Prod.ext (rev_zero n)
        (by show invol n (rev n (zero n)) = zero n; rw [rev_zero n, invol_zero])

theorem rev_one : ∀ (n : Nat), rev n (one (R := R) n) = one n
  | 0 => rfl
  | n + 1 =>
      Prod.ext (rev_one n)
        (by show invol n (rev n (zero n)) = zero n; rw [rev_zero n, invol_zero])

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

theorem invol_rev_comm : ∀ (n : Nat) (x : Cl R n),
    invol n (rev n x) = rev n (invol n x)
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (invol_rev_comm n a) (by
        show neg n (invol n (invol n (rev n b))) = invol n (rev n (neg n (invol n b)))
        rw [invol_invol, rev_neg, invol_neg, invol_rev_comm n (invol n b), invol_invol])

theorem rev_rev : ∀ (n : Nat) (x : Cl R n), rev n (rev n x) = x
  | 0, _ => rfl
  | n + 1, (a, b) =>
      Prod.ext (rev_rev n a) (by
        show invol n (rev n (invol n (rev n b))) = b
        rw [← invol_rev_comm n (rev n b), rev_rev, invol_invol])

/-! ### Multiplicative Ring & Involution Laws -/

theorem mul_zero : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q x (zero n) = zero n
  | 0, _, x => CRing.mul_zero x
  | n + 1, q, (a, b) =>
      Prod.ext
        (by
          show add n (mul (initMetric q) a (zero n))
            (smul n (lastMetric q) (mul (initMetric q) b (invol n (zero n)))) = zero n
          rw [invol_zero, mul_zero, mul_zero, smul_zero, add_zero])
        (by
          show add n (mul (initMetric q) a (zero n))
            (mul (initMetric q) b (invol n (zero n))) = zero n
          rw [invol_zero, mul_zero, mul_zero, add_zero])

theorem zero_mul : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q (zero n) x = zero n
  | 0, _, x => CRing.zero_mul x
  | n + 1, q, (c, d) =>
      Prod.ext
        (by
          show add n (mul (initMetric q) (zero n) c)
            (smul n (lastMetric q) (mul (initMetric q) (zero n) (invol n d))) = zero n
          rw [zero_mul, zero_mul, smul_zero, add_zero])
        (by
          show add n (mul (initMetric q) (zero n) d)
            (mul (initMetric q) (zero n) (invol n c)) = zero n
          rw [zero_mul, zero_mul, add_zero])

theorem one_mul : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q (one n) x = x
  | 0, _, x => CRing.one_mul x
  | n + 1, q, (c, d) =>
      Prod.ext
        (by
          show add n (mul (initMetric q) (one n) c)
            (smul n (lastMetric q) (mul (initMetric q) (zero n) (invol n d))) = c
          rw [one_mul, zero_mul, smul_zero, add_zero])
        (by
          show add n (mul (initMetric q) (one n) d)
            (mul (initMetric q) (zero n) (invol n c)) = d
          rw [one_mul, zero_mul, add_zero])

theorem mul_one : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n), mul q x (one n) = x
  | 0, _, x => CRing.mul_one x
  | n + 1, q, (a, b) =>
      Prod.ext
        (by
          show add n (mul (initMetric q) a (one n))
            (smul n (lastMetric q) (mul (initMetric q) b (invol n (zero n)))) = a
          rw [invol_zero, mul_one, mul_zero, smul_zero, add_zero])
        (by
          show add n (mul (initMetric q) a (zero n))
            (mul (initMetric q) b (invol n (one n))) = b
          rw [invol_one, mul_zero, mul_one, zero_add])

theorem left_distrib : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q x (add n y z) = add n (mul q x y) (mul q x z)
  | 0, _, x, y, z => CRing.left_distrib x y z
  | n + 1, q, (a, b), (c, d), (e, f) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show add n (mul q' a (add n c e)) (smul n qn (mul q' b (invol n (add n d f)))) =
            add n (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
                  (add n (mul q' a e) (smul n qn (mul q' b (invol n f))))
          rw [invol_add, left_distrib q', left_distrib q', smul_add, add_add_add_comm])
        (by
          show add n (mul q' a (add n d f)) (mul q' b (invol n (add n c e))) =
            add n (add n (mul q' a d) (mul q' b (invol n c)))
                  (add n (mul q' a f) (mul q' b (invol n e)))
          rw [invol_add, left_distrib q', left_distrib q', add_add_add_comm])

theorem right_distrib : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q (add n x y) z = add n (mul q x z) (mul q y z)
  | 0, _, x, y, z => CRing.right_distrib x y z
  | n + 1, q, (a, b), (c, d), (e, f) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show add n (mul q' (add n a c) e) (smul n qn (mul q' (add n b d) (invol n f))) =
            add n (add n (mul q' a e) (smul n qn (mul q' b (invol n f))))
                  (add n (mul q' c e) (smul n qn (mul q' d (invol n f))))
          rw [right_distrib q', right_distrib q', smul_add, add_add_add_comm])
        (by
          show add n (mul q' (add n a c) f) (mul q' (add n b d) (invol n e)) =
            add n (add n (mul q' a f) (mul q' b (invol n e)))
                  (add n (mul q' c f) (mul q' d (invol n e)))
          rw [right_distrib q', right_distrib q', add_add_add_comm])

theorem smul_mul : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    mul q (smul n r x) y = smul n r (mul q x y)
  | 0, _, r, x, y => CRing.mul_assoc r x y
  | n + 1, q, r, (a, b), (c, d) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show add n (mul q' (smul n r a) c) (smul n qn (mul q' (smul n r b) (invol n d))) =
            smul n r (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
          rw [smul_mul q', smul_mul q', smul_add, smul_smul, smul_smul, CRing.mul_comm qn r])
        (by
          show add n (mul q' (smul n r a) d) (mul q' (smul n r b) (invol n c)) =
            smul n r (add n (mul q' a d) (mul q' b (invol n c)))
          rw [smul_mul q', smul_mul q', smul_add])

theorem mul_smul : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    mul q x (smul n r y) = smul n r (mul q x y)
  | 0, _, r, x, y => by
      show CRing.mul x (CRing.mul r y) = CRing.mul r (CRing.mul x y)
      rw [← CRing.mul_assoc, CRing.mul_comm x r, CRing.mul_assoc]
  | n + 1, q, r, (a, b), (c, d) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show add n (mul q' a (smul n r c)) (smul n qn (mul q' b (invol n (smul n r d)))) =
            smul n r (add n (mul q' a c) (smul n qn (mul q' b (invol n d))))
          rw [invol_smul, mul_smul q', mul_smul q', smul_add, smul_smul, smul_smul, CRing.mul_comm qn r])
        (by
          show add n (mul q' a (smul n r d)) (mul q' b (invol n (smul n r c))) =
            smul n r (add n (mul q' a d) (mul q' b (invol n c)))
          rw [invol_smul, mul_smul q', mul_smul q', smul_add])

theorem mul_neg : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    mul q x (neg n y) = neg n (mul q x y)
  | n, q, x, y => by
      rw [← neg_one_smul n y, mul_smul, neg_one_smul]

theorem neg_mul : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    mul q (neg n x) y = neg n (mul q x y)
  | n, q, x, y => by
      rw [← neg_one_smul n x, smul_mul, neg_one_smul]

/-- Grade involution `invol` is an algebra automorphism of `Cl(R^n, q)`. -/
theorem invol_mul : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    invol n (mul q x y) = mul q (invol n x) (invol n y)
  | 0, _, _, _ => rfl
  | n + 1, q, (a, b), (c, d) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show invol n (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) =
            add n (mul q' (invol n a) (invol n c))
              (smul n qn (mul q' (neg n (invol n b)) (invol n (neg n (invol n d)))))
          rw [invol_add, invol_smul, invol_mul q', invol_mul q', invol_invol,
              invol_neg, invol_invol, neg_mul, mul_neg, neg_neg])
        (by
          show neg n (invol n (add n (mul q' a d) (mul q' b (invol n c)))) =
            add n (mul q' (invol n a) (neg n (invol n d)))
              (mul q' (neg n (invol n b)) (invol n (invol n c)))
          rw [invol_add, neg_add, invol_mul q', invol_mul q', invol_invol,
              mul_neg, neg_mul])

/-- Associativity of the Clifford geometric product across all dimensions `n`. -/
theorem mul_assoc : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    mul q (mul q x y) z = mul q x (mul q y z)
  | 0, _, x, y, z => CRing.mul_assoc x y z
  | n + 1, q, (a, b), (c, d), (e, f) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show add n (mul q' (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) e)
                     (smul n qn (mul q' (add n (mul q' a d) (mul q' b (invol n c))) (invol n f))) =
               add n (mul q' a (add n (mul q' c e) (smul n qn (mul q' d (invol n f)))))
                     (smul n qn (mul q' b (invol n (add n (mul q' c f) (mul q' d (invol n e))))))
          rw [right_distrib q', right_distrib q', smul_mul q', smul_add,
              left_distrib q', mul_smul q', invol_add, invol_mul q', invol_mul q', invol_invol,
              left_distrib q', smul_add,
              mul_assoc q', mul_assoc q', mul_assoc q', mul_assoc q',
              add_assoc, add_assoc,
              add_comm n (smul n qn (mul q' b (mul q' (invol n d) e)))]
          rw [← add_assoc n (smul n qn (mul q' a (mul q' d (invol n f))))
                (smul n qn (mul q' b (mul q' (invol n c) (invol n f))))
                (smul n qn (mul q' b (mul q' (invol n d) e)))])
        (by
          show add n (mul q' (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) f)
                     (mul q' (add n (mul q' a d) (mul q' b (invol n c))) (invol n e)) =
               add n (mul q' a (add n (mul q' c f) (mul q' d (invol n e))))
                     (mul q' b (invol n (add n (mul q' c e) (smul n qn (mul q' d (invol n f))))))
          rw [right_distrib q', right_distrib q', smul_mul q',
              left_distrib q', invol_add, invol_smul, invol_mul q', invol_mul q', invol_invol,
              left_distrib q', mul_smul q',
              mul_assoc q', mul_assoc q', mul_assoc q', mul_assoc q']
          rw [add_assoc, add_assoc]
          apply congrArg (add n (mul q' a (mul q' c f)))
          rw [← add_assoc, add_comm n (smul n qn (mul q' b (mul q' (invol n d) f))), add_assoc]
          apply congrArg (add n (mul q' a (mul q' d (invol n e))))
          exact add_comm n _ _)

/-- Reversion `rev` is an algebra anti-automorphism: `rev (x * y) = rev y * rev x`. -/
theorem rev_mul : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    rev n (mul q x y) = mul q (rev n y) (rev n x)
  | 0, _, x, y => CRing.mul_comm x y
  | n + 1, q, (a, b), (c, d) =>
      let q' := initMetric q
      let qn := lastMetric q
      Prod.ext
        (by
          show rev n (add n (mul q' a c) (smul n qn (mul q' b (invol n d)))) =
            add n (mul q' (rev n c) (rev n a))
                  (smul n qn (mul q' (invol n (rev n d)) (invol n (invol n (rev n b)))))
          rw [rev_add, rev_smul, rev_mul q', rev_mul q', invol_rev_comm n d, invol_invol])
        (by
          show invol n (rev n (add n (mul q' a d) (mul q' b (invol n c)))) =
            add n (mul q' (rev n c) (invol n (rev n b)))
                  (mul q' (invol n (rev n d)) (invol n (rev n a)))
          rw [rev_add, invol_add, rev_mul q', rev_mul q',
              invol_mul q', invol_mul q',
              ← invol_rev_comm n c, invol_invol, add_comm])

/-! ### Grading Properties & Homogeneous Extension -/

theorem hasGrade_zero : ∀ (n k : Nat), HasGrade n k (zero (R := R) n)
  | 0, 0 => trivial
  | 0, _ + 1 => rfl
  | n + 1, 0 => ⟨hasGrade_zero n 0, rfl⟩
  | n + 1, k + 1 => ⟨hasGrade_zero n (k + 1), hasGrade_zero n k⟩

theorem hasGrade_gt_zero : ∀ (n k : Nat) (x : Cl R n), n < k → HasGrade n k x → x = zero n
  | 0, 0, _, hlt, _ => absurd hlt (Nat.lt_irrefl 0)
  | 0, _ + 1, _, _, hx => hx
  | _ + 1, 0, _, hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, k + 1, (a, b), hlt, ⟨ha, hb⟩ =>
      have hk : n < k := Nat.lt_of_succ_lt_succ hlt
      Prod.ext
        (hasGrade_gt_zero n (k + 1) a (Nat.lt_succ_of_lt hk) ha)
        (hasGrade_gt_zero n k b hk hb)

theorem hasGrade_one (n : Nat) : HasGrade n 0 (one (R := R) n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, rfl⟩

theorem hasGrade_omega : ∀ (n : Nat), HasGrade n n (omega (R := R) n)
  | 0 => trivial
  | n + 1 => ⟨hasGrade_zero n (n + 1), hasGrade_omega n⟩

theorem hasGrade_add : ∀ (n k : Nat) {x y : Cl R n},
    HasGrade n k x → HasGrade n k y → HasGrade n k (add n x y)
  | 0, 0, _, _, _, _ => trivial
  | 0, _ + 1, _, _, hx, hy => by
      show CRing.add _ _ = CRing.zero
      rw [hx, hy, CRing.zero_add]
  | n + 1, 0, (_, _), (_, _), ⟨ha, hb⟩, ⟨hc, hd⟩ =>
      ⟨hasGrade_add n 0 ha hc, by show add n _ _ = zero n; rw [hb, hd, zero_add]⟩
  | n + 1, k + 1, (_, _), (_, _), ⟨ha, hb⟩, ⟨hc, hd⟩ =>
      ⟨hasGrade_add n (k + 1) ha hc, hasGrade_add n k hb hd⟩

theorem hasGrade_neg : ∀ (n k : Nat) {x : Cl R n},
    HasGrade n k x → HasGrade n k (neg n x)
  | 0, 0, _, _ => trivial
  | 0, _ + 1, _, hx => by show CRing.neg _ = CRing.zero; rw [hx, CRing.neg_zero]
  | n + 1, 0, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_neg n 0 ha, by show neg n _ = zero n; rw [hb, neg_zero]⟩
  | n + 1, k + 1, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_neg n (k + 1) ha, hasGrade_neg n k hb⟩

theorem hasGrade_smul : ∀ (n k : Nat) (r : R) {x : Cl R n},
    HasGrade n k x → HasGrade n k (smul n r x)
  | 0, 0, _, _, _ => trivial
  | 0, _ + 1, r, _, hx => by show CRing.mul r _ = CRing.zero; rw [hx, CRing.mul_zero]
  | n + 1, 0, r, (_, _), ⟨ha, hb⟩ =>
      ⟨hasGrade_smul n 0 r ha, by show smul n r _ = zero n; rw [hb, smul_zero]⟩
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

theorem hasGrade_zero_invol : ∀ (n : Nat) {x : Cl R n},
    HasGrade n 0 x → invol n x = x
  | 0, _, _ => rfl
  | n + 1, (a, b), ⟨ha, hb⟩ =>
      Prod.ext (hasGrade_zero_invol n ha)
        (by show neg n (invol n b) = b; rw [hb, invol_zero, neg_zero])

theorem wedge_step {n : Nat} (a b c d : Cl R n) :
    wedge (n + 1) (a, b) (c, d) =
      (wedge n a c, add n (wedge n a d) (wedge n b (invol n c))) := by
  show (add n (wedge n a c) (smul n CRing.zero (wedge n b (invol n d))),
        add n (wedge n a d) (wedge n b (invol n c))) =
       (wedge n a c, add n (wedge n a d) (wedge n b (invol n c)))
  apply Prod.ext
  · rw [zero_smul, add_zero]
  · rfl

theorem wedge_zero {n : Nat} (x : Cl R n) : wedge n x (zero n) = zero n :=
  mul_zero (zeroMetric n) x

theorem zero_wedge {n : Nat} (x : Cl R n) : wedge n (zero n) x = zero n :=
  zero_mul (zeroMetric n) x

theorem wedge_smul {n : Nat} (r : R) (x y : Cl R n) :
    wedge n x (smul n r y) = smul n r (wedge n x y) :=
  mul_smul (zeroMetric n) r x y

theorem wedge_left_distrib {n : Nat} (x y z : Cl R n) :
    wedge n x (add n y z) = add n (wedge n x y) (wedge n x z) :=
  left_distrib (zeroMetric n) x y z

theorem wedge_neg {n : Nat} (x y : Cl R n) :
    wedge n x (neg n y) = neg n (wedge n x y) :=
  mul_neg (zeroMetric n) x y

theorem hasGrade_wedge : ∀ (n j k : Nat) {x y : Cl R n},
    HasGrade n j x → HasGrade n k y → HasGrade n (j + k) (wedge n x y)
  | 0, 0, 0, _, _, _, _ => trivial
  | 0, 0, _ + 1, x, _, _, hy => by
      show CRing.mul x _ = CRing.zero
      rw [hy, CRing.mul_zero]
  | 0, j + 1, k, _, y, hx, _ => by
      have hpos : 0 < (j + 1) + k := by omega
      cases hjk : (j + 1) + k with
      | zero => omega
      | succ m =>
          show CRing.mul _ y = CRing.zero
          rw [hx, CRing.zero_mul]
  | n + 1, 0, 0, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [wedge_step, hb, hd, wedge_zero, zero_wedge, add_zero]
      exact ⟨hasGrade_wedge n 0 0 ha hc, rfl⟩
  | n + 1, 0, k + 1, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [Nat.zero_add, wedge_step, hb, zero_wedge, add_zero]
      have h1 := hasGrade_wedge n 0 (k + 1) ha hc
      have h2 := hasGrade_wedge n 0 k ha hd
      rw [Nat.zero_add] at h1 h2
      exact ⟨h1, h2⟩
  | n + 1, j + 1, 0, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [wedge_step, hd, wedge_zero, zero_add]
      have h1 := hasGrade_wedge n (j + 1) 0 ha hc
      have h2 := hasGrade_wedge n j 0 hb (hasGrade_invol n 0 hc)
      exact ⟨h1, h2⟩
  | n + 1, j + 1, k + 1, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [wedge_step]
      have heq : (j + 1) + (k + 1) = (j + k + 1) + 1 := by omega
      rw [heq]
      have h_ac : HasGrade n ((j + k + 1) + 1) (wedge n a c) := by
        have := hasGrade_wedge n (j + 1) (k + 1) ha hc
        have heq1 : (j + 1) + (k + 1) = (j + k + 1) + 1 := by omega
        rw [← heq1]
        exact this
      have h_ad : HasGrade n (j + k + 1) (wedge n a d) := by
        have := hasGrade_wedge n (j + 1) k ha hd
        have heq2 : (j + 1) + k = j + k + 1 := by omega
        rw [← heq2]
        exact this
      have h_bc : HasGrade n (j + k + 1) (wedge n b (invol n c)) := by
        have := hasGrade_wedge n j (k + 1) hb (hasGrade_invol n (k + 1) hc)
        have heq3 : j + (k + 1) = j + k + 1 := by omega
        rw [← heq3]
        exact this
      exact ⟨h_ac, hasGrade_add n (j + k + 1) h_ad h_bc⟩

/-- Any two additive maps on `Cl R n` that agree on all homogeneous elements of
    grades `k ≤ n` are equal on every (possibly inhomogeneous) element of `Cl R n`. -/
theorem eq_of_eq_on_grades :
    ∀ (n m : Nat) (f g : Cl R n → Cl R m),
      (∀ x y, f (add n x y) = add m (f x) (f y)) →
      (∀ x y, g (add n x y) = add m (g x) (g y)) →
      (∀ k, k ≤ n → ∀ x, HasGrade n k x → f x = g x) →
      ∀ z : Cl R n, f z = g z
  | 0, _, f, g, _, _, hgrade, z =>
      hgrade 0 (Nat.le_refl 0) z trivial
  | n + 1, m, f, g, hf, hg, hgrade, (a, b) => by
      have hdecomp : ((a, b) : Cl R (n + 1)) = add (n + 1) (a, zero n) (zero n, b) :=
        Prod.ext (add_zero n a).symm (zero_add n b).symm
      have hf1 : ∀ x : Cl R n, f (x, zero n) = g (x, zero n) :=
        eq_of_eq_on_grades n m (fun x => f (x, zero n)) (fun x => g (x, zero n))
          (fun x y => by
            dsimp only
            have : ((add n x y, zero n) : Cl R (n + 1)) = add (n + 1) (x, zero n) (y, zero n) :=
              Prod.ext rfl (add_zero n (zero n)).symm
            rw [this, hf])
          (fun x y => by
            dsimp only
            have : ((add n x y, zero n) : Cl R (n + 1)) = add (n + 1) (x, zero n) (y, zero n) :=
              Prod.ext rfl (add_zero n (zero n)).symm
            rw [this, hg])
          (fun k hk x hx => by
            cases k with
            | zero => exact hgrade 0 (Nat.zero_le _) (x, zero n) ⟨hx, rfl⟩
            | succ k' =>
                exact hgrade (k' + 1) (Nat.le_succ_of_le hk) (x, zero n) ⟨hx, hasGrade_zero n k'⟩)
      have hf2 : ∀ y : Cl R n, f (zero n, y) = g (zero n, y) :=
        eq_of_eq_on_grades n m (fun y => f (zero n, y)) (fun y => g (zero n, y))
          (fun x y => by
            dsimp only
            have : ((zero n, add n x y) : Cl R (n + 1)) = add (n + 1) (zero n, x) (zero n, y) :=
              Prod.ext (add_zero n (zero n)).symm rfl
            rw [this, hf])
          (fun x y => by
            dsimp only
            have : ((zero n, add n x y) : Cl R (n + 1)) = add (n + 1) (zero n, x) (zero n, y) :=
              Prod.ext (add_zero n (zero n)).symm rfl
            rw [this, hg])
          (fun k hk y hy =>
            hgrade (k + 1) (Nat.succ_le_succ hk) (zero n, y) ⟨hasGrade_zero n (k + 1), hy⟩)
      rw [hdecomp, hf, hg, hf1 a, hf2 b]

end ModuleOps

end Cl
end Conjecture00000007616
