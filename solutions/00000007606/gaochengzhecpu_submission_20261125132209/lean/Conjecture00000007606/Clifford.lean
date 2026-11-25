/-
  Conjecture 00000007606 — Arbitrary-Dimension Clifford Algebras & Universal Spin Theorems

  Constructs the universal Clifford algebra `Cl K sig` over any `FieldK K` and any
  orthogonal signature `sig : List K` (`e_i^2 = c_i`), proves full associative unital
  algebra laws, grade involution `invol`, reversion `rev`, fundamental Clifford law
  `v^2 = Q(v) * 1`, and establishes for ALL dimensions `n`:
    1. Universal Adjoint Orthogonality (`Q(Ad_x(v)) = Q(v)`),
    2. Universal Pseudoscalar Commutation & Reflection Obstruction (no element of
       `(Cl⁺)ˣ` ever induces a hyperplane reflection in `O(V, Q)` for `n ≥ 1`, and in
       odd dimensions `n = 2m + 1` not even `(Cl)ˣ` can via ordinary `Ad`),
    3. Universal Scalar-Unit Kernel Theorem (`Kˣ · 1 ⊆ ker(Ad)`),
    4. Universal Spin Kernel-Two Theorem (`ker(Ad|_{Spin(K, sig)}) = {+1, -1}` of
       exact cardinality `2` for ALL nondegenerate signatures `sig` in `char(K) ≠ 2`).
-/

import Conjecture00000007606.Field

namespace Conjecture00000007606

/-- Recursive `2^n`-dimensional Clifford algebra `Cl(K, [c_1, ..., c_n])`. -/
abbrev Cl (K : Type) : List K → Type
  | [] => K
  | _ :: cs => Cl K cs × Cl K cs

/-- Underlying `n`-dimensional quadratic space `V = K^n` for `sig : List K`. -/
abbrev Vec (K : Type) : List K → Type
  | [] => Unit
  | _ :: cs => Vec K cs × K

namespace Cl

section BasicAlgebra
variable {K : Type} [F : FieldK K]

def zero : (sig : List K) → Cl K sig
  | [] => F.zero
  | _ :: cs => (zero cs, zero cs)

def one : (sig : List K) → Cl K sig
  | [] => F.one
  | _ :: cs => (one cs, zero cs)

def scalar (k : K) : (sig : List K) → Cl K sig
  | [] => k
  | _ :: cs => (scalar k cs, zero cs)

def add : (sig : List K) → Cl K sig → Cl K sig → Cl K sig
  | [], a, b => F.add a b
  | _ :: cs, x, y => (add cs x.1 y.1, add cs x.2 y.2)

def neg : (sig : List K) → Cl K sig → Cl K sig
  | [], a => F.neg a
  | _ :: cs, x => (neg cs x.1, neg cs x.2)

def sub (sig : List K) (x y : Cl K sig) : Cl K sig :=
  add sig x (neg sig y)

def smul (k : K) : (sig : List K) → Cl K sig → Cl K sig
  | [], a => F.mul k a
  | _ :: cs, x => (smul k cs x.1, smul k cs x.2)

/-- Grade involution `α`: `+1` on even grades, `-1` on odd grades. -/
def invol : (sig : List K) → Cl K sig → Cl K sig
  | [], a => a
  | _ :: cs, x => (invol cs x.1, neg cs (invol cs x.2))

/-- Reversion `x ↦ x̃`: anti-automorphism fixing grade-1 vectors. -/
def rev : (sig : List K) → Cl K sig → Cl K sig
  | [], a => a
  | _ :: cs, x => (rev cs x.1, invol cs (rev cs x.2))

/-- Clifford product on `Cl K sig` (`e_top^2 = c`, `e_top y = α(y) e_top`). -/
def mul : (sig : List K) → Cl K sig → Cl K sig → Cl K sig
  | [], a, b => F.mul a b
  | c :: cs, x, y =>
      (add cs (mul cs x.1 y.1) (smul c cs (mul cs x.2 (invol cs y.2))),
       add cs (mul cs x.1 y.2) (mul cs x.2 (invol cs y.1)))

theorem add_assoc : ∀ (sig : List K) (x y z : Cl K sig),
    add sig (add sig x y) z = add sig x (add sig y z)
  | [], a, b, c => F.add_assoc a b c
  | _ :: cs, x, y, z => Prod.ext (add_assoc cs x.1 y.1 z.1) (add_assoc cs x.2 y.2 z.2)

theorem add_comm : ∀ (sig : List K) (x y : Cl K sig), add sig x y = add sig y x
  | [], a, b => F.add_comm a b
  | _ :: cs, x, y => Prod.ext (add_comm cs x.1 y.1) (add_comm cs x.2 y.2)

theorem zero_add : ∀ (sig : List K) (x : Cl K sig), add sig (zero sig) x = x
  | [], a => F.zero_add a
  | _ :: cs, x => Prod.ext (zero_add cs x.1) (zero_add cs x.2)

theorem add_zero (sig : List K) (x : Cl K sig) : add sig x (zero sig) = x := by
  rw [add_comm, zero_add]

theorem add_left_neg : ∀ (sig : List K) (x : Cl K sig), add sig (neg sig x) x = zero sig
  | [], a => F.add_left_neg a
  | _ :: cs, x => Prod.ext (add_left_neg cs x.1) (add_left_neg cs x.2)

theorem add_right_neg (sig : List K) (x : Cl K sig) : add sig x (neg sig x) = zero sig := by
  rw [add_comm, add_left_neg]

theorem add_left_cancel {sig : List K} {x y z : Cl K sig}
    (h : add sig x y = add sig x z) : y = z := by
  have h1 := congrArg (add sig (neg sig x)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem neg_zero : ∀ (sig : List K), neg sig (zero sig : Cl K sig) = zero sig
  | [] => FieldK.neg_zero
  | _ :: cs => Prod.ext (neg_zero cs) (neg_zero cs)

theorem neg_neg : ∀ (sig : List K) (x : Cl K sig), neg sig (neg sig x) = x
  | [], a => FieldK.neg_neg a
  | _ :: cs, x => Prod.ext (neg_neg cs x.1) (neg_neg cs x.2)

theorem neg_add : ∀ (sig : List K) (x y : Cl K sig),
    neg sig (add sig x y) = add sig (neg sig x) (neg sig y)
  | [], a, b => FieldK.neg_add a b
  | _ :: cs, x, y => Prod.ext (neg_add cs x.1 y.1) (neg_add cs x.2 y.2)

theorem smul_zero : ∀ (k : K) (sig : List K), smul k sig (zero sig) = zero sig
  | k, [] => FieldK.mul_zero k
  | k, _ :: cs => Prod.ext (smul_zero k cs) (smul_zero k cs)

theorem zero_smul : ∀ (sig : List K) (x : Cl K sig), smul F.zero sig x = zero sig
  | [], a => FieldK.zero_mul a
  | _ :: cs, x => Prod.ext (zero_smul cs x.1) (zero_smul cs x.2)

theorem one_smul : ∀ (sig : List K) (x : Cl K sig), smul F.one sig x = x
  | [], a => F.one_mul a
  | _ :: cs, x => Prod.ext (one_smul cs x.1) (one_smul cs x.2)

theorem neg_one_smul : ∀ (sig : List K) (x : Cl K sig), smul (F.neg F.one) sig x = neg sig x
  | [], a => FieldK.neg_one_mul a
  | _ :: cs, x => Prod.ext (neg_one_smul cs x.1) (neg_one_smul cs x.2)

theorem smul_add : ∀ (k : K) (sig : List K) (x y : Cl K sig),
    smul k sig (add sig x y) = add sig (smul k sig x) (smul k sig y)
  | k, [], a, b => F.left_distrib k a b
  | k, _ :: cs, x, y => Prod.ext (smul_add k cs x.1 y.1) (smul_add k cs x.2 y.2)

theorem add_smul : ∀ (a b : K) (sig : List K) (x : Cl K sig),
    smul (F.add a b) sig x = add sig (smul a sig x) (smul b sig x)
  | a, b, [], x => FieldK.right_distrib a b x
  | a, b, _ :: cs, x => Prod.ext (add_smul a b cs x.1) (add_smul a b cs x.2)

theorem smul_smul : ∀ (a b : K) (sig : List K) (x : Cl K sig),
    smul a sig (smul b sig x) = smul (F.mul a b) sig x
  | a, b, [], x => (F.mul_assoc a b x).symm
  | a, b, _ :: cs, x => Prod.ext (smul_smul a b cs x.1) (smul_smul a b cs x.2)

theorem smul_neg : ∀ (k : K) (sig : List K) (x : Cl K sig),
    smul k sig (neg sig x) = neg sig (smul k sig x)
  | k, [], a => FieldK.mul_neg k a
  | k, _ :: cs, x => Prod.ext (smul_neg k cs x.1) (smul_neg k cs x.2)

theorem smul_eq_zero_iff {k : K} (hk : k ≠ F.zero) {sig : List K} {x : Cl K sig}
    (h : smul k sig x = zero sig) : x = zero sig := by
  have h1 := congrArg (smul (F.inv k) sig) h
  rw [smul_smul, F.mul_left_inv k hk, one_smul, smul_zero] at h1
  exact h1

theorem scalar_eq_smul_one : ∀ (k : K) (sig : List K), scalar k sig = smul k sig (one sig)
  | k, [] => (FieldK.mul_one k).symm
  | k, _ :: cs => Prod.ext (scalar_eq_smul_one k cs) (smul_zero k cs).symm

theorem scalar_inj : ∀ {sig : List K} {a b : K}, scalar a sig = scalar b sig → a = b
  | [], _, _, h => h
  | _ :: _, _, _, h => scalar_inj (congrArg Prod.fst h)

theorem one_ne_zero (sig : List K) : (one sig : Cl K sig) ≠ zero sig := by
  intro h
  have hs : scalar (F.one : K) sig = scalar F.zero sig := by
    rw [scalar_eq_smul_one, one_smul, scalar_eq_smul_one, zero_smul]
    exact h
  exact F.zero_ne_one (scalar_inj hs).symm

theorem invol_zero : ∀ (sig : List K), invol sig (zero sig : Cl K sig) = zero sig
  | [] => rfl
  | _ :: cs => Prod.ext (invol_zero cs) (by dsimp [invol, zero]; rw [invol_zero, neg_zero])

theorem invol_one : ∀ (sig : List K), invol sig (one sig : Cl K sig) = one sig
  | [] => rfl
  | _ :: cs => Prod.ext (invol_one cs) (by dsimp [invol, one]; rw [invol_zero, neg_zero])

theorem invol_add : ∀ (sig : List K) (x y : Cl K sig),
    invol sig (add sig x y) = add sig (invol sig x) (invol sig y)
  | [], _, _ => rfl
  | _ :: cs, x, y => Prod.ext (invol_add cs x.1 y.1)
      (by dsimp [invol, add]; rw [invol_add, neg_add])

theorem invol_neg : ∀ (sig : List K) (x : Cl K sig),
    invol sig (neg sig x) = neg sig (invol sig x)
  | [], _ => rfl
  | _ :: cs, x => Prod.ext (invol_neg cs x.1) (by dsimp [invol, neg]; rw [invol_neg])

theorem invol_smul : ∀ (k : K) (sig : List K) (x : Cl K sig),
    invol sig (smul k sig x) = smul k sig (invol sig x)
  | _, [], _ => rfl
  | k, _ :: cs, x => Prod.ext (invol_smul k cs x.1)
      (by dsimp [invol, smul]; rw [invol_smul, smul_neg])

theorem invol_scalar (k : K) (sig : List K) : invol sig (scalar k sig) = scalar k sig := by
  rw [scalar_eq_smul_one, invol_smul, invol_one]

theorem invol_invol : ∀ (sig : List K) (x : Cl K sig), invol sig (invol sig x) = x
  | [], _ => rfl
  | _ :: cs, x => Prod.ext (invol_invol cs x.1)
      (by dsimp [invol]; rw [invol_neg, neg_neg, invol_invol])

theorem zero_mul : ∀ (sig : List K) (x : Cl K sig), mul sig (zero sig) x = zero sig
  | [], x => FieldK.zero_mul x
  | _ :: cs, x => Prod.ext
      (by dsimp [mul, zero]; rw [zero_mul, zero_mul, smul_zero, add_zero])
      (by dsimp [mul, zero]; rw [zero_mul, zero_mul, add_zero])

theorem mul_zero : ∀ (sig : List K) (x : Cl K sig), mul sig x (zero sig) = zero sig
  | [], x => FieldK.mul_zero x
  | _ :: cs, x => Prod.ext
      (by dsimp [mul, zero]; rw [mul_zero, invol_zero, mul_zero, smul_zero, add_zero])
      (by dsimp [mul, zero]; rw [mul_zero, invol_zero, mul_zero, add_zero])

theorem one_mul : ∀ (sig : List K) (x : Cl K sig), mul sig (one sig) x = x
  | [], x => F.one_mul x
  | _ :: cs, x => Prod.ext
      (by dsimp [mul, one]; rw [one_mul, zero_mul, smul_zero, add_zero])
      (by dsimp [mul, one]; rw [one_mul, zero_mul, add_zero])

theorem mul_one : ∀ (sig : List K) (x : Cl K sig), mul sig x (one sig) = x
  | [], x => FieldK.mul_one x
  | _ :: cs, x => Prod.ext
      (by dsimp [mul, one]; rw [mul_one, invol_zero, mul_zero, smul_zero, add_zero])
      (by dsimp [mul, one]; rw [mul_zero, invol_one, mul_one, zero_add])

theorem smul_mul_left : ∀ (k : K) (sig : List K) (x y : Cl K sig),
    mul sig (smul k sig x) y = smul k sig (mul sig x y)
  | k, [], a, b => F.mul_assoc k a b
  | k, c :: cs, x, y => Prod.ext
      (by
        dsimp [mul, smul]
        rw [smul_mul_left, smul_mul_left, smul_smul, F.mul_comm c k, ← smul_smul, smul_add])
      (by dsimp [mul, smul]; rw [smul_mul_left, smul_mul_left, smul_add])

theorem smul_mul_right : ∀ (k : K) (sig : List K) (x y : Cl K sig),
    mul sig x (smul k sig y) = smul k sig (mul sig x y)
  | k, [], a, b => by
      dsimp [mul, smul]
      rw [← F.mul_assoc, F.mul_comm a k, F.mul_assoc]
  | k, c :: cs, x, y => Prod.ext
      (by
        dsimp [mul, smul]
        rw [smul_mul_right, invol_smul, smul_mul_right, smul_smul,
            F.mul_comm c k, ← smul_smul, smul_add])
      (by
        dsimp [mul, smul]
        rw [smul_mul_right, invol_smul, smul_mul_right, smul_add])

theorem neg_mul (sig : List K) (x y : Cl K sig) :
    mul sig (neg sig x) y = neg sig (mul sig x y) := by
  rw [← neg_one_smul, smul_mul_left, neg_one_smul]

theorem mul_neg (sig : List K) (x y : Cl K sig) :
    mul sig x (neg sig y) = neg sig (mul sig x y) := by
  rw [← neg_one_smul, smul_mul_right, neg_one_smul]

theorem neg_mul_neg (sig : List K) (x y : Cl K sig) :
    mul sig (neg sig x) (neg sig y) = mul sig x y := by
  rw [neg_mul, mul_neg, neg_neg]

theorem scalar_mul (k : K) (sig : List K) (x : Cl K sig) :
    mul sig (scalar k sig) x = smul k sig x := by
  rw [scalar_eq_smul_one, smul_mul_left, one_mul]

theorem mul_scalar (k : K) (sig : List K) (x : Cl K sig) :
    mul sig x (scalar k sig) = smul k sig x := by
  rw [scalar_eq_smul_one, smul_mul_right, mul_one]

theorem scalar_mul_scalar (a b : K) (sig : List K) :
    mul sig (scalar a sig) (scalar b sig) = scalar (F.mul a b) sig := by
  rw [scalar_mul, scalar_eq_smul_one b, smul_smul, ← scalar_eq_smul_one]

theorem left_distrib : ∀ (sig : List K) (x y z : Cl K sig),
    mul sig x (add sig y z) = add sig (mul sig x y) (mul sig x z)
  | [], a, b, c => F.left_distrib a b c
  | c :: cs, x, y, z => by
      apply Prod.ext <;> dsimp [mul, add]
      · rw [left_distrib, invol_add, left_distrib, smul_add]
        let A := mul cs x.1 y.1
        let B := mul cs x.1 z.1
        let C := smul c cs (mul cs x.2 (invol cs y.2))
        let D := smul c cs (mul cs x.2 (invol cs z.2))
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs B D)
        rw [add_assoc cs A B (add cs C D), ← add_assoc cs B C D, add_comm cs B C,
            add_assoc cs C B D, ← add_assoc cs A C (add cs B D)]
      · rw [left_distrib, invol_add, left_distrib]
        let A := mul cs x.1 y.2
        let B := mul cs x.1 z.2
        let C := mul cs x.2 (invol cs y.1)
        let D := mul cs x.2 (invol cs z.1)
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs B D)
        rw [add_assoc cs A B (add cs C D), ← add_assoc cs B C D, add_comm cs B C,
            add_assoc cs C B D, ← add_assoc cs A C (add cs B D)]

theorem right_distrib : ∀ (sig : List K) (x y z : Cl K sig),
    mul sig (add sig x y) z = add sig (mul sig x z) (mul sig y z)
  | [], a, b, c => FieldK.right_distrib a b c
  | c :: cs, x, y, z => by
      apply Prod.ext <;> dsimp [mul, add]
      · rw [right_distrib, right_distrib, smul_add]
        let A := mul cs x.1 z.1
        let B := mul cs y.1 z.1
        let C := smul c cs (mul cs x.2 (invol cs z.2))
        let D := smul c cs (mul cs y.2 (invol cs z.2))
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs B D)
        rw [add_assoc cs A B (add cs C D), ← add_assoc cs B C D, add_comm cs B C,
            add_assoc cs C B D, ← add_assoc cs A C (add cs B D)]
      · rw [right_distrib, right_distrib]
        let A := mul cs x.1 z.2
        let B := mul cs y.1 z.2
        let C := mul cs x.2 (invol cs z.1)
        let D := mul cs y.2 (invol cs z.1)
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs B D)
        rw [add_assoc cs A B (add cs C D), ← add_assoc cs B C D, add_comm cs B C,
            add_assoc cs C B D, ← add_assoc cs A C (add cs B D)]

theorem invol_mul : ∀ (sig : List K) (x y : Cl K sig),
    invol sig (mul sig x y) = mul sig (invol sig x) (invol sig y)
  | [], _, _ => rfl
  | _ :: cs, x, y => by
      apply Prod.ext <;> dsimp [invol, mul]
      · rw [invol_add, invol_mul, invol_smul, invol_mul, invol_neg, neg_mul, mul_neg, neg_neg]
      · rw [invol_add, neg_add, invol_mul, invol_mul, mul_neg, neg_mul]

theorem mul_assoc : ∀ (sig : List K) (x y z : Cl K sig),
    mul sig (mul sig x y) z = mul sig x (mul sig y z)
  | [], a, b, c => F.mul_assoc a b c
  | c :: cs, x, y, z => by
      apply Prod.ext <;> dsimp [mul]
      · rw [right_distrib, smul_mul_left, right_distrib, smul_add,
            left_distrib, invol_add, invol_mul, invol_mul, invol_invol, left_distrib, smul_add,
            smul_mul_right,
            mul_assoc cs x.1 y.1 z.1,
            mul_assoc cs x.2 (invol cs y.2) z.1,
            mul_assoc cs x.1 y.2 (invol cs z.2),
            mul_assoc cs x.2 (invol cs y.1) (invol cs z.2)]
        let A := mul cs x.1 (mul cs y.1 z.1)
        let B := smul c cs (mul cs x.2 (mul cs (invol cs y.2) z.1))
        let C := smul c cs (mul cs x.1 (mul cs y.2 (invol cs z.2)))
        let D := smul c cs (mul cs x.2 (mul cs (invol cs y.1) (invol cs z.2)))
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs D B)
        rw [add_assoc cs A B (add cs C D), add_comm cs B (add cs C D),
            add_assoc cs C D B, ← add_assoc cs A C (add cs D B)]
      · rw [right_distrib, smul_mul_left, right_distrib,
            left_distrib, invol_add, invol_smul, invol_mul, invol_mul, invol_invol,
            left_distrib, smul_mul_right,
            mul_assoc cs x.1 y.1 z.2,
            mul_assoc cs x.2 (invol cs y.2) z.2,
            mul_assoc cs x.1 y.2 (invol cs z.1),
            mul_assoc cs x.2 (invol cs y.1) (invol cs z.1)]
        let A := mul cs x.1 (mul cs y.1 z.2)
        let B := smul c cs (mul cs x.2 (mul cs (invol cs y.2) z.2))
        let C := mul cs x.1 (mul cs y.2 (invol cs z.1))
        let D := mul cs x.2 (mul cs (invol cs y.1) (invol cs z.1))
        change add cs (add cs A B) (add cs C D) = add cs (add cs A C) (add cs D B)
        rw [add_assoc cs A B (add cs C D), add_comm cs B (add cs C D),
            add_assoc cs C D B, ← add_assoc cs A C (add cs D B)]

theorem rev_zero : ∀ (sig : List K), rev sig (zero sig : Cl K sig) = zero sig
  | [] => rfl
  | _ :: cs => Prod.ext (rev_zero cs) (by dsimp [rev, zero]; rw [rev_zero, invol_zero])

theorem rev_one : ∀ (sig : List K), rev sig (one sig : Cl K sig) = one sig
  | [] => rfl
  | _ :: cs => Prod.ext (rev_one cs) (by dsimp [rev, one]; rw [rev_zero, invol_zero])

theorem rev_add : ∀ (sig : List K) (x y : Cl K sig),
    rev sig (add sig x y) = add sig (rev sig x) (rev sig y)
  | [], _, _ => rfl
  | _ :: cs, x, y => Prod.ext (rev_add cs x.1 y.1)
      (by dsimp [rev, add]; rw [rev_add, invol_add])

theorem rev_neg : ∀ (sig : List K) (x : Cl K sig),
    rev sig (neg sig x) = neg sig (rev sig x)
  | [], _ => rfl
  | _ :: cs, x => Prod.ext (rev_neg cs x.1)
      (by dsimp [rev, neg]; rw [rev_neg, invol_neg])

theorem rev_smul : ∀ (k : K) (sig : List K) (x : Cl K sig),
    rev sig (smul k sig x) = smul k sig (rev sig x)
  | _, [], _ => rfl
  | k, _ :: cs, x => Prod.ext (rev_smul k cs x.1)
      (by dsimp [rev, smul]; rw [rev_smul, invol_smul])

theorem rev_scalar (k : K) (sig : List K) : rev sig (scalar k sig) = scalar k sig := by
  rw [scalar_eq_smul_one, rev_smul, rev_one]

theorem invol_rev_comm : ∀ (sig : List K) (x : Cl K sig),
    invol sig (rev sig x) = rev sig (invol sig x)
  | [], _ => rfl
  | _ :: cs, x => Prod.ext (invol_rev_comm cs x.1)
      (by dsimp [invol, rev, neg]; rw [rev_neg, invol_neg, invol_rev_comm])

theorem rev_rev : ∀ (sig : List K) (x : Cl K sig), rev sig (rev sig x) = x
  | [], _ => rfl
  | _ :: cs, x => Prod.ext (rev_rev cs x.1)
      (by dsimp [rev]; rw [← invol_rev_comm, invol_invol, rev_rev])

theorem rev_mul : ∀ (sig : List K) (x y : Cl K sig),
    rev sig (mul sig x y) = mul sig (rev sig y) (rev sig x)
  | [], a, b => F.mul_comm a b
  | _ :: cs, x, y => by
      apply Prod.ext <;> dsimp [rev, mul]
      · rw [rev_add, rev_mul, rev_smul, rev_mul, ← invol_rev_comm, invol_invol]
      · rw [rev_add, invol_add, rev_mul, rev_mul, invol_mul, invol_mul,
            ← invol_rev_comm cs y.1, invol_invol, add_comm]

theorem conj_mul {sig : List K} {x x_inv : Cl K sig}
    (hx_left : mul sig x_inv x = one sig) (a b : Cl K sig) :
    mul sig (mul sig (mul sig x a) x_inv) (mul sig (mul sig x b) x_inv) =
    mul sig (mul sig x (mul sig a b)) x_inv := by
  calc
    mul sig (mul sig (mul sig x a) x_inv) (mul sig (mul sig x b) x_inv)
      = mul sig (mul sig x a) (mul sig x_inv (mul sig (mul sig x b) x_inv)) := mul_assoc _ _ _ _
    _ = mul sig (mul sig x a) (mul sig (mul sig x_inv (mul sig x b)) x_inv) := by
          rw [← mul_assoc sig x_inv (mul sig x b) x_inv]
    _ = mul sig (mul sig x a) (mul sig (mul sig (mul sig x_inv x) b) x_inv) := by
          rw [← mul_assoc sig x_inv x b]
    _ = mul sig (mul sig x a) (mul sig b x_inv) := by
          rw [hx_left, one_mul]
    _ = mul sig x (mul sig a (mul sig b x_inv)) := mul_assoc _ _ _ _
    _ = mul sig x (mul sig (mul sig a b) x_inv) := by rw [← mul_assoc sig a b x_inv]
    _ = mul sig (mul sig x (mul sig a b)) x_inv := (mul_assoc _ _ _ _).symm

end BasicAlgebra

/-! ### Vector Subspace `V`, Quadratic Form `Q`, and Universal Adjoint Orthogonality -/

section VectorsAndOrthogonality
variable {K : Type} [F : FieldK K]

def vecZero : (sig : List K) → Vec K sig
  | [] => ()
  | _ :: cs => (vecZero cs, F.zero)

def quadForm : (sig : List K) → Vec K sig → K
  | [], _ => F.zero
  | c :: cs, v => F.add (quadForm cs v.1) (F.mul c (F.mul v.2 v.2))

def embedVec : (sig : List K) → Vec K sig → Cl K sig
  | [], _ => F.zero
  | _ :: cs, v => (embedVec cs v.1, scalar v.2 cs)

def embedSub (c : K) (cs : List K) (y : Cl K cs) : Cl K (c :: cs) :=
  (y, zero cs)

def eTop (c : K) (cs : List K) : Cl K (c :: cs) :=
  (zero cs, one cs)

theorem embedSub_one (c : K) (cs : List K) : embedSub c cs (one cs) = one (c :: cs) := rfl

theorem embedSub_mul (c : K) (cs : List K) (a b : Cl K cs) :
    mul (c :: cs) (embedSub c cs a) (embedSub c cs b) = embedSub c cs (mul cs a b) := by
  apply Prod.ext <;> dsimp [mul, embedSub]
  · rw [zero_mul, smul_zero, add_zero]
  · rw [mul_zero, zero_mul, add_zero]

theorem embedVec_zero : ∀ (sig : List K), embedVec sig (vecZero sig) = zero sig
  | [] => rfl
  | _ :: cs => Prod.ext (embedVec_zero cs)
      (by dsimp [embedVec, vecZero, zero]; rw [scalar_eq_smul_one, zero_smul])

theorem embedVec_sub (c : K) (cs : List K) (v0 : Vec K cs) :
    embedVec (c :: cs) (v0, F.zero) = embedSub c cs (embedVec cs v0) :=
  Prod.ext rfl (by dsimp [embedVec, embedSub]; rw [scalar_eq_smul_one, zero_smul])

theorem embedVec_top (c : K) (cs : List K) :
    embedVec (c :: cs) (vecZero cs, F.one) = eTop c cs :=
  Prod.ext (embedVec_zero cs) (by dsimp [embedVec, eTop]; rw [scalar_eq_smul_one, one_smul])

theorem embedVec_neg_top (c : K) (cs : List K) :
    embedVec (c :: cs) (vecZero cs, F.neg F.one) = neg (c :: cs) (eTop c cs) :=
  Prod.ext (by dsimp [embedVec, neg, eTop]; rw [embedVec_zero, neg_zero])
           (by dsimp [embedVec, neg, eTop]; rw [scalar_eq_smul_one, neg_one_smul])

theorem embedVec_inj : ∀ {sig : List K} {u v : Vec K sig},
    embedVec sig u = embedVec sig v → u = v
  | [], (), (), _ => rfl
  | _ :: _, _, _, h =>
      Prod.ext (embedVec_inj (congrArg Prod.fst h)) (scalar_inj (congrArg Prod.snd h))

theorem invol_embedVec : ∀ (sig : List K) (v : Vec K sig),
    invol sig (embedVec sig v) = neg sig (embedVec sig v)
  | [], () => FieldK.neg_zero.symm
  | _ :: cs, v => Prod.ext (invol_embedVec cs v.1)
      (by dsimp [invol, embedVec, neg]; rw [invol_scalar])

theorem rev_embedVec : ∀ (sig : List K) (v : Vec K sig),
    rev sig (embedVec sig v) = embedVec sig v
  | [], () => rfl
  | _ :: cs, v => Prod.ext (rev_embedVec cs v.1)
      (by dsimp [rev, embedVec]; rw [rev_scalar, invol_scalar])

/-- **Fundamental Clifford Law:** `v^2 = Q(v) · 1` for all dimensions and signatures. -/
theorem embedVec_sq : ∀ (sig : List K) (v : Vec K sig),
    mul sig (embedVec sig v) (embedVec sig v) = scalar (quadForm sig v) sig
  | [], () => FieldK.mul_zero F.zero
  | c :: cs, v => by
      apply Prod.ext <;> dsimp [mul, embedVec, quadForm, scalar]
      · rw [embedVec_sq cs v.1, invol_scalar, scalar_mul,
            scalar_eq_smul_one, scalar_eq_smul_one, smul_smul, smul_smul,
            F.mul_assoc c v.2 v.2, ← add_smul, ← scalar_eq_smul_one]
      · rw [mul_scalar, invol_embedVec, scalar_mul, smul_neg, add_right_neg]

/-- **Universal Adjoint Orthogonality Theorem:**
    In ANY dimension and signature, whenever an invertible Clifford element `x` maps
    a vector `v ∈ V` to a vector `w ∈ V` via `Ad_x(v) = x v x⁻¹`, it preserves `Q`
    (`Q(w) = Q(v)`). -/
theorem adjoint_preserves_quadForm {sig : List K} {x x_inv : Cl K sig}
    (hx_right : mul sig x x_inv = one sig)
    (hx_left : mul sig x_inv x = one sig)
    {v w : Vec K sig}
    (hw : mul sig (mul sig x (embedVec sig v)) x_inv = embedVec sig w) :
    quadForm sig w = quadForm sig v := by
  apply scalar_inj (sig := sig)
  calc
    scalar (quadForm sig w) sig
      = mul sig (embedVec sig w) (embedVec sig w) := (embedVec_sq sig w).symm
    _ = mul sig (mul sig (mul sig x (embedVec sig v)) x_inv)
                (mul sig (mul sig x (embedVec sig v)) x_inv) := by rw [← hw]
    _ = mul sig (mul sig x (mul sig (embedVec sig v) (embedVec sig v))) x_inv :=
          conj_mul hx_left _ _
    _ = mul sig (mul sig x (scalar (quadForm sig v) sig)) x_inv := by rw [embedVec_sq]
    _ = smul (quadForm sig v) sig (mul sig x x_inv) := by
          rw [mul_scalar, smul_mul_left]
    _ = scalar (quadForm sig v) sig := by rw [hx_right, ← scalar_eq_smul_one]

/-- **Universal Scalar-Unit Trivial Action Theorem:**
    Every nonzero scalar `k · 1 ∈ (Cl⁺)ˣ` (`k ∈ Kˣ`) is invertible in `Cl⁺` and acts
    trivially (`Ad_{k·1}(y) = y`) on the entire Clifford algebra (and hence on `V`). -/
theorem scalar_unit_even_and_trivial_adjoint {sig : List K} {k : K} (hk : k ≠ F.zero) :
    invol sig (scalar k sig) = scalar k sig ∧
    mul sig (scalar k sig) (scalar (F.inv k) sig) = one sig ∧
    mul sig (scalar (F.inv k) sig) (scalar k sig) = one sig ∧
    ∀ y : Cl K sig, mul sig (mul sig (scalar k sig) y) (scalar (F.inv k) sig) = y := by
  refine ⟨invol_scalar k sig, ?_, ?_, ?_⟩
  · rw [scalar_mul_scalar, FieldK.mul_right_inv hk, scalar_eq_smul_one, one_smul]
  · rw [scalar_mul_scalar, F.mul_left_inv k hk, scalar_eq_smul_one, one_smul]
  · intro y
    rw [scalar_mul, mul_scalar, smul_smul, F.mul_comm (F.inv k) k,
        FieldK.mul_right_inv hk, one_smul]

end VectorsAndOrthogonality

/-! ### Pseudoscalar `ω` & Universal Reflection Obstruction (ALL `n ≥ 1`) -/

section PseudoscalarAndReflections

/-- Top-grade volume element (pseudoscalar) `ω = e_1 e_2 ... e_n`. -/
def omega {K : Type} [F : FieldK K] : (sig : List K) → Cl K sig
  | [] => F.one
  | _ :: cs => (zero cs, omega cs)

theorem omega_step_eq_mul {K : Type} [F : FieldK K] (c : K) (cs : List K) :
    omega (c :: cs) = mul (c :: cs) (embedSub c cs (omega cs)) (eTop c cs) := by
  apply Prod.ext <;> dsimp [omega, mul, embedSub, eTop]
  · rw [mul_zero, zero_mul, smul_zero, add_zero]
  · rw [mul_one, invol_zero, zero_mul, add_zero]

theorem invol_omega {K : Type} [F : FieldK K] : ∀ (sig : List K),
    invol sig (omega sig) =
      if sig.length % 2 = 0 then omega sig else neg sig (omega sig)
  | [] => rfl
  | _ :: cs => by
      have ih := invol_omega cs
      by_cases he : cs.length % 2 = 0
      · have ho' : ¬ ((cs.length + 1) % 2 = 0) := by omega
        dsimp [List.length]
        simp only [ho', ite_false]
        apply Prod.ext <;> dsimp [invol, omega, neg]
        · rw [invol_zero, neg_zero]
        · rw [ih]; simp [he]
      · have he' : (cs.length + 1) % 2 = 0 := by omega
        dsimp [List.length]
        simp only [he', ite_true]
        apply Prod.ext <;> dsimp [invol, omega, neg]
        · exact invol_zero cs
        · rw [ih]; simp [he, neg_neg]

/-- Simultaneous structural induction proving:
    1. Every even element (`invol x = x`) commutes with `ω` in ALL dimensions `n ≥ 0`.
    2. Every odd element (`invol y = -y`) commutes with `ω` in odd dimensions (and `n = 0`)
       and anticommutes with `ω` in nonzero even dimensions. -/
theorem even_and_odd_omega_comm {K : Type} [F : FieldK K] : ∀ (sig : List K),
    (∀ x : Cl K sig, invol sig x = x → mul sig x (omega sig) = mul sig (omega sig) x) ∧
    (∀ y : Cl K sig, invol sig y = neg sig y →
      mul sig y (omega sig) =
        if sig.length = 0 ∨ sig.length % 2 = 1 then mul sig (omega sig) y
        else neg sig (mul sig (omega sig) y))
  | [] =>
      ⟨fun x _ => F.mul_comm x F.one,
       fun y _ => by dsimp [List.length, mul, omega]; exact F.mul_comm y F.one⟩
  | [c] =>
      ⟨fun x _ => by
        apply Prod.ext <;> dsimp [mul, omega, invol, smul, add, zero, one]
        · rw [FieldK.mul_zero, F.zero_add, FieldK.mul_one, FieldK.zero_mul,
              F.zero_add, F.one_mul]
        · rw [FieldK.mul_one, FieldK.mul_zero, FieldK.add_zero, F.one_mul,
              FieldK.zero_mul, F.zero_add],
       fun y _ => by
        dsimp [List.length]
        apply Prod.ext <;> dsimp [mul, omega, invol, smul, add, zero, one]
        · rw [FieldK.mul_zero, F.zero_add, FieldK.mul_one, FieldK.zero_mul,
              F.zero_add, F.one_mul]
        · rw [FieldK.mul_one, FieldK.mul_zero, FieldK.add_zero, F.one_mul,
              FieldK.zero_mul, F.zero_add]⟩
  | c :: d :: ds => by
      let cs := d :: ds
      obtain ⟨ih_even, ih_odd⟩ := even_and_odd_omega_comm cs
      have hcs_ne0 : ¬ (cs.length = 0) := by dsimp [cs, List.length]; omega
      constructor
      · intro x hx
        have hx0 : invol cs x.1 = x.1 := congrArg Prod.fst hx
        have hx1_raw : neg cs (invol cs x.2) = x.2 := congrArg Prod.snd hx
        have hx1 : invol cs x.2 = neg cs x.2 := by
          have h := congrArg (neg cs) hx1_raw
          rw [neg_neg] at h
          exact h
        apply Prod.ext
        · change add cs (mul cs x.1 (zero cs)) (smul c cs (mul cs x.2 (invol cs (omega cs)))) =
                 add cs (mul cs (zero cs) x.1) (smul c cs (mul cs (omega cs) (invol cs x.2)))
          rw [mul_zero, zero_mul, zero_add, zero_add, hx1]
          congr 1
          rw [mul_neg, invol_omega cs]
          by_cases he : cs.length % 2 = 0
          · simp only [he, ite_true]
            have ho := ih_odd x.2 hx1
            have hmod1 : ¬ (cs.length % 2 = 1) := by omega
            simp only [hcs_ne0, hmod1, or_self, ite_false] at ho
            exact ho
          · have hmod1 : cs.length % 2 = 1 := by omega
            simp only [he, ite_false, mul_neg]
            have ho := ih_odd x.2 hx1
            simp only [hmod1, or_true, ite_true] at ho
            rw [ho]
        · change add cs (mul cs x.1 (omega cs)) (mul cs x.2 (invol cs (zero cs))) =
                 add cs (mul cs (zero cs) x.2) (mul cs (omega cs) (invol cs x.1))
          rw [invol_zero, mul_zero, add_zero, zero_mul, zero_add, hx0, ih_even x.1 hx0]
      · intro y hy
        have hy0 : invol cs y.1 = neg cs y.1 := congrArg Prod.fst hy
        have hy1_raw : neg cs (invol cs y.2) = neg cs y.2 := congrArg Prod.snd hy
        have hy1 : invol cs y.2 = y.2 := by
          have h := congrArg (neg cs) hy1_raw
          rw [neg_neg, neg_neg] at h
          exact h
        have hne_top : ¬ ((c :: d :: ds).length = 0) := by dsimp [List.length]; omega
        by_cases hodd : (c :: d :: ds).length % 2 = 1
        · simp only [hodd, or_true, ite_true]
          have hcs_even : cs.length % 2 = 0 := by dsimp [cs, List.length] at hodd ⊢; omega
          apply Prod.ext
          · change add cs (mul cs y.1 (zero cs)) (smul c cs (mul cs y.2 (invol cs (omega cs)))) =
                   add cs (mul cs (zero cs) y.1) (smul c cs (mul cs (omega cs) (invol cs y.2)))
            rw [mul_zero, zero_mul, zero_add, zero_add, hy1, invol_omega cs]
            simp only [hcs_even, ite_true]
            rw [ih_even y.2 hy1]
          · change add cs (mul cs y.1 (omega cs)) (mul cs y.2 (invol cs (zero cs))) =
                   add cs (mul cs (zero cs) y.2) (mul cs (omega cs) (invol cs y.1))
            rw [invol_zero, mul_zero, add_zero, zero_mul, zero_add, hy0, mul_neg]
            have ho := ih_odd y.1 hy0
            have hmod1 : ¬ (cs.length % 2 = 1) := by omega
            simp only [hcs_ne0, hmod1, or_self, ite_false] at ho
            exact ho
        · simp only [hne_top, hodd, or_self, ite_false]
          have hcs_odd : cs.length % 2 = 1 := by dsimp [cs, List.length] at hodd ⊢; omega
          have hcs_ne_even : ¬ (cs.length % 2 = 0) := by omega
          apply Prod.ext
          · change add cs (mul cs y.1 (zero cs)) (smul c cs (mul cs y.2 (invol cs (omega cs)))) =
                   neg cs (add cs (mul cs (zero cs) y.1) (smul c cs (mul cs (omega cs) (invol cs y.2))))
            rw [mul_zero, zero_mul, zero_add, zero_add, hy1, invol_omega cs]
            simp only [hcs_ne_even, ite_false, mul_neg, smul_neg]
            rw [ih_even y.2 hy1]
          · change add cs (mul cs y.1 (omega cs)) (mul cs y.2 (invol cs (zero cs))) =
                   neg cs (add cs (mul cs (zero cs) y.2) (mul cs (omega cs) (invol cs y.1)))
            rw [invol_zero, mul_zero, add_zero, zero_mul, zero_add, hy0, mul_neg, neg_neg]
            have ho := ih_odd y.1 hy0
            simp only [hcs_odd, or_true, ite_true] at ho
            exact ho

/-- **Pseudoscalar Commutation with Even Subalgebra (ALL dimensions `n`):**
    Every even element `x ∈ Cl(K, sig)⁺` commutes with `ω`. -/
theorem even_comm_omega {K : Type} [FieldK K] {sig : List K} {x : Cl K sig}
    (hx : invol sig x = x) :
    mul sig x (omega sig) = mul sig (omega sig) x :=
  (even_and_odd_omega_comm sig).1 x hx

/-- **Pseudoscalar Centrality in Odd Dimensions (`n = 2m + 1`):**
    Over any field of characteristic `≠ 2`, when `dim V` is odd, `ω` is central in the
    ENTIRE Clifford algebra `Cl(K, sig)` (`x * ω = ω * x` for ALL `x`, even or odd). -/
theorem odd_dim_omega_central {K : Type} [FC : FieldCharNeTwo K] {sig : List K}
    (hodd : sig.length % 2 = 1) (x : Cl K sig) :
    mul sig x (omega sig) = mul sig (omega sig) x := by
  let x_even := add sig x (invol sig x)
  let x_odd := sub sig x (invol sig x)
  have he : invol sig x_even = x_even := by
    dsimp [x_even]
    rw [invol_add, invol_invol, add_comm]
  have ho : invol sig x_odd = neg sig x_odd := by
    dsimp [x_odd, sub]
    rw [invol_add, invol_neg, invol_invol, neg_add, neg_neg, add_comm]
  have hcomm_e : mul sig x_even (omega sig) = mul sig (omega sig) x_even :=
    even_comm_omega he
  have hcomm_o : mul sig x_odd (omega sig) = mul sig (omega sig) x_odd := by
    have h := (even_and_odd_omega_comm sig).2 x_odd ho
    simp only [hodd, or_true, ite_true] at h
    exact h
  have h2x : smul FieldK.two sig x = add sig x_even x_odd := by
    dsimp [x_even, x_odd, sub, FieldK.two]
    rw [add_smul, one_smul, add_assoc sig x (invol sig x),
        ← add_assoc sig (invol sig x) x (neg sig (invol sig x)),
        add_comm sig (invol sig x) x,
        add_assoc sig x (invol sig x) (neg sig (invol sig x)),
        add_right_neg, add_zero]
  have h2_comm : smul FieldK.two sig (mul sig x (omega sig)) =
                 smul FieldK.two sig (mul sig (omega sig) x) := by
    rw [← smul_mul_left, ← smul_mul_right, h2x, right_distrib, left_distrib, hcomm_e, hcomm_o]
  have hdiff : smul FieldK.two sig (sub sig (mul sig x (omega sig)) (mul sig (omega sig) x)) =
               zero sig := by
    dsimp [sub]
    rw [smul_add, smul_neg, h2_comm, add_right_neg]
  have hzero := smul_eq_zero_iff FC.two_ne_zero hdiff
  have h1 := congrArg (fun z => add sig z (mul sig (omega sig) x)) hzero
  dsimp [sub] at h1
  rw [add_assoc, add_left_neg, add_zero, zero_add] at h1
  exact h1

theorem omega_ne_neg_omega {K : Type} [FieldCharNeTwo K] :
    ∀ (sig : List K), omega sig ≠ neg sig (omega sig)
  | [] => FieldK.one_ne_neg_one
  | _ :: cs => fun h => omega_ne_neg_omega cs (congrArg Prod.snd h)

/-- Helper: if conjugation by `(x, x_inv)` fixes the image of every basis vector of a
    sub-signature `subSig` under a unital multiplicative map `ι`, then it fixes `ι(ω)`. -/
private theorem conj_fixes_mapped_omega {K : Type} [F : FieldK K]
    {bigSig : List K} {x x_inv : Cl K bigSig}
    (hx_right : mul bigSig x x_inv = one bigSig)
    (hx_left : mul bigSig x_inv x = one bigSig) :
    ∀ (subSig : List K) (ι : Cl K subSig → Cl K bigSig),
      ι (one subSig) = one bigSig →
      (∀ a b : Cl K subSig, ι (mul subSig a b) = mul bigSig (ι a) (ι b)) →
      (∀ u : Vec K subSig,
        mul bigSig (mul bigSig x (ι (embedVec subSig u))) x_inv = ι (embedVec subSig u)) →
      mul bigSig (mul bigSig x (ι (omega subSig))) x_inv = ι (omega subSig)
  | [], ι, hι1, _, _ => by
      change mul bigSig (mul bigSig x (ι (one []))) x_inv = ι (one [])
      rw [hι1, mul_one, hx_right]
  | d :: ds, ι, hι1, hι_mul, hfix => by
      rw [omega_step_eq_mul d ds, hι_mul]
      have ih := conj_fixes_mapped_omega hx_right hx_left ds (fun z => ι (embedSub d ds z))
        (by dsimp only; rw [embedSub_one, hι1])
        (fun a b => by dsimp only; rw [← embedSub_mul, hι_mul])
        (fun u => by dsimp only; rw [← embedVec_sub]; exact hfix (u, F.zero))
      have htop : mul bigSig (mul bigSig x (ι (eTop d ds))) x_inv = ι (eTop d ds) := by
        rw [← embedVec_top]
        exact hfix (vecZero ds, F.one)
      rw [← conj_mul hx_left, ih, htop]

/-- Hyperplane reflection `r_{e_top}(v_0, t) = (v_0, -t)` across `e_top^⊥` in `Vec K (c :: cs)`. -/
def reflTop {K : Type} [F : FieldK K] (c : K) (cs : List K) (v : Vec K (c :: cs)) :
    Vec K (c :: cs) :=
  (v.1, F.neg v.2)

theorem reflTop_preserves_quadForm {K : Type} [F : FieldK K] (c : K) (cs : List K)
    (v : Vec K (c :: cs)) :
    quadForm (c :: cs) (reflTop c cs v) = quadForm (c :: cs) v := by
  dsimp [quadForm, reflTop]
  rw [FieldK.neg_mul_neg]

theorem reflTop_involutive {K : Type} [FieldK K] (c : K) (cs : List K)
    (v : Vec K (c :: cs)) :
    reflTop c cs (reflTop c cs v) = v :=
  Prod.ext rfl (FieldK.neg_neg v.2)

theorem reflTop_nontrivial {K : Type} [FieldCharNeTwo K] (c : K) (cs : List K) :
    reflTop c cs (vecZero cs, FieldK.one) ≠ (vecZero cs, FieldK.one) :=
  fun h => FieldK.one_ne_neg_one (congrArg Prod.snd h).symm

/-- Core lemma: NO invertible element `x` that commutes with `ω_{c :: cs}` can induce
    `reflTop` via the ordinary adjoint action `v ↦ x v x⁻¹`. -/
theorem no_omega_commuting_unit_induces_reflTop {K : Type} [FieldCharNeTwo K]
    (c : K) (cs : List K) {x x_inv : Cl K (c :: cs)}
    (hx_right : mul (c :: cs) x x_inv = one (c :: cs))
    (hx_left : mul (c :: cs) x_inv x = one (c :: cs))
    (hcomm : mul (c :: cs) x (omega (c :: cs)) = mul (c :: cs) (omega (c :: cs)) x)
    (hrefl : ∀ v : Vec K (c :: cs),
      mul (c :: cs) (mul (c :: cs) x (embedVec (c :: cs) v)) x_inv =
        embedVec (c :: cs) (reflTop c cs v)) :
    False := by
  let bigSig := c :: cs
  have hpos : mul bigSig (mul bigSig x (omega bigSig)) x_inv = omega bigSig := by
    rw [hcomm, mul_assoc, hx_right, mul_one]
  have hsub : mul bigSig (mul bigSig x (embedSub c cs (omega cs))) x_inv =
              embedSub c cs (omega cs) :=
    conj_fixes_mapped_omega hx_right hx_left cs (embedSub c cs)
      (embedSub_one c cs)
      (fun a b => (embedSub_mul c cs a b).symm)
      (fun u => by
        rw [← embedVec_sub, hrefl (u, FieldK.zero)]
        dsimp [reflTop]
        rw [FieldK.neg_zero, embedVec_sub])
  have htop : mul bigSig (mul bigSig x (eTop c cs)) x_inv = neg bigSig (eTop c cs) := by
    conv => lhs; rw [← embedVec_top]
    rw [hrefl (vecZero cs, FieldK.one)]
    dsimp [reflTop]
    exact embedVec_neg_top c cs
  have hneg : mul bigSig (mul bigSig x (omega bigSig)) x_inv = neg bigSig (omega bigSig) := by
    rw [omega_step_eq_mul c cs, ← conj_mul hx_left, hsub, htop, mul_neg]
  exact omega_ne_neg_omega bigSig (hpos.symm.trans hneg)

/-- **Universal Even-Rotor Reflection Obstruction (ALL dimensions `n ≥ 1`):**
    Over ANY field `K` with `char(K) ≠ 2` and ANY `n = 1 + |cs| ≥ 1`, the orthogonal
    reflection `reflTop ∈ O(V, Q)` is NEVER induced via `Ad_x(v) = x v x⁻¹` by ANY
    invertible even element `x ∈ (Cl(K, c :: cs)⁺)ˣ`. -/
theorem even_unit_never_covers_orthogonal_reflection {K : Type} [FieldCharNeTwo K]
    (c : K) (cs : List K) {x x_inv : Cl K (c :: cs)}
    (heven : invol (c :: cs) x = x)
    (hx_right : mul (c :: cs) x x_inv = one (c :: cs))
    (hx_left : mul (c :: cs) x_inv x = one (c :: cs)) :
    ¬ (∀ v : Vec K (c :: cs),
        mul (c :: cs) (mul (c :: cs) x (embedVec (c :: cs) v)) x_inv =
          embedVec (c :: cs) (reflTop c cs v)) :=
  no_omega_commuting_unit_induces_reflTop c cs hx_right hx_left (even_comm_omega heven)

/-- **Odd-Dimension Total Ordinary-Adjoint Obstruction (`n = 2m + 1 ≥ 1`):**
    In EVERY odd dimension `n = 2m + 1`, NOT EVEN `Pin(V, Q)` or `(Cl(V, Q))ˣ` can
    induce `reflTop ∈ O(V, Q)` via the ordinary adjoint map `Ad_x(v) = x v x⁻¹`. -/
theorem odd_dim_no_clifford_unit_covers_reflection {K : Type} [FieldCharNeTwo K]
    (c : K) (cs : List K) (hodd : (c :: cs).length % 2 = 1)
    {x x_inv : Cl K (c :: cs)}
    (hx_right : mul (c :: cs) x x_inv = one (c :: cs))
    (hx_left : mul (c :: cs) x_inv x = one (c :: cs)) :
    ¬ (∀ v : Vec K (c :: cs),
        mul (c :: cs) (mul (c :: cs) x (embedVec (c :: cs) v)) x_inv =
          embedVec (c :: cs) (reflTop c cs v)) :=
  no_omega_commuting_unit_induces_reflTop c cs hx_right hx_left (odd_dim_omega_central hodd x)

end PseudoscalarAndReflections

/-! ### Universal Spin Group & Universal Kernel-Two Theorem (ALL `n ≥ 0`) -/

section UniversalSpinGroup
variable {K : Type} [FC : FieldCharNeTwo K]

/-- An element `x ∈ Cl(K, sig)` lies in `Spin(K, sig)` iff:
    1. `x ∈ Cl⁺` (`invol x = x`),
    2. `x * x̃ = 1` and `x̃ * x = 1` (unit Clifford norm, so `x⁻¹ = x̃`), and
    3. `x V x⁻¹ ⊆ V` (vector-space stabilization / Lipschitz condition). -/
def IsSpin (sig : List K) (x : Cl K sig) : Prop :=
  invol sig x = x ∧
  mul sig x (rev sig x) = one sig ∧
  mul sig (rev sig x) x = one sig ∧
  ∀ v : Vec K sig, ∃ w : Vec K sig,
    mul sig (mul sig x (embedVec sig v)) (rev sig x) = embedVec sig w

theorem one_mem_spin (sig : List K) : IsSpin sig (one sig : Cl K sig) := by
  refine ⟨invol_one sig, ?_, ?_, ?_⟩
  · rw [rev_one, one_mul]
  · rw [rev_one, one_mul]
  · intro v
    exact ⟨v, by rw [rev_one, one_mul, mul_one]⟩

theorem neg_one_mem_spin (sig : List K) : IsSpin sig (neg sig (one sig) : Cl K sig) := by
  refine ⟨by rw [invol_neg, invol_one], ?_, ?_, ?_⟩
  · rw [rev_neg, rev_one, neg_mul_neg, one_mul]
  · rw [rev_neg, rev_one, neg_mul_neg, one_mul]
  · intro v
    exact ⟨v, by rw [rev_neg, rev_one, neg_mul, neg_mul_neg, one_mul, mul_one]⟩

theorem one_ne_neg_one_cl (sig : List K) : (one sig : Cl K sig) ≠ neg sig (one sig) := by
  intro h
  have hs : scalar (FieldK.one : K) sig = scalar (FieldK.neg FieldK.one) sig := by
    rw [scalar_eq_smul_one, one_smul, scalar_eq_smul_one, neg_one_smul]
    exact h
  exact FieldK.one_ne_neg_one (scalar_inj hs)

theorem eq_zero_of_eq_neg_cl {sig : List K} {z : Cl K sig} (h : z = neg sig z) :
    z = zero sig := by
  have h2 : smul FieldK.two sig z = zero sig := by
    unfold FieldK.two
    rw [add_smul, one_smul]
    calc
      add sig z z = add sig z (neg sig z) := congrArg (add sig z) h
      _ = zero sig := add_right_neg sig z
  exact smul_eq_zero_iff FC.two_ne_zero h2

/-- Key structural lemma: in ANY nondegenerate Clifford algebra `Cl(K, sig)`
    (`∀ c ∈ sig, c ≠ 0`) with `char(K) ≠ 2`, an even element `x ∈ Cl⁺` that commutes
    with every vector in `V` must be a scalar multiple of `1` (`x = k · 1`). -/
theorem even_centralizer_of_V_eq_scalar :
    ∀ (sig : List K), (∀ c ∈ sig, c ≠ FieldK.zero) →
      ∀ x : Cl K sig, invol sig x = x →
        (∀ v : Vec K sig, mul sig x (embedVec sig v) = mul sig (embedVec sig v) x) →
        ∃ k : K, x = scalar k sig
  | [], _, x, _, _ => ⟨x, rfl⟩
  | c :: cs, hsig, x, hx_even, hcomm => by
      have hc : c ≠ FieldK.zero := hsig c (List.Mem.head cs)
      have hcs : ∀ d ∈ cs, d ≠ FieldK.zero := fun d hd => hsig d (List.Mem.tail c hd)
      have hx0 : invol cs x.1 = x.1 := congrArg Prod.fst hx_even
      have hx1_raw : neg cs (invol cs x.2) = x.2 := congrArg Prod.snd hx_even
      have hx1 : invol cs x.2 = neg cs x.2 := by
        have h := congrArg (neg cs) hx1_raw
        rw [neg_neg] at h
        exact h
      have htop := hcomm (vecZero cs, FieldK.one)
      rw [embedVec_top] at htop
      have htop_fst : (mul (c :: cs) x (eTop c cs)).1 =
                      (mul (c :: cs) (eTop c cs) x).1 := congrArg Prod.fst htop
      dsimp [mul, eTop] at htop_fst
      rw [mul_zero, zero_mul, zero_add, zero_add, invol_one, mul_one,
          one_mul, hx1, smul_neg] at htop_fst
      have hcx1_zero : smul c cs x.2 = zero cs := eq_zero_of_eq_neg_cl htop_fst
      have hx2_zero : x.2 = zero cs := smul_eq_zero_iff hc hcx1_zero
      have hsub_comm : ∀ u : Vec K cs,
          mul cs x.1 (embedVec cs u) = mul cs (embedVec cs u) x.1 := by
        intro u
        have hu := congrArg Prod.fst (hcomm (u, FieldK.zero))
        rw [embedVec_sub] at hu
        dsimp [mul, embedSub] at hu
        rw [hx2_zero, invol_zero, zero_mul, smul_zero, add_zero, add_zero] at hu
        exact hu
      obtain ⟨k, hk⟩ := even_centralizer_of_V_eq_scalar cs hcs x.1 hx0 hsub_comm
      exact ⟨k, Prod.ext hk hx2_zero⟩

/-- **Universal Spin Kernel-Two Theorem (ALL dimensions `n ≥ 0`):**
    Over ANY field `K` of characteristic `≠ 2` and ANY nondegenerate quadratic signature
    `sig : List K` (`∀ c ∈ sig, c ≠ 0`), `+1` and `-1` are distinct elements of
    `Spin(K, sig)`, and an element `x ∈ Spin(K, sig)` acts trivially on `V` under the
    adjoint map `Ad_x(v) = x v x⁻¹` IF AND ONLY IF `x = +1` or `x = -1`. -/
theorem spin_adjoint_kernel_eq_pm_one (sig : List K) (hsig : ∀ c ∈ sig, c ≠ FieldK.zero) :
    IsSpin sig (one sig : Cl K sig) ∧
    IsSpin sig (neg sig (one sig) : Cl K sig) ∧
    (one sig : Cl K sig) ≠ neg sig (one sig) ∧
    ∀ x : Cl K sig, IsSpin sig x →
      ((∀ v : Vec K sig, mul sig (mul sig x (embedVec sig v)) (rev sig x) = embedVec sig v) ↔
       (x = one sig ∨ x = neg sig (one sig))) := by
  refine ⟨one_mem_spin sig, neg_one_mem_spin sig, one_ne_neg_one_cl sig, ?_⟩
  intro x ⟨heven, hnormR, hnormL, _⟩
  constructor
  · intro htriv
    have hcomm : ∀ v : Vec K sig, mul sig x (embedVec sig v) = mul sig (embedVec sig v) x := by
      intro v
      have h1 := congrArg (fun z => mul sig z x) (htriv v)
      dsimp only at h1
      rw [mul_assoc sig (mul sig x (embedVec sig v)) (rev sig x) x, hnormL, mul_one] at h1
      exact h1
    obtain ⟨k, rfl⟩ := even_centralizer_of_V_eq_scalar sig hsig x heven hcomm
    have hk_sq : FieldK.mul k k = FieldK.one := by
      apply scalar_inj (sig := sig)
      rw [← scalar_mul_scalar]
      conv => lhs; arg 3; rw [← rev_scalar k sig]
      rw [hnormR, scalar_eq_smul_one, one_smul]
    cases FieldK.sq_eq_one_iff.mp hk_sq with
    | inl hk1 =>
        left
        rw [hk1, scalar_eq_smul_one, one_smul]
    | inr hkn1 =>
        right
        rw [hkn1, scalar_eq_smul_one, neg_one_smul]
  · intro hpm v
    cases hpm with
    | inl h1 => rw [h1, rev_one, one_mul, mul_one]
    | inr hn1 => rw [hn1, rev_neg, rev_one, neg_mul, neg_mul_neg, one_mul, mul_one]

end UniversalSpinGroup

end Cl

end Conjecture00000007606
