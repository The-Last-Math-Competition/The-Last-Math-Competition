/-
  CliffordDecomp/Algebra.lean
  Inductive Chevalley–Cayley–Dickson construction of the Clifford algebra `Cl(n, q)`
  over any `CommRing2 K` (commutative ring with invertible 2), together with:
  - Associative unital K-algebra laws
  - Main grade involution and reversion anti-involution
  - Quadratic form `quadForm`, polar bilinear form `polarForm`, vector embedding `vec`
  - Fundamental Clifford relation `vec(v)^2 = scalar(Q(v))`
  - Universal property of the Clifford algebra (existence and uniqueness)
-/
import CliffordDecomp.RatQ

namespace CliffordDecomp

section CliffordSpace
variable {K : Type u} [CommRing2 K]

/-- Tail of a tuple indexed by `Fin (n + 1)`. -/
def finTail {α : Type v} {n : Nat} (f : Fin (n + 1) → α) : Fin n → α :=
  fun i => f i.succ

/-- Head of a tuple indexed by `Fin (n + 1)`. -/
def finHead {α : Type v} {n : Nat} (f : Fin (n + 1) → α) : α :=
  f ⟨0, Nat.zero_lt_succ n⟩

/-- Underlying `2^n`-dimensional module of the Clifford algebra over `K^n`.
    Under `(x0, x1) : ClSpace K (n + 1)`, the pair represents `x0 + e_0 * x1`. -/
abbrev ClSpace (K : Type u) : Nat → Type u
  | 0 => K
  | n + 1 => ClSpace K n × ClSpace K n

namespace ClSpace

def zero : {n : Nat} → ClSpace K n
  | 0 => (0 : K)
  | _ + 1 => (zero, zero)

def one : {n : Nat} → ClSpace K n
  | 0 => (1 : K)
  | _ + 1 => (one, zero)

def scalar : {n : Nat} → K → ClSpace K n
  | 0, c => c
  | _ + 1, c => (scalar c, zero)

def scalarPart : {n : Nat} → ClSpace K n → K
  | 0, c => c
  | _ + 1, (x0, _) => scalarPart x0

def add : {n : Nat} → ClSpace K n → ClSpace K n → ClSpace K n
  | 0, a, b => a + b
  | _ + 1, (x0, x1), (y0, y1) => (add x0 y0, add x1 y1)

def neg : {n : Nat} → ClSpace K n → ClSpace K n
  | 0, a => -a
  | _ + 1, (x0, x1) => (neg x0, neg x1)

def sub {n : Nat} (x y : ClSpace K n) : ClSpace K n :=
  add x (neg y)

def smul : {n : Nat} → K → ClSpace K n → ClSpace K n
  | 0, c, a => c * a
  | _ + 1, c, (x0, x1) => (smul c x0, smul c x1)

/-- Main grade involution `X ↦ X̂`, acting by `(-1)^k` on grade `k`. -/
def invol : {n : Nat} → ClSpace K n → ClSpace K n
  | 0, a => a
  | _ + 1, (x0, x1) => (invol x0, neg (invol x1))

/-- Reversion anti-involution `X ↦ X̃`, reversing products of vectors. -/
def rev : {n : Nat} → ClSpace K n → ClSpace K n
  | 0, a => a
  | _ + 1, (x0, x1) => (rev x0, invol (rev x1))

/-- Clifford geometric product for orthogonal quadratic form `q : Fin n → K`:
    `(x0 + e_0 x1)(y0 + e_0 y1) = (x0 y0 + q_0 x̂1 y1) + e_0 (x1 y0 + x̂0 y1)`. -/
def mul : {n : Nat} → (Fin n → K) → ClSpace K n → ClSpace K n → ClSpace K n
  | 0, _, a, b => a * b
  | _ + 1, q, (x0, x1), (y0, y1) =>
      let q' := finTail q
      let q0 := finHead q
      (add (mul q' x0 y0) (smul q0 (mul q' (invol x1) y1)),
       add (mul q' x1 y0) (mul q' (invol x0) y1))

/-! ### Module & Involution Laws -/

theorem add_assoc {n : Nat} (x y z : ClSpace K n) : add (add x y) z = add x (add y z) := by
  induction n with
  | zero => exact CommRing2.add_assoc x y z
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    exact Prod.ext (ih x0 y0 z0) (ih x1 y1 z1)

theorem add_comm {n : Nat} (x y : ClSpace K n) : add x y = add y x := by
  induction n with
  | zero => exact CommRing2.add_comm x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem add_left_comm {n : Nat} (x y z : ClSpace K n) : add x (add y z) = add y (add x z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem zero_add {n : Nat} (x : ClSpace K n) : add zero x = x := by
  induction n with
  | zero => exact CommRing2.zero_add x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem add_zero {n : Nat} (x : ClSpace K n) : add x zero = x := by
  rw [add_comm, zero_add]

theorem neg_add_cancel {n : Nat} (x : ClSpace K n) : add (neg x) x = zero := by
  induction n with
  | zero => exact CommRing2.neg_add_cancel x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem add_neg_cancel {n : Nat} (x : ClSpace K n) : add x (neg x) = zero := by
  rw [add_comm, neg_add_cancel]

theorem add_left_cancel {n : Nat} {x y z : ClSpace K n} (h : add x y = add x z) : y = z := by
  have h1 : add (neg x) (add x y) = add (neg x) (add x z) := congrArg (add (neg x)) h
  rw [← add_assoc, neg_add_cancel, zero_add, ← add_assoc, neg_add_cancel, zero_add] at h1
  exact h1

theorem sub_self {n : Nat} (x : ClSpace K n) : sub x x = zero :=
  add_neg_cancel x

theorem sub_eq_zero_iff {n : Nat} {x y : ClSpace K n} : sub x y = zero ↔ x = y := by
  constructor
  · intro h
    have h1 : add (sub x y) y = add zero y := congrArg (add · y) h
    unfold sub at h1
    rw [add_assoc, neg_add_cancel, add_zero, zero_add] at h1
    exact h1
  · intro h; rw [h, sub_self]

theorem neg_zero {n : Nat} : neg (zero : ClSpace K n) = zero := by
  induction n with
  | zero => exact CommRing2.neg_zero
  | succ n ih => exact Prod.ext ih ih

theorem neg_neg {n : Nat} (x : ClSpace K n) : neg (neg x) = x := by
  induction n with
  | zero => exact CommRing2.neg_neg x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem neg_add {n : Nat} (x y : ClSpace K n) : neg (add x y) = add (neg x) (neg y) := by
  induction n with
  | zero => exact CommRing2.neg_add x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem smul_zero {n : Nat} (c : K) : smul c (zero : ClSpace K n) = zero := by
  induction n with
  | zero => exact CommRing2.mul_zero c
  | succ n ih => exact Prod.ext ih ih

theorem zero_smul {n : Nat} (x : ClSpace K n) : smul (0 : K) x = zero := by
  induction n with
  | zero => exact CommRing2.zero_mul x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem one_smul {n : Nat} (x : ClSpace K n) : smul (1 : K) x = x := by
  induction n with
  | zero => exact CommRing2.one_mul x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_add {n : Nat} (c : K) (x y : ClSpace K n) :
    smul c (add x y) = add (smul c x) (smul c y) := by
  induction n with
  | zero => exact CommRing2.left_distrib c x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem add_smul {n : Nat} (a b : K) (x : ClSpace K n) :
    smul (a + b) x = add (smul a x) (smul b x) := by
  induction n with
  | zero => exact CommRing2.right_distrib a b x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_smul {n : Nat} (a b : K) (x : ClSpace K n) :
    smul a (smul b x) = smul (a * b) x := by
  induction n with
  | zero => exact (CommRing2.mul_assoc a b x).symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem neg_smul {n : Nat} (c : K) (x : ClSpace K n) : smul (-c) x = neg (smul c x) := by
  induction n with
  | zero => exact CommRing2.neg_mul c x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_neg {n : Nat} (c : K) (x : ClSpace K n) : smul c (neg x) = neg (smul c x) := by
  induction n with
  | zero => exact CommRing2.mul_neg c x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem half_smul_add_self {n : Nat} (x : ClSpace K n) :
    smul CommRing2.half (add x x) = x := by
  calc
    smul CommRing2.half (add x x)
      = smul CommRing2.half (add (smul 1 x) (smul 1 x)) := by rw [one_smul]
    _ = smul CommRing2.half (smul ((1 : K) + 1) x) := by rw [← add_smul]
    _ = smul (CommRing2.half * ((1 : K) + 1)) x := by rw [smul_smul]
    _ = smul 1 x := by rw [CommRing2.half_mul_two]
    _ = x := one_smul x

theorem scalar_zero {n : Nat} : scalar (0 : K) = (zero : ClSpace K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih rfl

theorem scalar_one {n : Nat} : scalar (1 : K) = (one : ClSpace K n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih rfl

theorem scalar_add {n : Nat} (a b : K) :
    scalar (n := n) (a + b) = add (scalar a) (scalar b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (zero_add zero).symm

theorem scalar_smul {n : Nat} (a b : K) :
    scalar (n := n) (a * b) = smul a (scalar b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (smul_zero a).symm

theorem scalarPart_scalar {n : Nat} (c : K) : scalarPart (scalar (n := n) c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem scalar_injective {n : Nat} {a b : K} (h : scalar (n := n) a = scalar b) : a = b := by
  have h1 := congrArg scalarPart h
  rw [scalarPart_scalar, scalarPart_scalar] at h1
  exact h1

theorem scalarPart_zero {n : Nat} : scalarPart (zero : ClSpace K n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem scalarPart_add {n : Nat} (x y : ClSpace K n) :
    scalarPart (add x y) = scalarPart x + scalarPart y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact ih x0 y0

theorem scalarPart_neg {n : Nat} (x : ClSpace K n) :
    scalarPart (neg x) = -(scalarPart x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact ih x0

theorem scalarPart_smul {n : Nat} (c : K) (x : ClSpace K n) :
    scalarPart (smul c x) = c * scalarPart x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact ih x0

theorem invol_zero {n : Nat} : invol (zero : ClSpace K n) = zero := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [invol, zero]; rw [ih, neg_zero])

theorem invol_one {n : Nat} : invol (one : ClSpace K n) = one := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [invol, one]; rw [invol_zero, neg_zero])

theorem invol_scalar {n : Nat} (c : K) : invol (scalar (n := n) c) = scalar c := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [invol, scalar]; rw [invol_zero, neg_zero])

theorem invol_add {n : Nat} (x y : ClSpace K n) :
    invol (add x y) = add (invol x) (invol y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (by dsimp [invol, add]; rw [ih x1 y1, neg_add])

theorem invol_neg {n : Nat} (x : ClSpace K n) : invol (neg x) = neg (invol x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [invol, neg]; rw [ih x1])

theorem invol_smul {n : Nat} (c : K) (x : ClSpace K n) :
    invol (smul c x) = smul c (invol x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [invol, smul]; rw [ih x1, smul_neg])

theorem invol_invol {n : Nat} (x : ClSpace K n) : invol (invol x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [invol]; rw [invol_neg, ih x1, neg_neg])

/-! ### Multiplicative Algebra Laws -/

theorem mul_zero {n : Nat} (q : Fin n → K) (x : ClSpace K n) : mul q x zero = zero := by
  induction n with
  | zero => exact CommRing2.mul_zero x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    apply Prod.ext <;> dsimp [mul, zero]
    · rw [ih, ih, smul_zero, add_zero]
    · rw [ih, ih, add_zero]

theorem zero_mul {n : Nat} (q : Fin n → K) (x : ClSpace K n) : mul q zero x = zero := by
  induction n with
  | zero => exact CommRing2.zero_mul x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    apply Prod.ext <;> dsimp [mul, zero]
    · rw [invol_zero, ih, ih, smul_zero, add_zero]
    · rw [invol_zero, ih, ih, add_zero]

theorem one_mul {n : Nat} (q : Fin n → K) (x : ClSpace K n) : mul q one x = x := by
  induction n with
  | zero => exact CommRing2.one_mul x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    apply Prod.ext <;> dsimp [mul, one]
    · rw [invol_zero, zero_mul, smul_zero, add_zero, ih]
    · rw [invol_one, zero_mul, ih, zero_add]

theorem mul_one {n : Nat} (q : Fin n → K) (x : ClSpace K n) : mul q x one = x := by
  induction n with
  | zero => exact CommRing2.mul_one x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    apply Prod.ext <;> dsimp [mul, one]
    · rw [ih, mul_zero, smul_zero, add_zero]
    · rw [ih, mul_zero, add_zero]

theorem left_distrib {n : Nat} (q : Fin n → K) (x y z : ClSpace K n) :
    mul q x (add y z) = add (mul q x y) (mul q x z) := by
  induction n with
  | zero => exact CommRing2.left_distrib x y z
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    apply Prod.ext <;> dsimp [mul, add]
    · rw [ih, ih, smul_add]
      simp only [add_assoc, add_left_comm, add_comm]
    · rw [ih, ih]
      simp only [add_assoc, add_left_comm, add_comm]

theorem right_distrib {n : Nat} (q : Fin n → K) (x y z : ClSpace K n) :
    mul q (add x y) z = add (mul q x z) (mul q y z) := by
  induction n with
  | zero => exact CommRing2.right_distrib x y z
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    apply Prod.ext <;> dsimp [mul, add]
    · rw [invol_add, ih, ih, smul_add]
      simp only [add_assoc, add_left_comm, add_comm]
    · rw [invol_add, ih, ih]
      simp only [add_assoc, add_left_comm, add_comm]

theorem smul_mul {n : Nat} (q : Fin n → K) (c : K) (x y : ClSpace K n) :
    mul q (smul c x) y = smul c (mul q x y) := by
  induction n with
  | zero => exact CommRing2.mul_assoc c x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, smul]
    · rw [invol_smul, ih, ih, smul_add, smul_smul, smul_smul, CommRing2.mul_comm c]
    · rw [invol_smul, ih, ih, smul_add]

theorem mul_smul {n : Nat} (q : Fin n → K) (c : K) (x y : ClSpace K n) :
    mul q x (smul c y) = smul c (mul q x y) := by
  induction n with
  | zero => exact CommRing2.mul_left_comm x c y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, smul]
    · rw [ih, ih, smul_add, smul_smul, smul_smul, CommRing2.mul_comm c]
    · rw [ih, ih, smul_add]

theorem neg_mul {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    mul q (neg x) y = neg (mul q x y) := by
  induction n with
  | zero => exact CommRing2.neg_mul x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, neg]
    · rw [invol_neg, ih, ih, smul_neg, neg_add]
    · rw [invol_neg, ih, ih, neg_add]

theorem mul_neg {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    mul q x (neg y) = neg (mul q x y) := by
  induction n with
  | zero => exact CommRing2.mul_neg x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, neg]
    · rw [ih, ih, smul_neg, neg_add]
    · rw [ih, ih, neg_add]

theorem scalar_mul {n : Nat} (q : Fin n → K) (c : K) (x : ClSpace K n) :
    mul q (scalar c) x = smul c x := by
  conv => lhs; rw [← CommRing2.mul_one c]
  rw [scalar_smul, smul_mul, scalar_one, one_mul]

theorem mul_scalar {n : Nat} (q : Fin n → K) (x : ClSpace K n) (c : K) :
    mul q x (scalar c) = smul c x := by
  conv => lhs; rw [← CommRing2.mul_one c]
  rw [scalar_smul, mul_smul, scalar_one, mul_one]

theorem invol_mul {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    invol (mul q x y) = mul q (invol x) (invol y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, invol]
    · rw [invol_add, invol_smul, ih, ih, invol_neg, invol_invol, neg_mul, mul_neg, neg_neg]
    · rw [invol_add, ih, ih, invol_invol, neg_mul, mul_neg, neg_add]

/-- Associativity of the Clifford product for all dimensions `n` and all `q`. -/
theorem mul_assoc {n : Nat} (q : Fin n → K) (x y z : ClSpace K n) :
    mul q (mul q x y) z = mul q x (mul q y z) := by
  induction n with
  | zero => exact CommRing2.mul_assoc x y z
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    apply Prod.ext <;> dsimp [mul]
    · rw [right_distrib, left_distrib, left_distrib, invol_add, right_distrib,
          smul_mul, mul_smul, smul_add, smul_add,
          invol_mul, invol_mul, invol_invol, ih, ih, ih, ih]
      simp only [add_assoc, add_left_comm, add_comm]
    · rw [right_distrib, invol_add, invol_smul, right_distrib, left_distrib, left_distrib,
          smul_mul, mul_smul,
          invol_mul, invol_mul, invol_invol, ih, ih, ih, ih]
      simp only [add_assoc, add_left_comm, add_comm]

/-! ### Reversion Laws -/

theorem rev_zero {n : Nat} : rev (zero : ClSpace K n) = zero := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [rev, zero]; rw [ih, invol_zero])

theorem rev_one {n : Nat} : rev (one : ClSpace K n) = one := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [rev, one]; rw [rev_zero, invol_zero])

theorem rev_scalar {n : Nat} (c : K) : rev (scalar (n := n) c) = scalar c := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by dsimp [rev, scalar]; rw [rev_zero, invol_zero])

theorem rev_add {n : Nat} (x y : ClSpace K n) : rev (add x y) = add (rev x) (rev y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (by dsimp [rev, add]; rw [ih x1 y1, invol_add])

theorem rev_neg {n : Nat} (x : ClSpace K n) : rev (neg x) = neg (rev x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [rev, neg]; rw [ih x1, invol_neg])

theorem rev_smul {n : Nat} (c : K) (x : ClSpace K n) : rev (smul c x) = smul c (rev x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [rev, smul]; rw [ih x1, invol_smul])

theorem rev_invol_comm {n : Nat} (x : ClSpace K n) : rev (invol x) = invol (rev x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [rev, invol]; rw [rev_neg, invol_neg, ih x1])

theorem rev_rev {n : Nat} (x : ClSpace K n) : rev (rev x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (by dsimp [rev]; rw [rev_invol_comm, ih x1, invol_invol])

/-- Reversion is an algebra anti-involution: `(X * Y)~ = Y~ * X~`. -/
theorem rev_mul {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    rev (mul q x y) = mul q (rev y) (rev x) := by
  induction n with
  | zero => exact CommRing2.mul_comm x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    apply Prod.ext <;> dsimp [mul, rev]
    · rw [rev_add, rev_smul, ih, ih, rev_invol_comm, invol_invol]
    · rw [rev_add, invol_add, ih, ih, invol_mul, invol_mul, rev_invol_comm, invol_invol, add_comm]

theorem scalarPart_rev {n : Nat} (x : ClSpace K n) : scalarPart (rev x) = scalarPart x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact ih x0

/-! ### Vectors, Quadratic Form, Polar Form, and Fundamental Clifford Relation -/

def vZero {n : Nat} : Fin n → K := fun _ => 0
def vAdd {n : Nat} (u v : Fin n → K) : Fin n → K := fun i => u i + v i
def vSmul {n : Nat} (c : K) (v : Fin n → K) : Fin n → K := fun i => c * v i

def stdBasis {n : Nat} (i : Fin n) : Fin n → K :=
  fun j => if j = i then 1 else 0

/-- Diagonal quadratic form `Q(v) = ∑ q_i v_i^2`. -/
def quadForm : {n : Nat} → (Fin n → K) → (Fin n → K) → K
  | 0, _, _ => 0
  | _ + 1, q, v =>
      finHead q * (finHead v * finHead v) + quadForm (finTail q) (finTail v)

/-- Symmetric polar bilinear form `B_Q(u, v) = ∑ q_i u_i v_i`. -/
def polarForm : {n : Nat} → (Fin n → K) → (Fin n → K) → (Fin n → K) → K
  | 0, _, _, _ => 0
  | _ + 1, q, u, v =>
      finHead q * (finHead u * finHead v) + polarForm (finTail q) (finTail u) (finTail v)

theorem polarForm_self {n : Nat} (q v : Fin n → K) : polarForm q v v = quadForm q v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [polarForm, quadForm]
    rw [ih]

theorem polarForm_symm {n : Nat} (q u v : Fin n → K) : polarForm q u v = polarForm q v u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [polarForm]
    rw [CommRing2.mul_comm (finHead u) (finHead v), ih]

/-- Polarization identity: `Q(u + v) - Q(u) - Q(v) = 2 B_Q(u, v)`. -/
theorem quadForm_polarization {n : Nat} (q u v : Fin n → K) :
    quadForm q (vAdd u v) - quadForm q u - quadForm q v = ((1 : K) + 1) * polarForm q u v := by
  apply CommRing2.add_right_cancel (c := quadForm q u + quadForm q v)
  have lhs_simp :
      quadForm q (vAdd u v) - quadForm q u - quadForm q v + (quadForm q u + quadForm q v)
      = quadForm q (vAdd u v) := by
    rw [CommRing2.sub_eq_add_neg, CommRing2.sub_eq_add_neg]
    calc
      quadForm q (vAdd u v) + -quadForm q u + -quadForm q v + (quadForm q u + quadForm q v)
        = quadForm q (vAdd u v) + ((-quadForm q u + quadForm q u) + (-quadForm q v + quadForm q v)) := by
            simp only [CommRing2.add_assoc, CommRing2.add_left_comm, CommRing2.add_comm]
      _ = quadForm q (vAdd u v) := by
            rw [CommRing2.neg_add_cancel, CommRing2.neg_add_cancel, CommRing2.add_zero, CommRing2.add_zero]
  rw [lhs_simp]
  clear lhs_simp
  induction n with
  | zero =>
    dsimp [quadForm, polarForm]
    rw [CommRing2.mul_zero, CommRing2.add_zero, CommRing2.add_zero]
  | succ n ih =>
    dsimp [quadForm, polarForm, finHead, finTail, vAdd]
    have sq_exp :
        q 0 * ((u 0 + v 0) * (u 0 + v 0))
        = ((1 : K) + 1) * (q 0 * (u 0 * v 0)) +
          q 0 * (u 0 * u 0) +
          q 0 * (v 0 * v 0) := by
      rw [CommRing2.left_distrib (u 0 + v 0), CommRing2.right_distrib, CommRing2.right_distrib,
          CommRing2.left_distrib (q 0), CommRing2.left_distrib (q 0), CommRing2.left_distrib (q 0),
          CommRing2.two_mul, CommRing2.mul_comm (v 0) (u 0)]
      simp only [CommRing2.add_assoc, CommRing2.add_left_comm, CommRing2.add_comm]
    have htail_add : finTail (vAdd u v) = vAdd (finTail u) (finTail v) := rfl
    rw [sq_exp, htail_add, ih (finTail q) (finTail u) (finTail v),
        CommRing2.left_distrib ((1 : K) + 1)]
    simp only [CommRing2.add_assoc, CommRing2.add_left_comm, CommRing2.add_comm]

/-- Canonical linear embedding of vectors `v ∈ K^n` into grade 1 of `ClSpace K n`. -/
def vec : {n : Nat} → (Fin n → K) → ClSpace K n
  | 0, _ => (0 : K)
  | _ + 1, v => (vec (finTail v), smul (finHead v) one)

def basisVec {n : Nat} (i : Fin n) : ClSpace K n :=
  vec (stdBasis i)

theorem vec_zero {n : Nat} : vec (vZero : Fin n → K) = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [vec, vZero, finHead, finTail]
    exact Prod.ext ih (zero_smul one)

theorem vec_add {n : Nat} (u v : Fin n → K) :
    vec (vAdd u v) = add (vec u) (vec v) := by
  induction n with
  | zero => exact (CommRing2.add_zero 0).symm
  | succ n ih =>
    dsimp [vec, vAdd, finHead, finTail, add]
    exact Prod.ext (ih _ _) (add_smul _ _ one)

theorem vec_smul {n : Nat} (c : K) (v : Fin n → K) :
    vec (vSmul c v) = smul c (vec v) := by
  induction n with
  | zero => exact (CommRing2.mul_zero c).symm
  | succ n ih =>
    dsimp [vec, vSmul, finHead, finTail, smul]
    exact Prod.ext (ih _) (smul_smul c _ one).symm

theorem invol_vec {n : Nat} (v : Fin n → K) : invol (vec v) = neg (vec v) := by
  induction n with
  | zero => exact CommRing2.neg_zero.symm
  | succ n ih =>
    dsimp [vec, invol, neg]
    exact Prod.ext (ih _) (by rw [invol_smul, invol_one])

theorem rev_vec {n : Nat} (v : Fin n → K) : rev (vec v) = vec v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [vec, rev]
    exact Prod.ext (ih _) (by rw [rev_smul, rev_one, invol_smul, invol_one])

/-- **Fundamental Clifford Relation:** `vec(v)^2 = Q(v) · 1` for all `v ∈ K^n`. -/
theorem vec_sq_eq_quad {n : Nat} (q v : Fin n → K) :
    mul q (vec v) (vec v) = scalar (quadForm q v) := by
  induction n with
  | zero => exact CommRing2.zero_mul 0
  | succ n ih =>
    dsimp [vec, mul, quadForm, scalar]
    apply Prod.ext
    · dsimp
      rw [ih, invol_smul, invol_one, smul_mul, mul_smul, one_mul,
          smul_smul, smul_smul, ← scalar_one, ← scalar_smul, ← scalar_add]
      congr 1
      rw [CommRing2.mul_one, CommRing2.mul_assoc, CommRing2.add_comm]
    · dsimp
      rw [invol_vec, neg_mul, smul_mul, one_mul, mul_smul, mul_one, add_neg_cancel]

/-- **Polarized Clifford Law:** `vec(u) vec(v) + vec(v) vec(u) = 2 B_Q(u, v) · 1`. -/
theorem vec_anticomm_eq_polar {n : Nat} (q u v : Fin n → K) :
    add (mul q (vec u) (vec v)) (mul q (vec v) (vec u)) =
      scalar (((1 : K) + 1) * polarForm q u v) := by
  have hsum : mul q (vec (vAdd u v)) (vec (vAdd u v)) = scalar (quadForm q (vAdd u v)) :=
    vec_sq_eq_quad q (vAdd u v)
  rw [vec_add, left_distrib, right_distrib, right_distrib, vec_sq_eq_quad, vec_sq_eq_quad] at hsum
  have hpol := quadForm_polarization q u v
  have hq : quadForm q (vAdd u v) =
      quadForm q u + quadForm q v + ((1 : K) + 1) * polarForm q u v := by
    calc
      quadForm q (vAdd u v)
        = quadForm q (vAdd u v) + ((-quadForm q u + quadForm q u) + (-quadForm q v + quadForm q v)) := by
            rw [CommRing2.neg_add_cancel, CommRing2.neg_add_cancel, CommRing2.add_zero, CommRing2.add_zero]
      _ = (quadForm q (vAdd u v) + -quadForm q u + -quadForm q v) + (quadForm q u + quadForm q v) := by
            simp only [CommRing2.add_assoc, CommRing2.add_left_comm, CommRing2.add_comm]
      _ = (quadForm q (vAdd u v) - quadForm q u - quadForm q v) + (quadForm q u + quadForm q v) := by
            rw [CommRing2.sub_eq_add_neg, CommRing2.sub_eq_add_neg]
      _ = ((1 : K) + 1) * polarForm q u v + (quadForm q u + quadForm q v) := by rw [hpol]
      _ = quadForm q u + quadForm q v + ((1 : K) + 1) * polarForm q u v := by
            simp only [CommRing2.add_assoc, CommRing2.add_left_comm, CommRing2.add_comm]
  rw [hq, scalar_add, scalar_add] at hsum
  apply add_left_cancel (x := add (scalar (quadForm q u)) (scalar (quadForm q v)))
  calc
    add (add (scalar (quadForm q u)) (scalar (quadForm q v)))
        (add (mul q (vec u) (vec v)) (mul q (vec v) (vec u)))
      = add (add (scalar (quadForm q u)) (mul q (vec v) (vec u)))
            (add (mul q (vec u) (vec v)) (scalar (quadForm q v))) := by
          simp only [add_assoc, add_left_comm, add_comm]
    _ = add (add (scalar (quadForm q u)) (scalar (quadForm q v)))
            (scalar (((1 : K) + 1) * polarForm q u v)) := hsum

/-! ### Universal Property of the Clifford Algebra -/

/-- Structure of an associative unital `K`-algebra `A`. -/
structure AssocAlgebra (K : Type u) [CommRing2 K] (A : Type v)
    extends Add A, Neg A, Mul A, Zero A, One A where
  algebraMap : K → A
  add_assoc : ∀ x y z : A, x + y + z = x + (y + z)
  add_comm : ∀ x y : A, x + y = y + x
  zero_add : ∀ x : A, 0 + x = x
  neg_add_cancel : ∀ x : A, -x + x = 0
  mul_assoc : ∀ x y z : A, x * y * z = x * (y * z)
  one_mul : ∀ x : A, 1 * x = x
  mul_one : ∀ x : A, x * 1 = x
  left_distrib : ∀ x y z : A, x * (y + z) = x * y + x * z
  right_distrib : ∀ x y z : A, (x + y) * z = x * z + y * z
  algebraMap_zero : algebraMap 0 = 0
  algebraMap_one : algebraMap 1 = 1
  algebraMap_add : ∀ a b : K, algebraMap (a + b) = algebraMap a + algebraMap b
  algebraMap_mul : ∀ a b : K, algebraMap (a * b) = algebraMap a * algebraMap b
  algebraMap_comm : ∀ (c : K) (x : A), algebraMap c * x = x * algebraMap c

/-- A `K`-algebra homomorphism from `ClSpace K n` (with quadratic form `q`) to `A`. -/
structure IsCliffordAlgHom {n : Nat} (q : Fin n → K) {A : Type v}
    (alg : AssocAlgebra K A) (Φ : ClSpace K n → A) : Prop where
  map_scalar : ∀ c : K, Φ (scalar c) = alg.algebraMap c
  map_add : ∀ x y : ClSpace K n, Φ (add x y) = alg.add (Φ x) (Φ y)
  map_mul : ∀ x y : ClSpace K n, Φ (mul q x y) = alg.mul (Φ x) (Φ y)

/-- Canonical extension `lift f : ClSpace K n → A` of a linear Clifford map `f : K^n → A`. -/
def lift {A : Type v} (alg : AssocAlgebra K A) :
    {n : Nat} → ((Fin n → K) → A) → ClSpace K n → A
  | 0, _, c => alg.algebraMap c
  | n + 1, f, (x0, x1) =>
      let fTail : (Fin n → K) → A := fun v' => f (fun i => Fin.cases (0 : K) v' i)
      let e0Vec : Fin (n + 1) → K := fun i => Fin.cases (1 : K) (fun _ => 0) i
      alg.add (lift alg fTail x0) (alg.mul (f e0Vec) (lift alg fTail x1))

/-- Decomposition `(x0, x1) = (x0, 0) + e_0 * (x1, 0)` used for uniqueness of `lift`. -/
theorem branch_decomp {n : Nat} (q : Fin (n + 1) → K) (x0 x1 : ClSpace K n) :
    ((x0, x1) : ClSpace K (n + 1)) =
      add (x0, zero) (mul q (vec (fun i => Fin.cases (1 : K) (fun _ => 0) i)) (x1, zero)) := by
  dsimp [vec, finHead, finTail, mul, add]
  have htail : (fun i : Fin n => (Fin.cases (1 : K) (fun _ => (0 : K)) i.succ : K)) = vZero := rfl
  change (x0, x1) =
    (add x0 (add (mul (finTail q) (vec (fun i => Fin.cases (1 : K) (fun _ => (0 : K)) i.succ)) x1)
                 (smul (q 0) (mul (finTail q) (invol (smul 1 one)) zero))),
     add zero (add (mul (finTail q) (smul 1 one) x1)
                   (mul (finTail q) (invol (vec (fun i => Fin.cases (1 : K) (fun _ => (0 : K)) i.succ))) zero)))
  rw [htail, vec_zero, one_smul, invol_zero, zero_mul, mul_zero, smul_zero, add_zero,
      one_mul, zero_mul, add_zero, add_zero, zero_add]

/-- **Uniqueness part of the Universal Property:** Any `K`-algebra homomorphism `Φ` from
    `ClSpace K n` to `A` is uniquely determined by its restriction `Φ ∘ vec` to `K^n`
    (specifically `Φ = lift alg (Φ ∘ vec)`). -/
theorem lift_unique {n : Nat} (q : Fin n → K) {A : Type v} (alg : AssocAlgebra K A)
    (Φ : ClSpace K n → A) (hΦ : IsCliffordAlgHom q alg Φ) :
    ∀ x : ClSpace K n, Φ x = lift alg (fun v => Φ (vec v)) x := by
  induction n with
  | zero =>
    intro c
    exact hΦ.map_scalar c
  | succ n ih =>
    intro ⟨x0, x1⟩
    let q' := finTail q
    let emb : ClSpace K n → ClSpace K (n + 1) := fun z => (z, zero)
    let Φ' : ClSpace K n → A := fun z => Φ (emb z)
    have hΦ' : IsCliffordAlgHom q' alg Φ' := by
      refine ⟨?_, ?_, ?_⟩
      · intro c
        exact hΦ.map_scalar c
      · intro a b
        have hemb : emb (add a b) = add (emb a) (emb b) := Prod.ext rfl (add_zero zero).symm
        dsimp [Φ']
        rw [hemb, hΦ.map_add]
      · intro a b
        have hemb : emb (mul q' a b) = mul q (emb a) (emb b) := by
          dsimp [emb, mul]
          rw [invol_zero, zero_mul, smul_zero, add_zero, zero_mul, mul_zero, add_zero]
        dsimp [Φ']
        rw [hemb, hΦ.map_mul]
    have hvec_tail : (fun v' : Fin n → K => Φ (vec (fun i => Fin.cases (0 : K) v' i))) =
                     (fun v' : Fin n → K => Φ' (vec v')) := by
      funext v'
      dsimp [Φ', emb, vec, finHead, finTail]
      have h0 : smul (0 : K) (one : ClSpace K n) = zero := zero_smul one
      change Φ (vec (fun i => Fin.cases (0 : K) v' i.succ), smul 0 one) = Φ (vec v', zero)
      have ht : (fun i : Fin n => (Fin.cases (0 : K) v' i.succ : K)) = v' := rfl
      rw [h0, ht]
    conv => lhs; rw [branch_decomp q x0 x1]
    rw [hΦ.map_add, hΦ.map_mul]
    dsimp [lift]
    rw [hvec_tail, ← ih q' Φ' hΦ' x0, ← ih q' Φ' hΦ' x1]

end ClSpace
end CliffordSpace
end CliffordDecomp
