/-
  Conjecture 00000007617 — Constructive 2^n-Dimensional Grassmann Exterior
  and Degenerate/Euclidean Clifford Algebras
  Core Lean 4.19.0 only (zero external dependencies).

  Constructs `Cl R n` recursively over any commutative ring `CRing R`:
    Cl R 0       = R
    Cl R (n + 1) = Cl R n × Cl R n   (representing `a + b ∧ e_n`)
  Setting `q = 0` (`zeroMetric`) gives the Grassmann exterior algebra `Λ(R^n)`
  with wedge product `wedge n x y`; setting `q = (0, 1, ..., 1)` (`pgaMetric`)
  gives the Euclidean Projective Geometric Algebra `Cl_{n-1, 0, 1}`.
-/

import Conjecture00000007617.Ring

namespace Conjecture00000007617

/-- Underlying `2^n`-dimensional module of the Grassmann exterior and Clifford algebras over `R`. -/
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

section ModuleAndAlgebra
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

/-- Alternating sign `(-1)^m • x` defined directly by iterated negation. -/
def signCl (n : Nat) : Nat → Cl R n → Cl R n
  | 0, x => x
  | m + 1, x => neg n (signCl n m x)

/-- Grade involution `x̂` (`(-1)^k` on grade `k`). -/
def invol : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, x => (invol n x.1, neg n (invol n x.2))

/-- Clifford/Grassmann reversion `x̃` (`(-1)^{k(k-1)/2}` on grade `k`). -/
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

/-- Zero metric `q ≡ 0`, realizing the Grassmann exterior algebra `Λ(R^n)`. -/
def zeroMetric (n : Nat) : Fin n → R :=
  fun _ => CRing.zero

/-- Standard Euclidean metric `q ≡ 1`. -/
def euclidMetric (n : Nat) : Fin n → R :=
  fun _ => CRing.one

/-- Degenerate Euclidean PGA metric `q = (0, 1, ..., 1)` on `R^{m+1}` (`e_0^2 = 0`, `e_i^2 = 1`). -/
def pgaMetric (n : Nat) : Fin n → R :=
  fun i => if i.val == 0 then CRing.zero else CRing.one

/-- Exterior wedge (progressive) product `x ∧ y` on `Λ(R^n)`. -/
def wedge (n : Nat) (x y : Cl R n) : Cl R n :=
  mul (zeroMetric (R := R) n) x y

/-- Induced determinant bilinear form `⟨x, y⟩_q` on `Λ(R^n)`. -/
def inner : {n : Nat} → (Fin n → R) → Cl R n → Cl R n → R
  | 0, _, a, c => CRing.mul a c
  | _ + 1, q, x, y =>
      CRing.add (inner (initMetric q) x.1 y.1)
        (CRing.mul (lastMetric q) (inner (initMetric q) x.2 y.2))

/-- Standard basis vector `e_i ∈ Λ^1(R^n)`. -/
def basisVec : (n : Nat) → Fin n → Cl R n
  | 0, i => Fin.elim0 i
  | n + 1, ⟨k, _⟩ =>
      if h : k < n then
        (basisVec n ⟨k, h⟩, zero n)
      else
        (zero n, one n)

/-- Basis blade `e_I ∈ Λ^{|I|}(R^n)` for a subset mask `I : Fin n → Bool`. -/
def basisBlade : (n : Nat) → (Fin n → Bool) → Cl R n
  | 0, _ => CRing.one
  | n + 1, I =>
      let I' : Fin n → Bool := fun i => I ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      if I ⟨n, Nat.lt_succ_self n⟩ then
        (zero n, basisBlade n I')
      else
        (basisBlade n I', zero n)

/-- Scalar (grade-0) coordinate extraction. -/
def scalarPart : (n : Nat) → Cl R n → R
  | 0, a => a
  | n + 1, x => scalarPart n x.1

/-- Volume bracket `[x]_{ω_n}` extracting the `ω_n = e_0 ∧ ... ∧ e_{n-1}` coefficient. -/
def topCoeff : (n : Nat) → Cl R n → R
  | 0, a => a
  | n + 1, x => topCoeff n x.2

/-! ### Module Identities -/

theorem add_assoc (n : Nat) (x y z : Cl R n) :
    add n (add n x y) z = add n x (add n y z) := by
  induction n with
  | zero => exact CRing.add_assoc x y z
  | succ n ih => exact Prod.ext (ih x.1 y.1 z.1) (ih x.2 y.2 z.2)

theorem add_comm (n : Nat) (x y : Cl R n) :
    add n x y = add n y x := by
  induction n with
  | zero => exact CRing.add_comm x y
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem zero_add (n : Nat) (x : Cl R n) :
    add n (zero n) x = x := by
  induction n with
  | zero => exact CRing.zero_add x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem add_zero (n : Nat) (x : Cl R n) :
    add n x (zero n) = x := by
  rw [add_comm, zero_add]

theorem add_left_neg (n : Nat) (x : Cl R n) :
    add n (neg n x) x = zero n := by
  induction n with
  | zero => exact CRing.add_left_neg x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem add_right_neg (n : Nat) (x : Cl R n) :
    add n x (neg n x) = zero n := by
  rw [add_comm, add_left_neg]

theorem neg_zero (n : Nat) :
    neg n (zero (R := R) n) = zero n := by
  induction n with
  | zero => exact CRing.neg_zero
  | succ n ih => exact Prod.ext ih ih

theorem neg_neg (n : Nat) (x : Cl R n) :
    neg n (neg n x) = x := by
  induction n with
  | zero => exact CRing.neg_neg x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem neg_add (n : Nat) (x y : Cl R n) :
    neg n (add n x y) = add n (neg n x) (neg n y) := by
  induction n with
  | zero => exact CRing.neg_add x y
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem add_add_add_comm (n : Nat) (a b c d : Cl R n) :
    add n (add n a b) (add n c d) = add n (add n a c) (add n b d) := by
  induction n with
  | zero => exact CRing.add_add_add_comm a b c d
  | succ n ih => exact Prod.ext (ih a.1 b.1 c.1 d.1) (ih a.2 b.2 c.2 d.2)

theorem smul_zero (n : Nat) (r : R) :
    smul n r (zero n) = zero n := by
  induction n with
  | zero => exact CRing.mul_zero r
  | succ n ih => exact Prod.ext ih ih

theorem zero_smul (n : Nat) (x : Cl R n) :
    smul n CRing.zero x = zero n := by
  induction n with
  | zero => exact CRing.zero_mul x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem one_smul (n : Nat) (x : Cl R n) :
    smul n CRing.one x = x := by
  induction n with
  | zero => exact CRing.one_mul x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem smul_add (n : Nat) (r : R) (x y : Cl R n) :
    smul n r (add n x y) = add n (smul n r x) (smul n r y) := by
  induction n with
  | zero => exact CRing.left_distrib r x y
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem add_smul (n : Nat) (r s : R) (x : Cl R n) :
    smul n (CRing.add r s) x = add n (smul n r x) (smul n s x) := by
  induction n with
  | zero => exact CRing.right_distrib r s x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem smul_smul (n : Nat) (r s : R) (x : Cl R n) :
    smul n r (smul n s x) = smul n (CRing.mul r s) x := by
  induction n with
  | zero => exact Eq.symm (CRing.mul_assoc r s x)
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem smul_neg (n : Nat) (r : R) (x : Cl R n) :
    smul n r (neg n x) = neg n (smul n r x) := by
  induction n with
  | zero => exact CRing.mul_neg r x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem neg_smul (n : Nat) (r : R) (x : Cl R n) :
    smul n (CRing.neg r) x = neg n (smul n r x) := by
  induction n with
  | zero => exact CRing.neg_mul r x
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

/-! ### `signCl` Lemmas -/

theorem signCl_zero_elem (n m : Nat) :
    signCl n m (zero (R := R) n) = zero n := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, ih, neg_zero]

theorem signCl_add (n m : Nat) (x y : Cl R n) :
    signCl n m (add n x y) = add n (signCl n m x) (signCl n m y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, ih, neg_add]

theorem signCl_neg (n m : Nat) (x : Cl R n) :
    signCl n m (neg n x) = neg n (signCl n m x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, ih]

theorem signCl_add_exp (n m k : Nat) (x : Cl R n) :
    signCl n (m + k) x = signCl n m (signCl n k x) := by
  induction m with
  | zero => simp [signCl]
  | succ m ih =>
      have h : m + 1 + k = (m + k) + 1 := Nat.succ_add m k
      rw [h]
      simp [signCl, ih]

theorem signCl_even (n m : Nat) (x : Cl R n) :
    signCl n (2 * m) x = x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have h : 2 * (m + 1) = (2 * m) + 2 := by omega
      rw [h]
      simp [signCl, neg_neg, ih]

theorem signCl_self_cancel (n m : Nat) (x : Cl R n) :
    signCl n m (signCl n m x) = x := by
  rw [← signCl_add_exp]
  have h : m + m = 2 * m := by omega
  rw [h]
  exact signCl_even n m x

theorem signCl_pair (n m : Nat) (a b : Cl R n) :
    signCl (n + 1) m (a, b) = (signCl n m a, signCl n m b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [signCl, ih]
      rfl

/-! ### Involution, Reversion, and Associative Algebra Laws -/

theorem invol_zero (n : Nat) : invol n (zero (R := R) n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by simp [invol, zero, ih, neg_zero])

theorem invol_one (n : Nat) : invol n (one (R := R) n) = one n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by simp [invol, one, invol_zero, neg_zero])

theorem invol_add (n : Nat) (x y : Cl R n) :
    invol n (add n x y) = add n (invol n x) (invol n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1 y.1) (by simp [invol, add, ih, neg_add])

theorem invol_neg (n : Nat) (x : Cl R n) :
    invol n (neg n x) = neg n (invol n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [invol, neg, ih])

theorem invol_smul (n : Nat) (r : R) (x : Cl R n) :
    invol n (smul n r x) = smul n r (invol n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [invol, smul, ih, smul_neg])

theorem invol_invol (n : Nat) (x : Cl R n) :
    invol n (invol n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [invol, invol_neg, ih, neg_neg])

theorem invol_signCl (n m : Nat) (x : Cl R n) :
    invol n (signCl n m x) = signCl n m (invol n x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, invol_neg, ih]

theorem rev_zero (n : Nat) : rev n (zero (R := R) n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext ih (by simp [rev, zero, ih, invol_zero])

theorem rev_add (n : Nat) (x y : Cl R n) :
    rev n (add n x y) = add n (rev n x) (rev n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih x.1 y.1) (by simp [rev, add, ih, invol_add])

theorem rev_neg (n : Nat) (x : Cl R n) :
    rev n (neg n x) = neg n (rev n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih x.1) (by simp [rev, neg, ih, invol_neg])

theorem rev_invol_comm (n : Nat) (x : Cl R n) :
    rev n (invol n x) = invol n (rev n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [rev, invol, rev_neg, ih, invol_neg])

theorem rev_rev (n : Nat) (x : Cl R n) :
    rev n (rev n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [rev, rev_invol_comm, ih, invol_invol])

theorem mul_zero {n : Nat} (q : Fin n → R) (x : Cl R n) :
    mul q x (zero n) = zero n := by
  induction n with
  | zero => exact CRing.mul_zero x
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, zero, invol_zero, ih, smul_zero, add_zero])
        (by simp [mul, zero, invol_zero, ih, add_zero])

theorem zero_mul {n : Nat} (q : Fin n → R) (x : Cl R n) :
    mul q (zero n) x = zero n := by
  induction n with
  | zero => exact CRing.zero_mul x
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, zero, ih, smul_zero, add_zero])
        (by simp [mul, zero, ih, add_zero])

theorem one_mul {n : Nat} (q : Fin n → R) (x : Cl R n) :
    mul q (one n) x = x := by
  induction n with
  | zero => exact CRing.one_mul x
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, one, ih, zero_mul, smul_zero, add_zero])
        (by simp [mul, one, ih, zero_mul, add_zero])

theorem mul_one {n : Nat} (q : Fin n → R) (x : Cl R n) :
    mul q x (one n) = x := by
  induction n with
  | zero => exact CRing.mul_one x
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, one, ih, invol_zero, mul_zero, smul_zero, add_zero])
        (by simp [mul, one, ih, invol_one, mul_zero, zero_add])

theorem left_distrib {n : Nat} (q : Fin n → R) (x y z : Cl R n) :
    mul q x (add n y z) = add n (mul q x y) (mul q x z) := by
  induction n with
  | zero => exact CRing.left_distrib x y z
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change add n (mul q' x.1 (add n y.1 z.1))
            (smul n qn (mul q' x.2 (invol n (add n y.2 z.2)))) =
          add n (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2))))
            (add n (mul q' x.1 z.1) (smul n qn (mul q' x.2 (invol n z.2))))
        rw [invol_add, ih, ih, smul_add, add_add_add_comm]
      · change add n (mul q' x.1 (add n y.2 z.2))
            (mul q' x.2 (invol n (add n y.1 z.1))) =
          add n (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)))
            (add n (mul q' x.1 z.2) (mul q' x.2 (invol n z.1)))
        rw [invol_add, ih, ih, add_add_add_comm]

theorem right_distrib {n : Nat} (q : Fin n → R) (x y z : Cl R n) :
    mul q (add n x y) z = add n (mul q x z) (mul q y z) := by
  induction n with
  | zero => exact CRing.right_distrib x y z
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change add n (mul q' (add n x.1 y.1) z.1)
            (smul n qn (mul q' (add n x.2 y.2) (invol n z.2))) =
          add n (add n (mul q' x.1 z.1) (smul n qn (mul q' x.2 (invol n z.2))))
            (add n (mul q' y.1 z.1) (smul n qn (mul q' y.2 (invol n z.2))))
        rw [ih, ih, smul_add, add_add_add_comm]
      · change add n (mul q' (add n x.1 y.1) z.2)
            (mul q' (add n x.2 y.2) (invol n z.1)) =
          add n (add n (mul q' x.1 z.2) (mul q' x.2 (invol n z.1)))
            (add n (mul q' y.1 z.2) (mul q' y.2 (invol n z.1)))
        rw [ih, ih, add_add_add_comm]

theorem mul_neg {n : Nat} (q : Fin n → R) (x y : Cl R n) :
    mul q x (neg n y) = neg n (mul q x y) := by
  induction n with
  | zero => exact CRing.mul_neg x y
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, neg, invol_neg, ih, smul_neg, neg_add])
        (by simp [mul, neg, invol_neg, ih, neg_add])

theorem neg_mul {n : Nat} (q : Fin n → R) (x y : Cl R n) :
    mul q (neg n x) y = neg n (mul q x y) := by
  induction n with
  | zero => exact CRing.neg_mul x y
  | succ n ih =>
      exact Prod.ext
        (by simp [mul, neg, ih, smul_neg, neg_add])
        (by simp [mul, neg, ih, neg_add])

theorem smul_mul {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n) :
    mul q (smul n r x) y = smul n r (mul q x y) := by
  induction n with
  | zero => exact CRing.mul_assoc r x y
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change add n (mul q' (smul n r x.1) y.1)
            (smul n qn (mul q' (smul n r x.2) (invol n y.2))) =
          smul n r (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2))))
        rw [ih, ih, smul_add, smul_smul, smul_smul, CRing.mul_comm qn r]
      · change add n (mul q' (smul n r x.1) y.2) (mul q' (smul n r x.2) (invol n y.1)) =
          smul n r (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)))
        rw [ih, ih, smul_add]

theorem mul_smul {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n) :
    mul q x (smul n r y) = smul n r (mul q x y) := by
  induction n with
  | zero =>
      calc
        CRing.mul x (CRing.mul r y) = CRing.mul (CRing.mul x r) y := Eq.symm (CRing.mul_assoc x r y)
        _ = CRing.mul (CRing.mul r x) y := by rw [CRing.mul_comm x r]
        _ = CRing.mul r (CRing.mul x y) := CRing.mul_assoc r x y
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change add n (mul q' x.1 (smul n r y.1))
            (smul n qn (mul q' x.2 (invol n (smul n r y.2)))) =
          smul n r (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2))))
        rw [invol_smul, ih, ih, smul_add, smul_smul, smul_smul, CRing.mul_comm qn r]
      · change add n (mul q' x.1 (smul n r y.2)) (mul q' x.2 (invol n (smul n r y.1))) =
          smul n r (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)))
        rw [invol_smul, ih, ih, smul_add]

theorem signCl_mul {n : Nat} (q : Fin n → R) (m : Nat) (x y : Cl R n) :
    mul q (signCl n m x) y = signCl n m (mul q x y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, neg_mul, ih]

theorem mul_signCl {n : Nat} (q : Fin n → R) (m : Nat) (x y : Cl R n) :
    mul q x (signCl n m y) = signCl n m (mul q x y) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, mul_neg, ih]

theorem invol_mul {n : Nat} (q : Fin n → R) (x y : Cl R n) :
    invol n (mul q x y) = mul q (invol n x) (invol n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change invol n (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2)))) =
          add n (mul q' (invol n x.1) (invol n y.1))
            (smul n qn (mul q' (neg n (invol n x.2)) (invol n (neg n (invol n y.2)))))
        rw [invol_add, invol_smul, ih, ih, invol_neg, neg_mul, mul_neg, neg_neg]
      · change neg n (invol n (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1)))) =
          add n (mul q' (invol n x.1) (neg n (invol n y.2)))
            (mul q' (neg n (invol n x.2)) (invol n (invol n y.1)))
        rw [invol_add, neg_add, ih, ih, mul_neg, neg_mul]

theorem mul_assoc {n : Nat} (q : Fin n → R) (x y z : Cl R n) :
    mul q (mul q x y) z = mul q x (mul q y z) := by
  induction n with
  | zero => exact CRing.mul_assoc x y z
  | succ n ih =>
      let q' := initMetric q
      let qn := lastMetric q
      refine Prod.ext ?_ ?_
      · change add n (mul q' (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2)))) z.1)
            (smul n qn (mul q' (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1))) (invol n z.2))) =
          add n (mul q' x.1 (add n (mul q' y.1 z.1) (smul n qn (mul q' y.2 (invol n z.2)))))
            (smul n qn (mul q' x.2 (invol n (add n (mul q' y.1 z.2) (mul q' y.2 (invol n z.1))))))
        rw [right_distrib, right_distrib, left_distrib, invol_add, left_distrib,
            smul_add, smul_add, smul_mul, mul_smul,
            invol_mul, invol_mul, invol_invol,
            ih, ih, ih, ih, add_add_add_comm]
        congr 1
        exact add_comm n _ _
      · change add n (mul q' (add n (mul q' x.1 y.1) (smul n qn (mul q' x.2 (invol n y.2)))) z.2)
            (mul q' (add n (mul q' x.1 y.2) (mul q' x.2 (invol n y.1))) (invol n z.1)) =
          add n (mul q' x.1 (add n (mul q' y.1 z.2) (mul q' y.2 (invol n z.1))))
            (mul q' x.2 (invol n (add n (mul q' y.1 z.1) (smul n qn (mul q' y.2 (invol n z.2))))))
        rw [right_distrib, right_distrib, left_distrib, invol_add, invol_smul, left_distrib,
            smul_mul, mul_smul,
            invol_mul, invol_mul, invol_invol,
            ih, ih, ih, ih, add_add_add_comm]
        congr 1
        exact add_comm n _ _

theorem wedge_eq (n : Nat) (x y : Cl R (n + 1)) :
    wedge (n + 1) x y =
      (wedge n x.1 y.1, add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))) := by
  unfold wedge
  have hz : initMetric (zeroMetric (R := R) (n + 1)) = zeroMetric (R := R) n := rfl
  have hl : lastMetric (zeroMetric (R := R) (n + 1)) = CRing.zero := rfl
  simp only [mul, hz, hl, zero_smul, add_zero]

/-! ### Grading of `Λ(R^n)` and Exterior Anticommutativity -/

def HasGrade : (n : Nat) → Nat → Cl R n → Prop
  | 0, 0, _ => True
  | 0, _ + 1, a => a = CRing.zero
  | n + 1, 0, x => HasGrade n 0 x.1 ∧ x.2 = zero n
  | n + 1, k + 1, x => HasGrade n (k + 1) x.1 ∧ HasGrade n k x.2

theorem hasGrade_zero (n k : Nat) : HasGrade n k (zero (R := R) n) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => trivial
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => exact ⟨ih 0, rfl⟩
      | succ k => exact ⟨ih (k + 1), ih k⟩

theorem hasGrade_gt_eq_zero {n k : Nat} {x : Cl R n} (hgt : n < k) (hg : HasGrade n k x) :
    x = zero n := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => exact hg
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hgt1 : n < k + 1 := by omega
          have hgt2 : n < k := by omega
          exact Prod.ext (ih hgt1 hg.1) (ih hgt2 hg.2)

theorem hasGrade_add {n k : Nat} {x y : Cl R n}
    (hx : HasGrade n k x) (hy : HasGrade n k y) : HasGrade n k (add n x y) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => trivial
      | succ k =>
          change CRing.add x y = CRing.zero
          rw [hx, hy, CRing.add_zero]
  | succ n ih =>
      cases k with
      | zero =>
          refine ⟨ih hx.1 hy.1, ?_⟩
          change add n x.2 y.2 = zero n
          rw [hx.2, hy.2, add_zero]
      | succ k => exact ⟨ih hx.1 hy.1, ih hx.2 hy.2⟩

theorem hasGrade_neg {n k : Nat} {x : Cl R n}
    (hx : HasGrade n k x) : HasGrade n k (neg n x) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => trivial
      | succ k =>
          change CRing.neg x = CRing.zero
          rw [hx, CRing.neg_zero]
  | succ n ih =>
      cases k with
      | zero =>
          refine ⟨ih hx.1, ?_⟩
          change neg n x.2 = zero n
          rw [hx.2, neg_zero]
      | succ k => exact ⟨ih hx.1, ih hx.2⟩

theorem hasGrade_signCl {n k : Nat} (m : Nat) {x : Cl R n}
    (hx : HasGrade n k x) : HasGrade n k (signCl n m x) := by
  induction m with
  | zero => exact hx
  | succ m ih => exact hasGrade_neg ih

theorem hasGrade_smul {n k : Nat} (r : R) {x : Cl R n}
    (hx : HasGrade n k x) : HasGrade n k (smul n r x) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => trivial
      | succ k =>
          change CRing.mul r x = CRing.zero
          rw [hx, CRing.mul_zero]
  | succ n ih =>
      cases k with
      | zero =>
          refine ⟨ih hx.1, ?_⟩
          change smul n r x.2 = zero n
          rw [hx.2, smul_zero]
      | succ k => exact ⟨ih hx.1, ih hx.2⟩

theorem hasGrade_zero_eq_smul_one {n : Nat} {x : Cl R n} (hx : HasGrade n 0 x) :
    x = smul n (scalarPart n x) (one n) := by
  induction n with
  | zero =>
      change x = CRing.mul x CRing.one
      exact Eq.symm (CRing.mul_one x)
  | succ n ih =>
      refine Prod.ext (ih hx.1) ?_
      rw [hx.2]
      exact Eq.symm (smul_zero n (scalarPart n x.1))

theorem invol_on_grade {n k : Nat} {x : Cl R n} (hx : HasGrade n k x) :
    invol n x = signCl n k x := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k =>
          rw [hx]
          exact Eq.symm (signCl_zero_elem 0 (k + 1))
  | succ n ih =>
      rw [signCl_pair]
      cases k with
      | zero =>
          refine Prod.ext (ih hx.1) ?_
          change neg n (invol n x.2) = x.2
          rw [hx.2, invol_zero, neg_zero]
      | succ k =>
          refine Prod.ext (ih hx.1) ?_
          change neg n (invol n x.2) = neg n (signCl n k x.2)
          rw [ih hx.2]

theorem wedge_hasGrade {n r s : Nat} {x y : Cl R n}
    (hx : HasGrade n r x) (hy : HasGrade n s y) :
    HasGrade n (r + s) (wedge n x y) := by
  induction n generalizing r s with
  | zero =>
      cases r with
      | zero =>
          cases s with
          | zero => trivial
          | succ s =>
              change CRing.mul x y = CRing.zero
              rw [hy, CRing.mul_zero]
      | succ r =>
          cases hrs : (r + 1) + s with
          | zero => omega
          | succ m =>
              change CRing.mul x y = CRing.zero
              rw [hx, CRing.zero_mul]
  | succ n ih =>
      rw [wedge_eq]
      cases r with
      | zero =>
          cases s with
          | zero =>
              refine ⟨ih hx.1 hy.1, ?_⟩
              change add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1)) = zero n
              rw [hx.2, hy.2]
              unfold wedge
              rw [mul_zero, zero_mul, add_zero]
          | succ s =>
              have h0s : 0 + (s + 1) = s + 1 := Nat.zero_add (s + 1)
              have hfst : HasGrade n (s + 1) (wedge n x.1 y.1) := by
                rw [← h0s]; exact ih hx.1 hy.1
              have hsnd : HasGrade n s (add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))) := by
                rw [hx.2]
                unfold wedge
                rw [zero_mul, add_zero]
                have h0s' : 0 + s = s := Nat.zero_add s
                rw [← h0s']
                exact ih hx.1 hy.2
              rw [h0s]
              exact ⟨hfst, hsnd⟩
      | succ r =>
          cases s with
          | zero =>
              have hr0 : (r + 1) + 0 = r + 1 := Nat.add_zero (r + 1)
              have hfst : HasGrade n (r + 1) (wedge n x.1 y.1) := by
                rw [← hr0]; exact ih hx.1 hy.1
              have hsnd : HasGrade n r (add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))) := by
                rw [hy.2]
                unfold wedge
                rw [mul_zero, zero_add]
                have hinv : HasGrade n 0 (invol n y.1) := by
                  rw [invol_on_grade hy.1]
                  exact hy.1
                have hr0' : r + 0 = r := Nat.add_zero r
                rw [← hr0']
                exact ih hx.2 hinv
              rw [hr0]
              exact ⟨hfst, hsnd⟩
          | succ s =>
              have hrs : (r + 1) + (s + 1) = ((r + 1) + s) + 1 := rfl
              have hfst : HasGrade n ((r + 1) + (s + 1)) (wedge n x.1 y.1) := ih hx.1 hy.1
              have hsnd : HasGrade n ((r + 1) + s) (add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))) := by
                apply hasGrade_add
                · exact ih hx.1 hy.2
                · have hinv : HasGrade n (s + 1) (invol n y.1) := by
                    rw [invol_on_grade hy.1]
                    exact hasGrade_signCl (s + 1) hy.1
                  have heq : r + (s + 1) = (r + 1) + s := by omega
                  have h2 : HasGrade n (r + (s + 1)) (wedge n x.2 (invol n y.1)) := ih hx.2 hinv
                  rw [heq] at h2
                  exact h2
              rw [hrs] at hfst ⊢
              exact ⟨hfst, hsnd⟩

theorem wedge_grade_comm {n r s : Nat} {x y : Cl R n}
    (hx : HasGrade n r x) (hy : HasGrade n s y) :
    wedge n y x = signCl n (r * s) (wedge n x y) := by
  induction n generalizing r s with
  | zero =>
      cases r with
      | zero =>
          simp only [Nat.zero_mul, signCl]
          exact CRing.mul_comm y x
      | succ r =>
          change CRing.mul y x = signCl 0 ((r + 1) * s) (CRing.mul x y)
          rw [hx, CRing.mul_zero, CRing.zero_mul]
          exact Eq.symm (signCl_zero_elem 0 ((r + 1) * s))
  | succ n ih =>
      rw [wedge_eq, wedge_eq, signCl_pair]
      cases r with
      | zero =>
          cases s with
          | zero =>
              refine Prod.ext (ih hx.1 hy.1) ?_
              simp only [Nat.zero_mul, signCl]
              change add n (wedge n y.1 x.2) (wedge n y.2 (invol n x.1)) =
                add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))
              rw [hx.2, hy.2]
              unfold wedge
              rw [mul_zero, mul_zero, zero_mul, zero_mul, add_zero]
          | succ s =>
              refine Prod.ext (ih hx.1 hy.1) ?_
              simp only [Nat.zero_mul, signCl]
              change add n (wedge n y.1 x.2) (wedge n y.2 (invol n x.1)) =
                add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))
              rw [hx.2, invol_on_grade hx.1]
              simp only [signCl]
              unfold wedge at *
              rw [mul_zero, zero_mul, add_zero, zero_add]
              have hcomm := ih hx.1 hy.2
              simp only [Nat.zero_mul, signCl] at hcomm
              exact hcomm
      | succ r =>
          cases s with
          | zero =>
              refine Prod.ext (ih hx.1 hy.1) ?_
              simp only [Nat.mul_zero, signCl]
              change add n (wedge n y.1 x.2) (wedge n y.2 (invol n x.1)) =
                add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1))
              rw [hy.2, invol_on_grade hy.1]
              simp only [signCl]
              unfold wedge at *
              rw [zero_mul, mul_zero, zero_add, add_zero]
              have hcomm := ih hx.2 hy.1
              simp only [Nat.mul_zero, signCl] at hcomm
              exact hcomm
          | succ s =>
              refine Prod.ext (ih hx.1 hy.1) ?_
              change add n (wedge n y.1 x.2) (wedge n y.2 (invol n x.1)) =
                signCl n ((r + 1) * (s + 1)) (add n (wedge n x.1 y.2) (wedge n x.2 (invol n y.1)))
              rw [invol_on_grade hx.1, invol_on_grade hy.1]
              unfold wedge at *
              rw [mul_signCl, mul_signCl]
              have t1 := ih hx.1 hy.2
              have t2 := ih hx.2 hy.1
              rw [t2, t1, ← signCl_add_exp, signCl_add, ← signCl_add_exp]
              have e1 : (r + 1) + (r + 1) * s = (r + 1) * (s + 1) := by
                rw [Nat.mul_succ (r + 1) s, Nat.add_comm]
              have e2 : ((r + 1) * (s + 1)) + (s + 1) = 2 * (s + 1) + r * (s + 1) := by
                rw [Nat.succ_mul r (s + 1), Nat.two_mul]
                omega
              rw [e1, e2, signCl_add_exp, signCl_even, add_comm]

/-- Universal alternating identity `v ∧ v = 0` for all 1-vectors over EVERY commutative ring `R`. -/
theorem wedge_vec_self_eq_zero {n : Nat} {v : Cl R n} (hv : HasGrade n 1 v) :
    wedge n v v = zero n := by
  induction n with
  | zero =>
      change CRing.mul v v = CRing.zero
      rw [hv, CRing.zero_mul]
  | succ n ih =>
      rw [wedge_eq]
      refine Prod.ext (ih hv.1) ?_
      change add n (wedge n v.1 v.2) (wedge n v.2 (invol n v.1)) = zero n
      rw [invol_on_grade hv.1]
      simp only [signCl]
      have hb : v.2 = smul n (scalarPart n v.2) (one n) := hasGrade_zero_eq_smul_one hv.2
      unfold wedge
      rw [mul_neg, hb, mul_smul, smul_mul, mul_one, one_mul, add_right_neg]

/-! ### Degenerate PGA Null Ideal `inNullIdeal` (`e_0` Two-Sided Nilpotent Ideal) -/

/-- Predicate `x ∈ (e_0)` in `Cl R (m + 1)`: every basis term of `x` contains `e_0`. -/
def inNullIdeal : (m : Nat) → Cl R (m + 1) → Prop
  | 0, x => x.1 = CRing.zero
  | m + 1, x => inNullIdeal m x.1 ∧ inNullIdeal m x.2

theorem inNullIdeal_zero (m : Nat) : inNullIdeal m (zero (R := R) (m + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ⟨ih, ih⟩

theorem inNullIdeal_add (m : Nat) {x y : Cl R (m + 1)}
    (hx : inNullIdeal m x) (hy : inNullIdeal m y) :
    inNullIdeal m (add (m + 1) x y) := by
  induction m with
  | zero =>
      change CRing.add x.1 y.1 = CRing.zero
      rw [hx, hy, CRing.add_zero]
  | succ m ih => exact ⟨ih hx.1 hy.1, ih hx.2 hy.2⟩

theorem inNullIdeal_neg (m : Nat) {x : Cl R (m + 1)}
    (hx : inNullIdeal m x) : inNullIdeal m (neg (m + 1) x) := by
  induction m with
  | zero =>
      change CRing.neg x.1 = CRing.zero
      rw [hx, CRing.neg_zero]
  | succ m ih => exact ⟨ih hx.1, ih hx.2⟩

theorem inNullIdeal_smul (m : Nat) (r : R) {x : Cl R (m + 1)}
    (hx : inNullIdeal m x) : inNullIdeal m (smul (m + 1) r x) := by
  induction m with
  | zero =>
      change CRing.mul r x.1 = CRing.zero
      rw [hx, CRing.mul_zero]
  | succ m ih => exact ⟨ih hx.1, ih hx.2⟩

theorem inNullIdeal_invol (m : Nat) {x : Cl R (m + 1)}
    (hx : inNullIdeal m x) : inNullIdeal m (invol (m + 1) x) := by
  induction m with
  | zero => exact hx
  | succ m ih => exact ⟨ih hx.1, inNullIdeal_neg m (ih hx.2)⟩

theorem inNullIdeal_rev (m : Nat) {x : Cl R (m + 1)}
    (hx : inNullIdeal m x) : inNullIdeal m (rev (m + 1) x) := by
  induction m with
  | zero => exact hx
  | succ m ih => exact ⟨ih hx.1, inNullIdeal_invol m (ih hx.2)⟩

/-- Whenever `q(0) = 0` (such as `pgaMetric` or `zeroMetric`), `(e_0)` is a two-sided ideal
    and its square vanishes identically: `x, y ∈ (e_0) → x ·_q y = 0`. -/
theorem inNullIdeal_mul_left (m : Nat) (q : Fin (m + 1) → R)
    (hq0 : q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero)
    {x : Cl R (m + 1)} (hx : inNullIdeal m x) (y : Cl R (m + 1)) :
    inNullIdeal m (mul q x y) := by
  induction m with
  | zero =>
      change CRing.add (CRing.mul x.1 y.1)
        (CRing.mul (q ⟨0, Nat.zero_lt_succ 0⟩) (CRing.mul x.2 y.2)) = CRing.zero
      rw [hx, hq0, CRing.zero_mul, CRing.zero_mul, CRing.add_zero]
  | succ m ih =>
      have hq' : initMetric q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero := hq0
      exact ⟨
        inNullIdeal_add m (ih (initMetric q) hq' hx.1 y.1)
          (inNullIdeal_smul m (lastMetric q) (ih (initMetric q) hq' hx.2 (invol (m + 1) y.2))),
        inNullIdeal_add m (ih (initMetric q) hq' hx.1 y.2) (ih (initMetric q) hq' hx.2 (invol (m + 1) y.1))
      ⟩

theorem inNullIdeal_mul_right (m : Nat) (q : Fin (m + 1) → R)
    (hq0 : q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero)
    (x : Cl R (m + 1)) {y : Cl R (m + 1)} (hy : inNullIdeal m y) :
    inNullIdeal m (mul q x y) := by
  induction m with
  | zero =>
      change CRing.add (CRing.mul x.1 y.1)
        (CRing.mul (q ⟨0, Nat.zero_lt_succ 0⟩) (CRing.mul x.2 y.2)) = CRing.zero
      rw [hy, hq0, CRing.mul_zero, CRing.zero_mul, CRing.add_zero]
  | succ m ih =>
      have hq' : initMetric q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero := hq0
      exact ⟨
        inNullIdeal_add m (ih (initMetric q) hq' x.1 hy.1)
          (inNullIdeal_smul m (lastMetric q) (ih (initMetric q) hq' x.2 (inNullIdeal_invol m hy.2))),
        inNullIdeal_add m (ih (initMetric q) hq' x.1 hy.2) (ih (initMetric q) hq' x.2 (inNullIdeal_invol m hy.1))
      ⟩

theorem inNullIdeal_mul_nilpotent (m : Nat) (q : Fin (m + 1) → R)
    (hq0 : q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero)
    {x y : Cl R (m + 1)} (hx : inNullIdeal m x) (hy : inNullIdeal m y) :
    mul q x y = zero (m + 1) := by
  induction m with
  | zero =>
      refine Prod.ext ?_ ?_
      · change CRing.add (CRing.mul x.1 y.1)
          (CRing.mul (q ⟨0, Nat.zero_lt_succ 0⟩) (CRing.mul x.2 y.2)) = CRing.zero
        rw [hx, hq0, CRing.zero_mul, CRing.zero_mul, CRing.add_zero]
      · change CRing.add (CRing.mul x.1 y.2) (CRing.mul x.2 y.1) = CRing.zero
        rw [hx, hy, CRing.zero_mul, CRing.mul_zero, CRing.add_zero]
  | succ m ih =>
      have hq' : initMetric q ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero := hq0
      refine Prod.ext ?_ ?_
      · change add (m + 1) (mul (initMetric q) x.1 y.1)
            (smul (m + 1) (lastMetric q) (mul (initMetric q) x.2 (invol (m + 1) y.2))) = zero (m + 1)
        rw [ih (initMetric q) hq' hx.1 hy.1, ih (initMetric q) hq' hx.2 (inNullIdeal_invol m hy.2), smul_zero, add_zero]
      · change add (m + 1) (mul (initMetric q) x.1 y.2)
            (mul (initMetric q) x.2 (invol (m + 1) y.1)) = zero (m + 1)
        rw [ih (initMetric q) hq' hx.1 hy.2, ih (initMetric q) hq' hx.2 (inNullIdeal_invol m hy.1), add_zero]

end ModuleAndAlgebra
end Cl
end Conjecture00000007617
