/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization of Clifford algebras Cl_R(sig) over arbitrary
commutative / ordered commutative rings, with zero external dependencies.
-/

namespace CliffordNormConjecture

/-- Unit element class in Core Lean 4, equipping `1` notation via `OfNat`. -/
class One (R : Type) where
  one : R

instance {R : Type} [One R] : OfNat R 1 := ⟨One.one⟩
instance : One Int := ⟨(1 : Int)⟩

/-- Minimal commutative ring typeclass in Core Lean 4 (no external dependencies). -/
class CommRing (R : Type) extends Add R, Sub R, Neg R, Mul R, Zero R, One R where
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  add_zero : ∀ a : R, a + 0 = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  sub_eq_add_neg : ∀ a b : R, a - b = a + (-b)
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- Nontrivial ordered commutative ring typeclass (satisfied by ℤ, ℚ, and ℝ). -/
class OrderedCommRing (R : Type) extends CommRing R, LE R, LT R where
  lt_iff_le_not_le : ∀ a b : R, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  le_refl : ∀ a : R, a ≤ a
  le_trans : ∀ {a b c : R}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : R}, a ≤ b → b ≤ a → a = b
  add_le_add_left : ∀ {a b : R}, a ≤ b → ∀ c : R, c + a ≤ c + b
  zero_lt_one : (0 : R) < 1
  mul_nonneg : ∀ {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  mul_pos : ∀ {a b : R}, 0 < a → 0 < b → 0 < a * b
  sq_nonneg : ∀ a : R, 0 ≤ a * a

section RingLemmas

variable {R : Type} [CommRing R]

theorem add_neg_cancel (a : R) : a + (-a) = 0 := by
  rw [CommRing.add_comm, CommRing.neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun t => -a + t) h
  rw [← CommRing.add_assoc, ← CommRing.add_assoc, CommRing.neg_add_cancel,
      CommRing.zero_add, CommRing.zero_add] at h1
  exact h1

theorem zero_mul (a : R) : (0 : R) * a = 0 := by
  have h : (0 : R) * a + 0 * a = 0 * a + 0 := by
    rw [← CommRing.right_distrib, CommRing.zero_add, CommRing.add_zero]
  exact add_left_cancel h

theorem mul_zero (a : R) : a * (0 : R) = 0 := by
  rw [CommRing.mul_comm, zero_mul]

theorem neg_zero_eq : -(0 : R) = 0 := by
  have h : -(0 : R) + 0 = 0 + 0 := by
    rw [CommRing.neg_add_cancel, CommRing.zero_add]
  rw [CommRing.add_zero, CommRing.add_zero] at h
  exact h

theorem neg_involutive (a : R) : -(-a) = a := by
  have h : -a + -(-a) = -a + a := by
    rw [add_neg_cancel, CommRing.neg_add_cancel]
  exact add_left_cancel h

theorem neg_eq_neg_one_mul (a : R) : -a = (-1 : R) * a := by
  have h : a + (-a) = a + (-1 : R) * a := by
    rw [add_neg_cancel]
    conv => rhs; lhs; rw [← CommRing.one_mul a]
    rw [← CommRing.right_distrib, add_neg_cancel, zero_mul]
  exact add_left_cancel h

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [neg_eq_neg_one_mul a, neg_eq_neg_one_mul (a * b), CommRing.mul_assoc]

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  rw [CommRing.mul_comm a (-b), neg_mul, CommRing.mul_comm b a]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_involutive]

theorem neg_add_rev (a b : R) : -(a + b) = -a + -b := by
  rw [neg_eq_neg_one_mul, CommRing.left_distrib, ← neg_eq_neg_one_mul, ← neg_eq_neg_one_mul]

theorem add_left_comm (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← CommRing.add_assoc, CommRing.add_comm a b, CommRing.add_assoc]

theorem add_add_add_comm (a b c d : R) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [CommRing.add_assoc, add_left_comm b c d, ← CommRing.add_assoc]

theorem sub_self (a : R) : a - a = 0 := by
  rw [CommRing.sub_eq_add_neg, add_neg_cancel]

/-- Two in any ring: 1 + 1. -/
def two (R : Type) [CommRing R] : R := (1 : R) + 1

/-- Four in any ring: two * two. -/
def four (R : Type) [CommRing R] : R := two R * two R

/-- Eight in any ring: two * four. -/
def eight (R : Type) [CommRing R] : R := two R * four R

end RingLemmas

section OrderLemmas

variable {R : Type} [OrderedCommRing R]

theorem add_le_add_right {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [CommRing.add_comm a c, CommRing.add_comm b c]
  exact OrderedCommRing.add_le_add_left h c

theorem add_le_add {a b c d : R} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  OrderedCommRing.le_trans (add_le_add_right hab c) (OrderedCommRing.add_le_add_left hcd b)

theorem add_nonneg {a b : R} (ha : (0 : R) ≤ a) (hb : (0 : R) ≤ b) : (0 : R) ≤ a + b := by
  have h := add_le_add ha hb
  rw [CommRing.add_zero] at h
  exact h

theorem lt_of_lt_of_le {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rw [OrderedCommRing.lt_iff_le_not_le] at hab ⊢
  refine ⟨OrderedCommRing.le_trans hab.1 hbc, ?_⟩
  intro hca
  exact hab.2 (OrderedCommRing.le_trans hbc hca)

theorem lt_of_le_of_lt {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [OrderedCommRing.lt_iff_le_not_le] at hbc ⊢
  refine ⟨OrderedCommRing.le_trans hab hbc.1, ?_⟩
  intro hca
  exact hbc.2 (OrderedCommRing.le_trans hca hab)

theorem add_lt_add_left {a b : R} (h : a < b) (c : R) : c + a < c + b := by
  rw [OrderedCommRing.lt_iff_le_not_le] at h ⊢
  refine ⟨OrderedCommRing.add_le_add_left h.1 c, ?_⟩
  intro hcb
  have h1 := OrderedCommRing.add_le_add_left hcb (-c)
  rw [← CommRing.add_assoc, ← CommRing.add_assoc, CommRing.neg_add_cancel,
      CommRing.zero_add, CommRing.zero_add] at h1
  exact h.2 h1

theorem add_pos {a b : R} (ha : (0 : R) < a) (hb : (0 : R) < b) : (0 : R) < a + b := by
  have h1 : (0 : R) < a + 0 := by rw [CommRing.add_zero]; exact ha
  have h2 : a + (0 : R) < a + b := add_lt_add_left hb a
  exact lt_of_lt_of_le h1 ((OrderedCommRing.lt_iff_le_not_le _ _).1 h2).1

theorem zero_le_one : (0 : R) ≤ 1 :=
  ((OrderedCommRing.lt_iff_le_not_le 0 1).1 OrderedCommRing.zero_lt_one).1

theorem zero_lt_two : (0 : R) < two R :=
  add_pos OrderedCommRing.zero_lt_one OrderedCommRing.zero_lt_one

theorem zero_le_two : (0 : R) ≤ two R :=
  ((OrderedCommRing.lt_iff_le_not_le 0 (two R)).1 zero_lt_two).1

theorem zero_lt_four : (0 : R) < four R :=
  OrderedCommRing.mul_pos zero_lt_two zero_lt_two

theorem four_lt_eight : four R < eight R := by
  have h : four R + (0 : R) < four R + four R := add_lt_add_left zero_lt_four (four R)
  rw [CommRing.add_zero] at h
  have h2 : four R + four R = eight R := by
    unfold eight two
    rw [CommRing.right_distrib, CommRing.one_mul]
  rw [h2] at h
  exact h

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := by
  intro heq
  subst heq
  exact ((OrderedCommRing.lt_iff_le_not_le a a).1 h).2 (OrderedCommRing.le_refl a)

theorem one_ne_neg_one : (1 : R) ≠ -(1 : R) := by
  intro h
  have h2 : (1 : R) + 1 = -(1 : R) + 1 := congrArg (fun t => t + 1) h
  rw [CommRing.neg_add_cancel] at h2
  exact ne_of_lt (zero_lt_two (R := R)) h2.symm

/-- Parallelogram inequality: (a + b)^2 ≤ 2 * (a^2 + b^2) in any OrderedCommRing. -/
theorem sq_add_le_two_mul_add_sq (a b : R) :
    (a + b) * (a + b) ≤ two R * (a * a + b * b) := by
  have hdiff : (0 : R) ≤ (a - b) * (a - b) := OrderedCommRing.sq_nonneg (a - b)
  have hid : (a + b) * (a + b) + (a - b) * (a - b) = two R * (a * a + b * b) := by
    rw [CommRing.sub_eq_add_neg]
    rw [CommRing.left_distrib, CommRing.right_distrib, CommRing.right_distrib]
    rw [CommRing.left_distrib, CommRing.right_distrib, CommRing.right_distrib]
    rw [mul_neg, neg_mul, neg_mul_neg, CommRing.mul_comm b a]
    unfold two
    rw [CommRing.right_distrib, CommRing.one_mul]
    rw [add_add_add_comm (a * a + a * b) (a * b + b * b) (a * a + -(a * b)) (-(a * b) + b * b)]
    rw [add_add_add_comm (a * a) (a * b) (a * a) (-(a * b))]
    rw [add_neg_cancel, CommRing.add_zero]
    rw [add_add_add_comm (a * b) (b * b) (-(a * b)) (b * b)]
    rw [add_neg_cancel, CommRing.zero_add]
    rw [add_add_add_comm (a * a) (a * a) (b * b) (b * b)]
  have hle := OrderedCommRing.add_le_add_left hdiff ((a + b) * (a + b))
  rw [CommRing.add_zero, hid] at hle
  exact hle

end OrderLemmas

/-- Verified instance of OrderedCommRing on Core Lean's built-in `Int`. -/
instance : OrderedCommRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg
  sub_eq_add_neg := fun a b => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  lt_iff_le_not_le := fun a b => by omega
  le_refl := fun a => by omega
  le_trans := fun h1 h2 => by omega
  le_antisymm := fun h1 h2 => by omega
  add_le_add_left := fun h c => by omega
  zero_lt_one := by omega
  mul_nonneg := Int.mul_nonneg
  mul_pos := Int.mul_pos
  sq_nonneg := fun a => by
    cases Int.le_total 0 a with
    | inl h => exact Int.mul_nonneg h h
    | inr h =>
      have hn : 0 ≤ -a := by omega
      have hp : (-a) * (-a) = a * a := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [← hp]
      exact Int.mul_nonneg hn hn

/-- Recursive construction of the Clifford algebra Cl_R(sig) over a commutative ring R.
    For `sig = []`, `Cl R [] = R`.
    For `sig = c :: cs`, `Cl R (c :: cs) = Cl R cs × Cl R cs`, representing `x₀ + x₁ e`
    where `e² = c` and `e` anticommutes with odd elements of `Cl R cs`. -/
@[reducible] def Cl (R : Type) : List R → Type
  | [] => R
  | _ :: cs => Cl R cs × Cl R cs

namespace Cl

section BasicOps

variable {R : Type} [CommRing R]

def zero : {sig : List R} → Cl R sig
  | [] => (0 : R)
  | _ :: _ => (zero, zero)

def one : {sig : List R} → Cl R sig
  | [] => (1 : R)
  | _ :: _ => (one, zero)

def add : {sig : List R} → Cl R sig → Cl R sig → Cl R sig
  | [], x, y => x + y
  | _ :: _, (x0, x1), (y0, y1) => (add x0 y0, add x1 y1)

def neg : {sig : List R} → Cl R sig → Cl R sig
  | [], x => -x
  | _ :: _, (x0, x1) => (neg x0, neg x1)

def sub {sig : List R} (x y : Cl R sig) : Cl R sig :=
  add x (neg y)

def smul : {sig : List R} → R → Cl R sig → Cl R sig
  | [], r, x => r * x
  | _ :: _, r, (x0, x1) => (smul r x0, smul r x1)

/-- Grade involution `X̂` (multiplies grade-k blades by `(-1)^k`). -/
def involute : {sig : List R} → Cl R sig → Cl R sig
  | [], x => x
  | _ :: _, (x0, x1) => (involute x0, neg (involute x1))

/-- Reversal `X̃` (reverses blade order; multiplies grade-k blades by `(-1)^{k(k-1)/2}`). -/
def rev : {sig : List R} → Cl R sig → Cl R sig
  | [], x => x
  | _ :: _, (x0, x1) => (rev x0, involute (rev x1))

/-- Clifford conjugation `X̄ = rev (involute X)` (sign `(-1)^{k(k+1)/2}`). -/
def conj : {sig : List R} → Cl R sig → Cl R sig
  | [], x => x
  | _ :: _, (x0, x1) => (conj x0, neg (involute (conj x1)))

/-- Geometric product on `Cl R sig`:
    `(x₀ + x₁ e)(y₀ + y₁ e) = (x₀ y₀ + c · x₁ ŷ₁) + (x₀ y₁ + x₁ ŷ₀) e`. -/
def mul : {sig : List R} → Cl R sig → Cl R sig → Cl R sig
  | [], x, y => x * y
  | c :: _, (x0, x1), (y0, y1) =>
      (add (mul x0 y0) (smul c (mul x1 (involute y1))),
       add (mul x0 y1) (mul x1 (involute y0)))

/-- Scalar (grade-0) part `⟨X⟩₀`. -/
def scalarPart : {sig : List R} → Cl R sig → R
  | [], x => x
  | _ :: _, (x0, _) => scalarPart x0

/-- Euclidean L²-blade coordinate norm squared `‖X‖₂² = ∑_A x_A²`. -/
def l2NormSq : {sig : List R} → Cl R sig → R
  | [], x => x * x
  | _ :: _, (x0, x1) => l2NormSq x0 + l2NormSq x1

/-- Scalar reversal quadratic form `N_rev(X) = ⟨X̃ X⟩₀`. -/
def revNorm {sig : List R} (x : Cl R sig) : R :=
  scalarPart (mul (rev x) x)

/-- Scalar Clifford-conjugation quadratic form `N_conj(X) = ⟨X̄ X⟩₀`. -/
def conjNorm {sig : List R} (x : Cl R sig) : R :=
  scalarPart (mul (conj x) x)

/-- Canonical isometric algebra embedding `Cl R cs ↪ Cl R (c :: cs)`. -/
def embedLeft {c : R} {cs : List R} (x : Cl R cs) : Cl R (c :: cs) :=
  (x, zero)

/-- Iterated prefix embedding `Cl R cs ↪ Cl R (pfx ++ cs)`. -/
def embedPrefix : (pfx : List R) → {cs : List R} → Cl R cs → Cl R (pfx ++ cs)
  | [], _, x => x
  | _ :: ps, _, x => embedLeft (embedPrefix ps x)

/-- Coordinate vector space matching `sig : List R`. -/
@[reducible] def Vec (R : Type) : List R → Type
  | [] => PUnit
  | _ :: cs => Vec R cs × R

/-- Quadratic form `Q_sig(v) = ∑ c_i v_i²`. -/
def quadForm : {sig : List R} → Vec R sig → R
  | [], _ => 0
  | c :: _, (vs, v) => quadForm vs + c * (v * v)

/-- Euclidean vector norm squared `∑ v_i²`. -/
def vecL2Sq : {sig : List R} → Vec R sig → R
  | [], _ => 0
  | _ :: _, (vs, v) => vecL2Sq vs + v * v

/-- Embedding of grade-1 vectors `Vec R sig ↪ Cl R sig`. -/
def ofVec : {sig : List R} → Vec R sig → Cl R sig
  | [], _ => (0 : R)
  | _ :: _, (vs, v) => (ofVec vs, smul v one)

/-- Predicate asserting that `x : Cl R sig` lies in the grade-1 vector subspace. -/
def isGradeOne : {sig : List R} → Cl R sig → Prop
  | [], x => x = 0
  | _ :: _, (x0, x1) => isGradeOne x0 ∧ ∃ r : R, x1 = smul r one

/-- Product of a list of grade-1 vectors (a versor in the Lipschitz monoid). -/
def versor {sig : List R} : List (Vec R sig) → Cl R sig
  | [] => one
  | v :: vs => mul (ofVec v) (versor vs)

/-- Reducible replicated signature list so fixed-dimension `Cl R (eucSig R k)`
    unfolds transparently during typeclass synthesis. -/
@[reducible] def repSig {R : Type} (c : R) : Nat → List R
  | 0 => []
  | n + 1 => c :: repSig c n

/-- Euclidean signature `(1, ..., 1)` of dimension `n` (`Cl_{n,0}`). -/
@[reducible] def eucSig (R : Type) [CommRing R] (n : Nat) : List R :=
  repSig (1 : R) n

/-- Spin-geometry negative-definite signature `(-1, ..., -1)` of dimension `n` (`Cl_{0,n}`). -/
@[reducible] def spinSig (R : Type) [CommRing R] (n : Nat) : List R :=
  repSig (-(1 : R)) n

end BasicOps

section AlgebraicLaws

variable {R : Type} [CommRing R]

theorem add_comm_cl {sig : List R} (x y : Cl R sig) : add x y = add y x := by
  induction sig with
  | nil => exact CommRing.add_comm x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem add_assoc_cl {sig : List R} (x y z : Cl R sig) :
    add (add x y) z = add x (add y z) := by
  induction sig with
  | nil => exact CommRing.add_assoc x y z
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    exact Prod.ext (ih x0 y0 z0) (ih x1 y1 z1)

theorem zero_add_cl {sig : List R} (x : Cl R sig) : add zero x = x := by
  induction sig with
  | nil => exact CommRing.zero_add x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem add_zero_cl {sig : List R} (x : Cl R sig) : add x zero = x := by
  induction sig with
  | nil => exact CommRing.add_zero x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem neg_add_cancel_cl {sig : List R} (x : Cl R sig) : add (neg x) x = zero := by
  induction sig with
  | nil => exact CommRing.neg_add_cancel x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem add_neg_cancel_cl {sig : List R} (x : Cl R sig) : add x (neg x) = zero := by
  rw [add_comm_cl, neg_add_cancel_cl]

theorem neg_zero_cl {sig : List R} : neg (zero : Cl R sig) = zero := by
  induction sig with
  | nil => exact neg_zero_eq
  | cons _ _ ih => exact Prod.ext ih ih

theorem neg_involutive_cl {sig : List R} (x : Cl R sig) : neg (neg x) = x := by
  induction sig with
  | nil => exact neg_involutive x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem neg_add_cl {sig : List R} (x y : Cl R sig) :
    neg (add x y) = add (neg x) (neg y) := by
  induction sig with
  | nil => exact neg_add_rev x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem add_left_comm_cl {sig : List R} (x y z : Cl R sig) :
    add x (add y z) = add y (add x z) := by
  rw [← add_assoc_cl, add_comm_cl x y, add_assoc_cl]

theorem add_add_add_comm_cl {sig : List R} (a b c d : Cl R sig) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc_cl, add_left_comm_cl b c d, ← add_assoc_cl]

theorem smul_zero_cl {sig : List R} (r : R) : smul r (zero : Cl R sig) = zero := by
  induction sig with
  | nil => exact mul_zero r
  | cons _ _ ih => exact Prod.ext (ih) (ih)

theorem zero_smul_cl {sig : List R} (x : Cl R sig) : smul 0 x = zero := by
  induction sig with
  | nil => exact zero_mul x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem one_smul_cl {sig : List R} (x : Cl R sig) : smul 1 x = x := by
  induction sig with
  | nil => exact CommRing.one_mul x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_add_cl {sig : List R} (r : R) (x y : Cl R sig) :
    smul r (add x y) = add (smul r x) (smul r y) := by
  induction sig with
  | nil => exact CommRing.left_distrib r x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    exact Prod.ext (ih x0 y0) (ih x1 y1)

theorem add_smul_cl {sig : List R} (r s : R) (x : Cl R sig) :
    smul (r + s) x = add (smul r x) (smul s x) := by
  induction sig with
  | nil => exact CommRing.right_distrib r s x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_smul_cl {sig : List R} (r s : R) (x : Cl R sig) :
    smul (r * s) x = smul r (smul s x) := by
  induction sig with
  | nil => exact CommRing.mul_assoc r s x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem smul_neg_cl {sig : List R} (r : R) (x : Cl R sig) :
    smul r (neg x) = neg (smul r x) := by
  induction sig with
  | nil => exact mul_neg r x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem neg_smul_cl {sig : List R} (r : R) (x : Cl R sig) :
    smul (-r) x = neg (smul r x) := by
  induction sig with
  | nil => exact neg_mul r x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) (ih x1)

theorem involute_zero {sig : List R} : involute (zero : Cl R sig) = zero := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    simp only [involute, zero, ih, neg_zero_cl]

theorem involute_one {sig : List R} : involute (one : Cl R sig) = one := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    simp only [involute, one, ih, involute_zero, neg_zero_cl]

theorem involute_add {sig : List R} (x y : Cl R sig) :
    involute (add x y) = add (involute x) (involute y) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    simp only [involute, add, ih, neg_add_cl]

theorem involute_neg {sig : List R} (x : Cl R sig) :
    involute (neg x) = neg (involute x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [involute, neg, ih]

theorem involute_smul {sig : List R} (r : R) (x : Cl R sig) :
    involute (smul r x) = smul r (involute x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [involute, smul, ih, smul_neg_cl]

theorem involute_involutive {sig : List R} (x : Cl R sig) :
    involute (involute x) = x := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [involute, involute_neg, ih, neg_involutive_cl]

theorem zero_mul_cl {sig : List R} (x : Cl R sig) : mul zero x = zero := by
  induction sig with
  | nil => exact zero_mul x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [mul, zero, ih, smul_zero_cl, add_zero_cl]

theorem mul_zero_cl {sig : List R} (x : Cl R sig) : mul x zero = zero := by
  induction sig with
  | nil => exact mul_zero x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [mul, zero, involute_zero, ih, smul_zero_cl, add_zero_cl]

theorem one_mul_cl {sig : List R} (x : Cl R sig) : mul one x = x := by
  induction sig with
  | nil => exact CommRing.one_mul x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [mul, one, ih, zero_mul_cl, smul_zero_cl, add_zero_cl]

theorem mul_one_cl {sig : List R} (x : Cl R sig) : mul x one = x := by
  induction sig with
  | nil => exact CommRing.mul_one x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [mul, one, involute_zero, involute_one, ih, mul_zero_cl, smul_zero_cl,
      add_zero_cl, zero_add_cl]

theorem smul_mul_cl {sig : List R} (r : R) (x y : Cl R sig) :
    mul (smul r x) y = smul r (mul x y) := by
  induction sig with
  | nil => exact CommRing.mul_assoc r x y
  | cons c _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    refine Prod.ext ?_ ?_
    · simp only [mul, smul, ih, smul_add_cl]
      rw [← smul_smul_cl, CommRing.mul_comm c r, smul_smul_cl]
    · simp only [mul, smul, ih, smul_add_cl]

theorem mul_smul_cl {sig : List R} (r : R) (x y : Cl R sig) :
    mul x (smul r y) = smul r (mul x y) := by
  induction sig with
  | nil =>
    change x * (r * y) = r * (x * y)
    rw [← CommRing.mul_assoc, CommRing.mul_comm x r, CommRing.mul_assoc]
  | cons c _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    refine Prod.ext ?_ ?_
    · simp only [mul, smul, involute_smul, ih, smul_add_cl]
      rw [← smul_smul_cl, CommRing.mul_comm c r, smul_smul_cl]
    · simp only [mul, smul, involute_smul, ih, smul_add_cl]

theorem neg_mul_cl {sig : List R} (x y : Cl R sig) :
    mul (neg x) y = neg (mul x y) := by
  induction sig with
  | nil => exact neg_mul x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    simp only [mul, neg, ih, smul_neg_cl, neg_add_cl]

theorem mul_neg_cl {sig : List R} (x y : Cl R sig) :
    mul x (neg y) = neg (mul x y) := by
  induction sig with
  | nil => exact mul_neg x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    simp only [mul, neg, involute_neg, ih, smul_neg_cl, neg_add_cl]

theorem left_distrib_cl {sig : List R} (x y z : Cl R sig) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  induction sig with
  | nil => exact CommRing.left_distrib x y z
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    refine Prod.ext ?_ ?_
    · simp only [mul, add, involute_add, ih, smul_add_cl]
      exact add_add_add_comm_cl _ _ _ _
    · simp only [mul, add, involute_add, ih]
      exact add_add_add_comm_cl _ _ _ _

theorem right_distrib_cl {sig : List R} (x y z : Cl R sig) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  induction sig with
  | nil => exact CommRing.right_distrib x y z
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    refine Prod.ext ?_ ?_
    · simp only [mul, add, ih, smul_add_cl]
      exact add_add_add_comm_cl _ _ _ _
    · simp only [mul, add, ih]
      exact add_add_add_comm_cl _ _ _ _

/-- Grade involution is an algebra automorphism: `involute (X Y) = involute X * involute Y`. -/
theorem involute_mul {sig : List R} (x y : Cl R sig) :
    involute (mul x y) = mul (involute x) (involute y) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    simp only [mul, involute, involute_add, involute_smul, ih,
      involute_neg, neg_mul_cl, mul_neg_cl, neg_involutive_cl, neg_add_cl]

/-- Associativity of the geometric product on `Cl R sig` for any signature `sig`. -/
theorem mul_assoc_cl {sig : List R} (x y z : Cl R sig) :
    mul (mul x y) z = mul x (mul y z) := by
  induction sig with
  | nil => exact CommRing.mul_assoc x y z
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩; rcases z with ⟨z0, z1⟩
    refine Prod.ext ?_ ?_
    · simp only [mul, right_distrib_cl, left_distrib_cl, involute_add, involute_smul,
        involute_mul, involute_involutive, smul_mul_cl, mul_smul_cl, smul_add_cl, ih]
      rw [add_assoc_cl, add_assoc_cl]
      apply congrArg (add (mul x0 (mul y0 z0)))
      rw [add_left_comm_cl]
      exact congrArg (add _) (add_comm_cl _ _)
    · simp only [mul, right_distrib_cl, left_distrib_cl, involute_add, involute_smul,
        involute_mul, involute_involutive, smul_mul_cl, mul_smul_cl, smul_add_cl, ih]
      rw [add_assoc_cl, add_assoc_cl]
      apply congrArg (add (mul x0 (mul y0 z1)))
      rw [add_left_comm_cl]
      exact congrArg (add _) (add_comm_cl _ _)

theorem rev_neg {sig : List R} (x : Cl R sig) : rev (neg x) = neg (rev x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [rev, neg, ih, involute_neg]

/-- Reversal commutes with grade involution. -/
theorem rev_involute {sig : List R} (x : Cl R sig) :
    rev (involute x) = involute (rev x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [involute, rev, rev_neg, ih, involute_neg]

theorem rev_add {sig : List R} (x y : Cl R sig) : rev (add x y) = add (rev x) (rev y) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    simp only [rev, add, ih, involute_add]

theorem rev_smul {sig : List R} (r : R) (x : Cl R sig) : rev (smul r x) = smul r (rev x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [rev, smul, ih, involute_smul]

theorem rev_zero {sig : List R} : rev (zero : Cl R sig) = zero := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    simp only [rev, zero, ih, involute_zero]

theorem rev_one {sig : List R} : rev (one : Cl R sig) = one := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    simp only [rev, one, ih, rev_zero, involute_zero]

theorem rev_involutive {sig : List R} (x : Cl R sig) : rev (rev x) = x := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [rev, rev_involute, ih, involute_involutive]

/-- Reversal is an algebra anti-automorphism: `rev (X Y) = rev Y * rev X`. -/
theorem rev_mul {sig : List R} (x y : Cl R sig) :
    rev (mul x y) = mul (rev y) (rev x) := by
  induction sig with
  | nil => exact CommRing.mul_comm x y
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    refine Prod.ext ?_ ?_
    · simp only [rev, mul, rev_add, rev_smul, ih, rev_involute,
        involute_mul, involute_involutive]
    · simp only [rev, mul, rev_add, ih, rev_involute,
        involute_add, involute_mul, involute_involutive]
      exact add_comm_cl _ _

/-- Clifford conjugation equals `rev ∘ involute`. -/
theorem conj_eq_rev_involute {sig : List R} (x : Cl R sig) :
    conj x = rev (involute x) := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [conj, involute, rev, rev_neg, involute_neg, ih]

theorem conj_involutive {sig : List R} (x : Cl R sig) : conj (conj x) = x := by
  rw [conj_eq_rev_involute, conj_eq_rev_involute, rev_involute, rev_involutive, involute_involutive]

/-- Clifford conjugation is an algebra anti-automorphism: `conj (X Y) = conj Y * conj X`. -/
theorem conj_mul {sig : List R} (x y : Cl R sig) :
    conj (mul x y) = mul (conj y) (conj x) := by
  rw [conj_eq_rev_involute, conj_eq_rev_involute, conj_eq_rev_involute, involute_mul, rev_mul]

theorem conj_smul {sig : List R} (r : R) (x : Cl R sig) :
    conj (smul r x) = smul r (conj x) := by
  rw [conj_eq_rev_involute, conj_eq_rev_involute, involute_smul, rev_smul]

theorem conj_one {sig : List R} : conj (one : Cl R sig) = one := by
  rw [conj_eq_rev_involute, involute_one, rev_one]

/-- Scalar part lemmas. -/
theorem scalarPart_add {sig : List R} (x y : Cl R sig) :
    scalarPart (add x y) = scalarPart x + scalarPart y := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, _⟩; rcases y with ⟨y0, _⟩
    exact ih x0 y0

theorem scalarPart_smul {sig : List R} (r : R) (x : Cl R sig) :
    scalarPart (smul r x) = r * scalarPart x := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, _⟩
    exact ih x0

theorem scalarPart_one {sig : List R} : scalarPart (one : Cl R sig) = 1 := by
  induction sig with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem scalarPart_zero {sig : List R} : scalarPart (zero : Cl R sig) = 0 := by
  induction sig with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem scalarPart_involute {sig : List R} (x : Cl R sig) :
    scalarPart (involute x) = scalarPart x := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, _⟩
    exact ih x0

/-- L²-norm invariance under involutions and scalar multiplication. -/
theorem l2NormSq_zero {sig : List R} : l2NormSq (zero : Cl R sig) = 0 := by
  induction sig with
  | nil => exact zero_mul (0 : R)
  | cons _ _ ih =>
    simp only [l2NormSq, zero, ih, CommRing.add_zero]

theorem l2NormSq_one {sig : List R} : l2NormSq (one : Cl R sig) = 1 := by
  induction sig with
  | nil => exact CommRing.one_mul (1 : R)
  | cons _ _ ih =>
    simp only [l2NormSq, one, ih, l2NormSq_zero, CommRing.add_zero]

theorem l2NormSq_neg {sig : List R} (x : Cl R sig) : l2NormSq (neg x) = l2NormSq x := by
  induction sig with
  | nil => exact neg_mul_neg x x
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [l2NormSq, neg, ih]

theorem l2NormSq_involute {sig : List R} (x : Cl R sig) : l2NormSq (involute x) = l2NormSq x := by
  induction sig with
  | nil => rfl
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [l2NormSq, involute, l2NormSq_neg, ih]

theorem l2NormSq_smul {sig : List R} (r : R) (x : Cl R sig) :
    l2NormSq (smul r x) = (r * r) * l2NormSq x := by
  induction sig with
  | nil =>
    change (r * x) * (r * x) = (r * r) * (x * x)
    rw [CommRing.mul_assoc r x (r * x), ← CommRing.mul_assoc x r x,
        CommRing.mul_comm x r, CommRing.mul_assoc r x x, ← CommRing.mul_assoc r r (x * x)]
  | cons _ _ ih =>
    rcases x with ⟨x0, x1⟩
    simp only [l2NormSq, smul, ih, CommRing.left_distrib]

/-- Embedding preservation laws for `embedLeft` and `embedPrefix`. -/
theorem embedLeft_mul {c : R} {cs : List R} (x y : Cl R cs) :
    embedLeft (c := c) (mul x y) = mul (embedLeft x) (embedLeft y) := by
  simp only [embedLeft, mul, involute_zero, mul_zero_cl, zero_mul_cl, smul_zero_cl, add_zero_cl]

theorem embedLeft_involute {c : R} {cs : List R} (x : Cl R cs) :
    involute (embedLeft (c := c) x) = embedLeft (involute x) := by
  simp only [embedLeft, involute, involute_zero, neg_zero_cl]

theorem embedLeft_l2NormSq {c : R} {cs : List R} (x : Cl R cs) :
    l2NormSq (embedLeft (c := c) x) = l2NormSq x := by
  simp only [embedLeft, l2NormSq, l2NormSq_zero, CommRing.add_zero]

theorem embedLeft_revNorm {c : R} {cs : List R} (x : Cl R cs) :
    revNorm (embedLeft (c := c) x) = revNorm x := by
  simp only [revNorm, embedLeft, rev, rev_zero, involute_zero, mul, zero_mul_cl, smul_zero_cl,
    add_zero_cl, scalarPart]

theorem embedLeft_conjNorm {c : R} {cs : List R} (x : Cl R cs) :
    conjNorm (embedLeft (c := c) x) = conjNorm x := by
  have hz : conj (zero : Cl R cs) = zero := by
    rw [conj_eq_rev_involute, involute_zero, rev_zero]
  simp only [conjNorm, embedLeft, conj, hz, involute_zero, neg_zero_cl, mul,
    zero_mul_cl, smul_zero_cl, add_zero_cl, scalarPart]

theorem embedLeft_eq_zero_iff {c : R} {cs : List R} (x : Cl R cs) :
    embedLeft (c := c) x = zero ↔ x = zero := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    rw [h]
    rfl

theorem embedPrefix_mul (pfx : List R) {cs : List R} (x y : Cl R cs) :
    embedPrefix pfx (mul x y) = mul (embedPrefix pfx x) (embedPrefix pfx y) := by
  induction pfx with
  | nil => rfl
  | cons _ ps ih => simp only [embedPrefix, ih, embedLeft_mul]

theorem embedPrefix_involute (pfx : List R) {cs : List R} (x : Cl R cs) :
    involute (embedPrefix pfx x) = embedPrefix pfx (involute x) := by
  induction pfx with
  | nil => rfl
  | cons _ ps ih => simp only [embedPrefix, embedLeft_involute, ih]

theorem embedPrefix_l2NormSq (pfx : List R) {cs : List R} (x : Cl R cs) :
    l2NormSq (embedPrefix pfx x) = l2NormSq x := by
  induction pfx with
  | nil => rfl
  | cons _ ps ih => simp only [embedPrefix, embedLeft_l2NormSq, ih]

theorem embedPrefix_revNorm (pfx : List R) {cs : List R} (x : Cl R cs) :
    revNorm (embedPrefix pfx x) = revNorm x := by
  induction pfx with
  | nil => rfl
  | cons _ ps ih => simp only [embedPrefix, embedLeft_revNorm, ih]

theorem embedPrefix_conjNorm (pfx : List R) {cs : List R} (x : Cl R cs) :
    conjNorm (embedPrefix pfx x) = conjNorm x := by
  induction pfx with
  | nil => rfl
  | cons _ ps ih => simp only [embedPrefix, embedLeft_conjNorm, ih]

theorem embedPrefix_eq_zero_iff (pfx : List R) {cs : List R} (x : Cl R cs) :
    embedPrefix pfx x = zero ↔ x = zero := by
  induction pfx with
  | nil => exact Iff.rfl
  | cons _ ps ih => exact Iff.trans (embedLeft_eq_zero_iff _) ih

end AlgebraicLaws

end Cl
end CliffordNormConjecture
