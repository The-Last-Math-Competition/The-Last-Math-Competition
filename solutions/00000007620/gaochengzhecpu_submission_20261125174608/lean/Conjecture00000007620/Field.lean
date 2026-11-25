/-
  Conjecture 00000007620 — Algebraic Foundations & Ring Spectral Invariants
  Pure Core Lean 4.19.0 (zero external dependencies, zero sorry, zero axioms).
-/

namespace Conjecture00000007620

universe u v

/-- Genuine associative unital ring typeclass. -/
class AssocRing (R : Type u) extends Zero R, OfNat R 1, Add R, Neg R, Sub R, Mul R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  add_zero : ∀ a : R, a + 0 = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

section RingLemmas

variable {R : Type u} [AssocRing R]

theorem add_neg_cancel_right_ring (a : R) : a + -a = 0 := by
  rw [AssocRing.add_comm, AssocRing.neg_add_cancel]

theorem add_left_cancel_ring {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← AssocRing.add_assoc, ← AssocRing.add_assoc, AssocRing.neg_add_cancel,
      AssocRing.zero_add, AssocRing.zero_add] at h1
  exact h1

theorem add_right_cancel_ring {a b c : R} (h : b + a = c + a) : b = c := by
  apply add_left_cancel_ring (a := a)
  rw [AssocRing.add_comm a b, AssocRing.add_comm a c]
  exact h

theorem mul_zero_ring (a : R) : a * 0 = 0 := by
  apply add_left_cancel_ring (a := a * 0)
  rw [← AssocRing.left_distrib, AssocRing.add_zero, AssocRing.add_zero]

theorem zero_mul_ring (a : R) : 0 * a = 0 := by
  apply add_left_cancel_ring (a := 0 * a)
  rw [← AssocRing.right_distrib, AssocRing.add_zero, AssocRing.add_zero]

theorem neg_zero_ring : -(0 : R) = 0 := by
  apply add_right_cancel_ring (a := (0 : R))
  rw [AssocRing.neg_add_cancel, AssocRing.zero_add]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel_ring (a := a)
  rw [add_neg_cancel_right_ring, h]

theorem neg_neg_ring (a : R) : -(-a) = a :=
  neg_eq_of_add_eq_zero (AssocRing.neg_add_cancel a)

theorem neg_add_distrib_ring (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  have h : a + b + (-a + -b) = a + -a + (b + -b) := by
    rw [AssocRing.add_assoc a b (-a + -b),
        ← AssocRing.add_assoc b (-a) (-b),
        AssocRing.add_comm b (-a),
        AssocRing.add_assoc (-a) b (-b),
        ← AssocRing.add_assoc a (-a) (b + -b)]
  rw [h, add_neg_cancel_right_ring, add_neg_cancel_right_ring, AssocRing.add_zero]

theorem mul_neg_ring (a b : R) : a * -b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← AssocRing.left_distrib, add_neg_cancel_right_ring, mul_zero_ring]

theorem neg_mul_ring (a b : R) : -a * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← AssocRing.right_distrib, add_neg_cancel_right_ring, zero_mul_ring]

theorem neg_mul_neg_ring (a b : R) : -a * -b = a * b := by
  rw [neg_mul_ring, mul_neg_ring, neg_neg_ring]

theorem sub_self_ring (a : R) : a - a = 0 := by
  rw [AssocRing.sub_eq_add_neg, add_neg_cancel_right_ring]

theorem sub_eq_zero_iff_eq {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply add_right_cancel_ring (a := -b)
    rw [← AssocRing.sub_eq_add_neg, h, add_neg_cancel_right_ring]
  · intro h
    rw [h, sub_self_ring]

theorem mul_sub_ring (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.left_distrib, mul_neg_ring, ← AssocRing.sub_eq_add_neg]

theorem sub_mul_ring (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.right_distrib, neg_mul_ring, ← AssocRing.sub_eq_add_neg]

end RingLemmas

/-- Genuine unital ring homomorphism between associative rings. -/
structure RingHom (A : Type u) (B : Type v) [AssocRing A] [AssocRing B] where
  toFun : A → B
  map_one : toFun 1 = 1
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y : A, toFun (x * y) = toFun x * toFun y

namespace RingHom

variable {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]

theorem map_zero (f : RingHom A B) : f.toFun 0 = 0 := by
  apply add_left_cancel_ring (a := f.toFun 0)
  rw [← f.map_add, AssocRing.add_zero, AssocRing.add_zero]

theorem map_neg (f : RingHom A B) (x : A) : f.toFun (-x) = -(f.toFun x) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← f.map_add, add_neg_cancel_right_ring, f.map_zero]

end RingHom

/-- Genuine bijective unital ring isomorphism between associative rings. -/
structure RingIso (A : Type u) (B : Type v) [AssocRing A] [AssocRing B] where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x : A, invFun (toFun x) = x
  right_inv : ∀ y : B, toFun (invFun y) = y
  map_one : toFun 1 = 1
  map_add : ∀ x y : A, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y : A, toFun (x * y) = toFun x * toFun y

namespace RingIso

variable {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]

def toRingHom (e : RingIso A B) : RingHom A B where
  toFun := e.toFun
  map_one := e.map_one
  map_add := e.map_add
  map_mul := e.map_mul

theorem map_zero (e : RingIso A B) : e.toFun 0 = 0 :=
  e.toRingHom.map_zero

theorem map_neg (e : RingIso A B) (x : A) : e.toFun (-x) = -(e.toFun x) :=
  e.toRingHom.map_neg x

theorem injective (e : RingIso A B) {x y : A} (h : e.toFun x = e.toFun y) : x = y := by
  have h1 := congrArg e.invFun h
  rw [e.left_inv, e.left_inv] at h1
  exact h1

def symm (e : RingIso A B) : RingIso B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_one := by
    apply e.injective
    rw [e.right_inv, e.map_one]
  map_add := fun x y => by
    apply e.injective
    rw [e.right_inv, e.map_add, e.right_inv, e.right_inv]
  map_mul := fun x y => by
    apply e.injective
    rw [e.right_inv, e.map_mul, e.right_inv, e.right_inv]

end RingIso

/-! ### Intrinsic Ring-Theoretic Spectral Invariants (Layer 2: Clifford Spectrum) -/

/-- Element lies in the center Z(A) of the ring A. -/
def IsCentral {A : Type u} [AssocRing A] (z : A) : Prop :=
  ∀ x : A, z * x = x * z

/-- Central idempotent: element of Idem(Z(A)) = {z ∈ Z(A) | z² = z}. -/
def IsCentralIdem {A : Type u} [AssocRing A] (z : A) : Prop :=
  IsCentral z ∧ z * z = z

/-- The central idempotent spectrum of A contains a nontrivial idempotent (z ∉ {0, 1}),
    corresponding to disconnected Spec(Z(A)) / non-simple Wedderburn block decomposition. -/
def HasNontrivialCentralIdem (A : Type u) [AssocRing A] : Prop :=
  ∃ z : A, IsCentralIdem z ∧ z ≠ 0 ∧ z ≠ 1

/-- Existence of a nontrivial central involution (w ∈ Z(A), w² = 1, w ≠ ±1),
    corresponding to split pseudoscalar eigenvalue spectrum {+1, -1}. -/
def HasNontrivialCentralInvolution (A : Type u) [AssocRing A] : Prop :=
  ∃ w : A, IsCentral w ∧ w * w = 1 ∧ w ≠ 1 ∧ w ≠ -1

/-- Pierce k-orthogonality capacity: existence of k nonzero mutually orthogonal idempotents,
    measuring the direct-sum length of the regular module (e.g., 4 in M₄(F) vs ≤ 2 in M₂(ℍ_F)). -/
def HasOrthogonalIdempotents (A : Type u) [AssocRing A] (k : Nat) : Prop :=
  ∃ p : Fin k → A,
    (∀ i : Fin k, p i ≠ 0 ∧ p i * p i = p i) ∧
    (∀ i j : Fin k, i ≠ j → p i * p j = 0)

theorem RingIso.preserve_centralIdem {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]
    (e : RingIso A B) : HasNontrivialCentralIdem A → HasNontrivialCentralIdem B := by
  rintro ⟨z, ⟨hzC, hzI⟩, hz0, hz1⟩
  refine ⟨e.toFun z, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y
    have h := congrArg e.toFun (hzC (e.invFun y))
    rw [e.map_mul, e.map_mul, e.right_inv] at h
    exact h
  · rw [← e.map_mul, hzI]
  · intro h0
    rw [← e.map_zero] at h0
    exact hz0 (e.injective h0)
  · intro h1
    rw [← e.map_one] at h1
    exact hz1 (e.injective h1)

theorem RingIso.preserve_centralInvolution {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]
    (e : RingIso A B) : HasNontrivialCentralInvolution A → HasNontrivialCentralInvolution B := by
  rintro ⟨w, hwC, hw2, hw1, hwn1⟩
  refine ⟨e.toFun w, ?_, ?_, ?_, ?_⟩
  · intro y
    have h := congrArg e.toFun (hwC (e.invFun y))
    rw [e.map_mul, e.map_mul, e.right_inv] at h
    exact h
  · rw [← e.map_mul, hw2, e.map_one]
  · intro h1
    rw [← e.map_one] at h1
    exact hw1 (e.injective h1)
  · intro hn1
    have hm : -(1 : B) = e.toFun (-1) := by
      rw [e.map_neg, e.map_one]
    rw [hm] at hn1
    exact hwn1 (e.injective hn1)

theorem RingIso.preserve_orthogonalIdempotents {A : Type u} {B : Type v}
    [AssocRing A] [AssocRing B] (e : RingIso A B) {k : Nat} :
    HasOrthogonalIdempotents A k → HasOrthogonalIdempotents B k := by
  rintro ⟨p, hp, horth⟩
  refine ⟨fun i => e.toFun (p i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · intro h0
      rw [← e.map_zero] at h0
      exact (hp i).1 (e.injective h0)
    · rw [← e.map_mul, (hp i).2]
  · intro i j hij
    rw [← e.map_mul, horth i j hij, e.map_zero]

/-! ### Formally Real Fields and Exact Rational Field Construction -/

/-- A formally real field: commutative field in which a sum of four squares vanishes
    only when all four terms vanish (satisfied by ℝ, ℚ, real algebraic numbers, etc.). -/
class FormallyRealField (F : Type u) extends AssocRing F where
  inv : F → F
  mul_comm : ∀ a b : F, a * b = b * a
  zero_ne_one : (0 : F) ≠ 1
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * inv a = 1
  inv_zero : inv (0 : F) = 0
  sum_four_sq_eq_zero :
    ∀ a b c d : F, a * a + b * b + c * c + d * d = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

section FieldLemmas

variable {F : Type u} [FormallyRealField F]

theorem one_ne_zero_field : (1 : F) ≠ 0 :=
  fun h => FormallyRealField.zero_ne_one h.symm

theorem inv_mul_cancel_field {a : F} (ha : a ≠ 0) : FormallyRealField.inv a * a = 1 := by
  rw [FormallyRealField.mul_comm]
  exact FormallyRealField.mul_inv_cancel a ha

theorem mul_eq_zero_field {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h1 : FormallyRealField.inv a * (a * b) = FormallyRealField.inv a * 0 :=
      congrArg (fun x => FormallyRealField.inv a * x) h
    rw [← AssocRing.mul_assoc, inv_mul_cancel_field ha, AssocRing.one_mul, mul_zero_ring] at h1
    exact h1

theorem two_ne_zero_field : (1 + 1 : F) ≠ 0 := by
  intro h2
  have h4 : (1 : F) * 1 + (1 : F) * 1 + (0 : F) * 0 + (0 : F) * 0 = 0 := by
    rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero, AssocRing.add_zero]
    exact h2
  have h1 := (FormallyRealField.sum_four_sq_eq_zero 1 1 0 0 h4).1
  exact one_ne_zero_field h1

def halfField (F : Type u) [FormallyRealField F] : F := FormallyRealField.inv (1 + 1 : F)

theorem two_mul_half_field : (1 + 1 : F) * halfField F = 1 :=
  FormallyRealField.mul_inv_cancel (1 + 1) two_ne_zero_field

theorem half_mul_two_field : halfField F * (1 + 1 : F) = 1 :=
  inv_mul_cancel_field two_ne_zero_field

theorem half_add_half_field : halfField F + halfField F = (1 : F) := by
  have h : halfField F * (1 + 1 : F) = halfField F + halfField F := by
    rw [AssocRing.left_distrib, AssocRing.mul_one]
  rw [← h]
  exact half_mul_two_field

theorem half_ne_zero_field : halfField F ≠ 0 := by
  intro h0
  have h1 : (1 + 1 : F) * halfField F = 0 := by
    rw [h0, mul_zero_ring]
  rw [two_mul_half_field] at h1
  exact one_ne_zero_field h1

theorem neg_one_ne_one_field : (-1 : F) ≠ 1 := by
  intro h
  have h2 : (1 + 1 : F) = 0 := by
    have h' : (-1 : F) + 1 = 1 + 1 := congrArg (fun x => x + 1) h
    rw [AssocRing.neg_add_cancel] at h'
    exact h'.symm
  exact two_ne_zero_field h2

theorem linear_pair_eq_zero {u v : F} (hsum : u + v = 0) (hdiff : u - v = 0) :
    u = 0 ∧ v = 0 := by
  have h1 : (u + v) + (u - v) = 0 := by rw [hsum, hdiff, AssocRing.add_zero]
  have h2 : (u + v) + (u - v) = (1 + 1) * u := by
    rw [AssocRing.sub_eq_add_neg,
        AssocRing.add_assoc u v (u + -v),
        ← AssocRing.add_assoc v u (-v),
        AssocRing.add_comm v u,
        AssocRing.add_assoc u v (-v),
        add_neg_cancel_right_ring,
        AssocRing.add_zero,
        AssocRing.right_distrib,
        AssocRing.one_mul]
  rw [h2] at h1
  cases mul_eq_zero_field h1 with
  | inl ht => exact False.elim (two_ne_zero_field ht)
  | inr hu =>
    refine ⟨hu, ?_⟩
    rw [hu, AssocRing.zero_add] at hsum
    exact hsum

end FieldLemmas

/-! ### Constructive Realization of `FormallyRealField`: Exact Rational Field `RatField` -/

/-- Strictly positive integers, serving as denominators of formal fractions. -/
abbrev PosInt : Type := { d : Int // 0 < d }

/-- Raw numerator/denominator pairs representing n / d. -/
structure RawRat where
  num : Int
  den : PosInt

/-- Cross-multiplication equivalence on raw fractions. -/
def RawRat.Equiv (p q : RawRat) : Prop :=
  p.num * q.den.val = q.num * p.den.val

theorem RawRat.equiv_refl (p : RawRat) : RawRat.Equiv p p := rfl

theorem RawRat.equiv_symm {p q : RawRat} (h : RawRat.Equiv p q) : RawRat.Equiv q p := h.symm

theorem RawRat.equiv_trans {p q r : RawRat}
    (hpq : RawRat.Equiv p q) (hqr : RawRat.Equiv q r) : RawRat.Equiv p r := by
  unfold RawRat.Equiv at *
  have h1 : p.num * r.den.val * q.den.val = r.num * p.den.val * q.den.val := by
    calc
      p.num * r.den.val * q.den.val
          = (p.num * q.den.val) * r.den.val := by
            rw [Int.mul_assoc, Int.mul_comm r.den.val q.den.val, ← Int.mul_assoc]
      _ = (q.num * p.den.val) * r.den.val := by rw [hpq]
      _ = (q.num * r.den.val) * p.den.val := by
            rw [Int.mul_assoc, Int.mul_comm p.den.val r.den.val, ← Int.mul_assoc]
      _ = (r.num * q.den.val) * p.den.val := by rw [hqr]
      _ = r.num * p.den.val * q.den.val := by
            rw [Int.mul_assoc, Int.mul_comm q.den.val p.den.val, ← Int.mul_assoc]
  have hq0 : q.den.val ≠ 0 := by
    have hpos := q.den.property
    omega
  exact Int.eq_of_mul_eq_mul_right hq0 h1

instance RawRat.instSetoid : Setoid RawRat where
  r := RawRat.Equiv
  iseqv := ⟨RawRat.equiv_refl, RawRat.equiv_symm, RawRat.equiv_trans⟩

/-- The exact field ℚ of rational numbers. -/
abbrev RatField : Type := Quotient RawRat.instSetoid

namespace RatField

def mkRat (n : Int) (d : PosInt) : RatField :=
  Quotient.mk RawRat.instSetoid ⟨n, d⟩

def ofInt (n : Int) : RatField :=
  mkRat n ⟨1, by omega⟩

def rawAdd (p q : RawRat) : RawRat :=
  ⟨p.num * q.den.val + q.num * p.den.val,
   ⟨p.den.val * q.den.val, Int.mul_pos p.den.property q.den.property⟩⟩

def rawNeg (p : RawRat) : RawRat :=
  ⟨-p.num, p.den⟩

def rawMul (p q : RawRat) : RawRat :=
  ⟨p.num * q.num,
   ⟨p.den.val * q.den.val, Int.mul_pos p.den.property q.den.property⟩⟩

def rawInv (p : RawRat) : RawRat :=
  if hpos : 0 < p.num then
    ⟨p.den.val, ⟨p.num, hpos⟩⟩
  else if _hneg : p.num < 0 then
    ⟨-p.den.val, ⟨-p.num, by omega⟩⟩
  else
    ⟨0, ⟨1, by omega⟩⟩

private theorem int_ring_add_wd (pn pd qn qd p'n p'd q'n q'd : Int)
    (hp : pn * p'd = p'n * pd) (hq : qn * q'd = q'n * qd) :
    (pn * qd + qn * pd) * (p'd * q'd) = (p'n * q'd + q'n * p'd) * (pd * qd) := by
  have t1 : pn * qd * (p'd * q'd) = p'n * q'd * (pd * qd) := by
    calc
      pn * qd * (p'd * q'd) = (pn * p'd) * (qd * q'd) := by
        rw [Int.mul_assoc pn qd (p'd * q'd), ← Int.mul_assoc qd p'd q'd,
            Int.mul_comm qd p'd, Int.mul_assoc p'd qd q'd, ← Int.mul_assoc]
      _ = (p'n * pd) * (q'd * qd) := by rw [hp, Int.mul_comm qd q'd]
      _ = p'n * q'd * (pd * qd) := by
        rw [Int.mul_assoc p'n pd (q'd * qd), ← Int.mul_assoc pd q'd qd,
            Int.mul_comm pd q'd, Int.mul_assoc q'd pd qd, ← Int.mul_assoc]
  have t2 : qn * pd * (p'd * q'd) = q'n * p'd * (pd * qd) := by
    calc
      qn * pd * (p'd * q'd) = (qn * q'd) * (pd * p'd) := by
        rw [Int.mul_assoc qn pd (p'd * q'd), Int.mul_comm p'd q'd,
            ← Int.mul_assoc pd q'd p'd, Int.mul_comm pd q'd,
            Int.mul_assoc q'd pd p'd, ← Int.mul_assoc]
      _ = (q'n * qd) * (p'd * pd) := by rw [hq, Int.mul_comm pd p'd]
      _ = q'n * p'd * (pd * qd) := by
        rw [Int.mul_assoc q'n qd (p'd * pd), ← Int.mul_assoc qd p'd pd,
            Int.mul_comm qd p'd, Int.mul_assoc p'd qd pd,
            Int.mul_comm qd pd, ← Int.mul_assoc]
  rw [Int.add_mul, Int.add_mul, t1, t2]

def add : RatField → RatField → RatField :=
  Quotient.lift₂ (fun p q => Quotient.mk _ (rawAdd p q)) (by
    intro p q p' q' hp hq
    apply Quotient.sound
    exact int_ring_add_wd p.num p.den.val q.num q.den.val p'.num p'.den.val q'.num q'.den.val hp hq)

def neg : RatField → RatField :=
  Quotient.lift (fun p => Quotient.mk _ (rawNeg p)) (by
    intro p p' hp
    apply Quotient.sound
    show (-p.num) * p'.den.val = (-p'.num) * p.den.val
    rw [Int.neg_mul, Int.neg_mul, hp])

def mul : RatField → RatField → RatField :=
  Quotient.lift₂ (fun p q => Quotient.mk _ (rawMul p q)) (by
    intro p q p' q' hp hq
    apply Quotient.sound
    show (p.num * q.num) * (p'.den.val * q'.den.val) = (p'.num * q'.num) * (p.den.val * q.den.val)
    calc
      (p.num * q.num) * (p'.den.val * q'.den.val)
          = (p.num * p'.den.val) * (q.num * q'.den.val) := by
            rw [Int.mul_assoc p.num q.num _, ← Int.mul_assoc q.num p'.den.val q'.den.val,
                Int.mul_comm q.num p'.den.val, Int.mul_assoc p'.den.val q.num q'.den.val,
                ← Int.mul_assoc]
      _ = (p'.num * p.den.val) * (q'.num * q.den.val) := by rw [hp, hq]
      _ = (p'.num * q'.num) * (p.den.val * q.den.val) := by
            rw [Int.mul_assoc p'.num p.den.val _, ← Int.mul_assoc p.den.val q'.num q.den.val,
                Int.mul_comm p.den.val q'.num, Int.mul_assoc q'.num p.den.val q.den.val,
                ← Int.mul_assoc])

def inv : RatField → RatField :=
  Quotient.lift (fun p => Quotient.mk _ (rawInv p)) (by
    intro p q hpq
    change RawRat.Equiv p q at hpq
    apply Quotient.sound
    change RawRat.Equiv (rawInv p) (rawInv q)
    unfold rawInv RawRat.Equiv at *
    have hp_d : 0 < p.den.val := p.den.property
    have hq_d : 0 < q.den.val := q.den.property
    split
    · next hp_pos =>
      have hprod : 0 < p.num * q.den.val := Int.mul_pos hp_pos hq_d
      rw [hpq] at hprod
      have hq_pos : 0 < q.num := by
        cases Int.lt_trichotomy 0 q.num with
        | inl h => exact h
        | inr h =>
          cases h with
          | inl h0 => rw [← h0, Int.zero_mul] at hprod; omega
          | inr hneg =>
            have hc : q.num * p.den.val < 0 := Int.mul_neg_of_neg_of_pos hneg hp_d
            omega
      rw [dif_pos hq_pos]
      show p.den.val * q.num = q.den.val * p.num
      rw [Int.mul_comm p.den.val q.num, Int.mul_comm q.den.val p.num]
      exact hpq.symm
    · next hp_not_pos =>
      split
      · next hp_neg =>
        have hprod : p.num * q.den.val < 0 := Int.mul_neg_of_neg_of_pos hp_neg hq_d
        rw [hpq] at hprod
        have hq_neg : q.num < 0 := by
          cases Int.lt_trichotomy q.num 0 with
          | inl h => exact h
          | inr h =>
            cases h with
            | inl h0 => rw [h0, Int.zero_mul] at hprod; omega
            | inr hpos =>
              have hc : 0 < q.num * p.den.val := Int.mul_pos hpos hp_d
              omega
        have hq_not_pos : ¬ (0 < q.num) := by omega
        rw [dif_neg hq_not_pos, dif_pos hq_neg]
        show (-p.den.val) * (-q.num) = (-q.den.val) * (-p.num)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg,
            Int.neg_mul, Int.mul_neg, Int.neg_neg,
            Int.mul_comm p.den.val q.num, Int.mul_comm q.den.val p.num]
        exact hpq.symm
      · next hp_not_neg =>
        have hp0 : p.num = 0 := by omega
        rw [hp0, Int.zero_mul] at hpq
        have hq0 : q.num = 0 := by
          cases Int.mul_eq_zero.mp hpq.symm with
          | inl h => exact h
          | inr h => omega
        have hq_np : ¬ (0 < q.num) := by omega
        have hq_nn : ¬ (q.num < 0) := by omega
        rw [dif_neg hq_np, dif_neg hq_nn])

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases Int.le_total 0 a with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have h' : 0 ≤ -a := by omega
    have hmul : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← hmul]
    exact Int.mul_nonneg h' h'

instance : AssocRing RatField where
  zero := ofInt 0
  ofNat := ofInt 1
  add := add
  neg := neg
  sub := fun a b => add a (neg b)
  mul := mul
  add_assoc := fun a b c => by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    show ((p.num * q.den.val + q.num * p.den.val) * r.den.val + r.num * (p.den.val * q.den.val)) *
           (p.den.val * (q.den.val * r.den.val)) =
         (p.num * (q.den.val * r.den.val) + (q.num * r.den.val + r.num * q.den.val) * p.den.val) *
           (p.den.val * q.den.val * r.den.val)
    rw [Int.mul_assoc p.den.val q.den.val r.den.val]
    apply congrArg (fun x => x * (p.den.val * (q.den.val * r.den.val)))
    rw [Int.add_mul, Int.add_mul,
        Int.mul_assoc p.num q.den.val r.den.val,
        Int.mul_assoc q.num p.den.val r.den.val,
        Int.mul_comm p.den.val r.den.val,
        ← Int.mul_assoc q.num r.den.val p.den.val,
        ← Int.mul_assoc r.num p.den.val q.den.val,
        Int.mul_assoc r.num p.den.val q.den.val,
        Int.mul_comm p.den.val q.den.val,
        ← Int.mul_assoc r.num q.den.val p.den.val,
        Int.add_assoc]
  add_comm := fun a b => by
    refine Quotient.inductionOn₂ a b (fun p q => Quotient.sound ?_)
    show (p.num * q.den.val + q.num * p.den.val) * (q.den.val * p.den.val) =
         (q.num * p.den.val + p.num * q.den.val) * (p.den.val * q.den.val)
    rw [Int.add_comm (p.num * q.den.val) _, Int.mul_comm q.den.val p.den.val]
  zero_add := fun a => by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    show (0 * p.den.val + p.num * 1) * p.den.val = p.num * (1 * p.den.val)
    rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
  add_zero := fun a => by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    show (p.num * 1 + 0 * p.den.val) * p.den.val = p.num * (p.den.val * 1)
    rw [Int.mul_one, Int.zero_mul, Int.add_zero, Int.mul_one]
  neg_add_cancel := fun a => by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    show ((-p.num) * p.den.val + p.num * p.den.val) * 1 = 0 * (p.den.val * p.den.val)
    rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul]
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := fun a b c => by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    show p.num * q.num * r.num * (p.den.val * (q.den.val * r.den.val)) =
         p.num * (q.num * r.num) * (p.den.val * q.den.val * r.den.val)
    rw [Int.mul_assoc p.num q.num r.num, Int.mul_assoc p.den.val q.den.val r.den.val]
  one_mul := fun a => by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    show 1 * p.num * p.den.val = p.num * (1 * p.den.val)
    rw [Int.one_mul, Int.one_mul]
  mul_one := fun a => by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    show p.num * 1 * p.den.val = p.num * (p.den.val * 1)
    rw [Int.mul_one, Int.mul_one]
  left_distrib := fun a b c => by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    show p.num * (q.num * r.den.val + r.num * q.den.val) *
           (p.den.val * q.den.val * (p.den.val * r.den.val)) =
         (p.num * q.num * (p.den.val * r.den.val) + p.num * r.num * (p.den.val * q.den.val)) *
           (p.den.val * (q.den.val * r.den.val))
    have hden : p.den.val * q.den.val * (p.den.val * r.den.val) =
                p.den.val * (p.den.val * (q.den.val * r.den.val)) := by
      calc
        p.den.val * q.den.val * (p.den.val * r.den.val)
            = p.den.val * (q.den.val * (p.den.val * r.den.val)) :=
              Int.mul_assoc p.den.val q.den.val _
        _ = p.den.val * ((q.den.val * p.den.val) * r.den.val) := by
              rw [← Int.mul_assoc q.den.val p.den.val r.den.val]
        _ = p.den.val * ((p.den.val * q.den.val) * r.den.val) := by
              rw [Int.mul_comm q.den.val p.den.val]
        _ = p.den.val * (p.den.val * (q.den.val * r.den.val)) := by
              rw [Int.mul_assoc p.den.val q.den.val r.den.val]
    rw [hden, ← Int.mul_assoc _ p.den.val (p.den.val * (q.den.val * r.den.val))]
    apply congrArg (fun x => x * (p.den.val * (q.den.val * r.den.val)))
    rw [Int.mul_add, Int.add_mul,
        ← Int.mul_assoc p.num q.num r.den.val,
        Int.mul_assoc (p.num * q.num) r.den.val p.den.val,
        Int.mul_comm r.den.val p.den.val,
        ← Int.mul_assoc p.num r.num q.den.val,
        Int.mul_assoc (p.num * r.num) q.den.val p.den.val,
        Int.mul_comm q.den.val p.den.val]
  right_distrib := fun a b c => by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    show (p.num * q.den.val + q.num * p.den.val) * r.num *
           (p.den.val * r.den.val * (q.den.val * r.den.val)) =
         (p.num * r.num * (q.den.val * r.den.val) + q.num * r.num * (p.den.val * r.den.val)) *
           (p.den.val * q.den.val * r.den.val)
    have hden : p.den.val * r.den.val * (q.den.val * r.den.val) =
                r.den.val * (p.den.val * q.den.val * r.den.val) := by
      rw [Int.mul_assoc p.den.val r.den.val (q.den.val * r.den.val),
          ← Int.mul_assoc r.den.val q.den.val r.den.val,
          Int.mul_comm r.den.val q.den.val,
          Int.mul_assoc q.den.val r.den.val r.den.val,
          ← Int.mul_assoc p.den.val q.den.val (r.den.val * r.den.val),
          ← Int.mul_assoc (p.den.val * q.den.val) r.den.val r.den.val,
          Int.mul_comm (p.den.val * q.den.val * r.den.val) r.den.val]
    rw [hden, ← Int.mul_assoc _ r.den.val (p.den.val * q.den.val * r.den.val)]
    apply congrArg (fun x => x * (p.den.val * q.den.val * r.den.val))
    rw [Int.add_mul, Int.add_mul,
        Int.mul_assoc p.num q.den.val r.num, Int.mul_comm q.den.val r.num,
        ← Int.mul_assoc p.num r.num q.den.val, Int.mul_assoc (p.num * r.num) q.den.val r.den.val,
        Int.mul_assoc q.num p.den.val r.num, Int.mul_comm p.den.val r.num,
        ← Int.mul_assoc q.num r.num p.den.val, Int.mul_assoc (q.num * r.num) p.den.val r.den.val]

theorem raw_eq_zero_iff (p : RawRat) :
    (Quotient.mk RawRat.instSetoid p : RatField) = 0 ↔ p.num = 0 := by
  constructor
  · intro h
    have heq := Quotient.exact (s := RawRat.instSetoid) h
    change RawRat.Equiv p ⟨0, ⟨1, by omega⟩⟩ at heq
    unfold RawRat.Equiv at heq
    rw [Int.mul_one, Int.zero_mul] at heq
    exact heq
  · intro h
    apply Quotient.sound
    show p.num * 1 = 0 * p.den.val
    rw [h, Int.zero_mul, Int.zero_mul]

instance : FormallyRealField RatField where
  inv := inv
  mul_comm := fun a b => by
    refine Quotient.inductionOn₂ a b (fun p q => Quotient.sound ?_)
    show p.num * q.num * (q.den.val * p.den.val) = q.num * p.num * (p.den.val * q.den.val)
    rw [Int.mul_comm p.num q.num, Int.mul_comm q.den.val p.den.val]
  zero_ne_one := by
    intro h
    have heq := Quotient.exact (s := RawRat.instSetoid) h
    change (0 : Int) * 1 = 1 * 1 at heq
    omega
  mul_inv_cancel := fun a ha => by
    refine Quotient.inductionOn a (fun p hp0 => ?_) ha
    have hnum0 : p.num ≠ 0 := fun hn => hp0 ((raw_eq_zero_iff p).mpr hn)
    apply Quotient.sound
    change RawRat.Equiv (rawMul p (rawInv p)) ⟨1, ⟨1, by omega⟩⟩
    unfold rawMul rawInv RawRat.Equiv
    split
    · next hpos =>
      show p.num * p.den.val * 1 = 1 * (p.den.val * p.num)
      rw [Int.mul_one, Int.one_mul, Int.mul_comm]
    · next hnot_pos =>
      have hneg : p.num < 0 := by omega
      rw [dif_pos hneg]
      show p.num * (-p.den.val) * 1 = 1 * (p.den.val * (-p.num))
      rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm]
  inv_zero := by
    apply Quotient.sound
    change RawRat.Equiv (rawInv ⟨0, ⟨1, by omega⟩⟩) ⟨0, ⟨1, by omega⟩⟩
    unfold rawInv RawRat.Equiv
    have hnp : ¬ (0 < (0 : Int)) := by omega
    have hnn : ¬ ((0 : Int) < 0) := by omega
    simp [hnp, hnn]
  sum_four_sq_eq_zero := fun a b c d => by
    refine Quotient.inductionOn₂ a b (fun pa pb =>
      Quotient.inductionOn₂ c d (fun pc pd h => ?_))
    change Quotient.mk RawRat.instSetoid
      (rawAdd (rawAdd (rawAdd (rawMul pa pa) (rawMul pb pb)) (rawMul pc pc)) (rawMul pd pd)) = 0 at h
    rw [raw_eq_zero_iff] at h
    let da := pa.den.val
    let db := pb.den.val
    let dc := pc.den.val
    let dd := pd.den.val
    have hda : 0 < da := pa.den.property
    have hdb : 0 < db := pb.den.property
    have hdc : 0 < dc := pc.den.property
    have hdd : 0 < dd := pd.den.property
    change (((pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) +
             pc.num * pc.num * (da * da * (db * db))) * (dd * dd) +
            pd.num * pd.num * (da * da * (db * db) * (dc * dc))) = 0 at h
    have s1 : 0 ≤ pa.num * pa.num := int_sq_nonneg pa.num
    have s2 : 0 ≤ pb.num * pb.num := int_sq_nonneg pb.num
    have s3 : 0 ≤ pc.num * pc.num := int_sq_nonneg pc.num
    have s4 : 0 ≤ pd.num * pd.num := int_sq_nonneg pd.num
    have p_da2 : 0 < da * da := Int.mul_pos hda hda
    have p_db2 : 0 < db * db := Int.mul_pos hdb hdb
    have p_dc2 : 0 < dc := hdc
    have p_dc2' : 0 < dc * dc := Int.mul_pos p_dc2 p_dc2
    have p_dd2 : 0 < dd * dd := Int.mul_pos hdd hdd
    have p_ab : 0 < da * da * (db * db) := Int.mul_pos p_da2 p_db2
    have p_abc : 0 < da * da * (db * db) * (dc * dc) := Int.mul_pos p_ab p_dc2'
    have t1 : 0 ≤ pa.num * pa.num * (db * db) := Int.mul_nonneg s1 (Int.le_of_lt p_db2)
    have t2 : 0 ≤ pb.num * pb.num * (da * da) := Int.mul_nonneg s2 (Int.le_of_lt p_da2)
    have t12 : 0 ≤ (pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) :=
      Int.mul_nonneg (Int.add_nonneg t1 t2) (Int.le_of_lt p_dc2')
    have t3 : 0 ≤ pc.num * pc.num * (da * da * (db * db)) :=
      Int.mul_nonneg s3 (Int.le_of_lt p_ab)
    have t123 : 0 ≤ ((pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) +
                     pc.num * pc.num * (da * da * (db * db))) * (dd * dd) :=
      Int.mul_nonneg (Int.add_nonneg t12 t3) (Int.le_of_lt p_dd2)
    have t4 : 0 ≤ pd.num * pd.num * (da * da * (db * db) * (dc * dc)) :=
      Int.mul_nonneg s4 (Int.le_of_lt p_abc)
    have hz4 : pd.num * pd.num * (da * da * (db * db) * (dc * dc)) = 0 := by omega
    have hz123 : ((pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) +
                  pc.num * pc.num * (da * da * (db * db))) * (dd * dd) = 0 := by omega
    have hz123' : (pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) +
                  pc.num * pc.num * (da * da * (db * db)) = 0 := by
      cases Int.mul_eq_zero.mp hz123 with
      | inl h0 => exact h0
      | inr h0 => omega
    have hz3 : pc.num * pc.num * (da * da * (db * db)) = 0 := by omega
    have hz12 : (pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da)) * (dc * dc) = 0 := by
      omega
    have hz12' : pa.num * pa.num * (db * db) + pb.num * pb.num * (da * da) = 0 := by
      cases Int.mul_eq_zero.mp hz12 with
      | inl h0 => exact h0
      | inr h0 => omega
    have hz1 : pa.num * pa.num * (db * db) = 0 := by omega
    have hz2 : pb.num * pb.num * (da * da) = 0 := by omega
    have na : pa.num = 0 := by
      cases Int.mul_eq_zero.mp hz1 with
      | inl h0 => exact (Int.mul_eq_zero.mp h0).elim id id
      | inr h0 => omega
    have nb : pb.num = 0 := by
      cases Int.mul_eq_zero.mp hz2 with
      | inl h0 => exact (Int.mul_eq_zero.mp h0).elim id id
      | inr h0 => omega
    have nc : pc.num = 0 := by
      cases Int.mul_eq_zero.mp hz3 with
      | inl h0 => exact (Int.mul_eq_zero.mp h0).elim id id
      | inr h0 => omega
    have nd : pd.num = 0 := by
      cases Int.mul_eq_zero.mp hz4 with
      | inl h0 => exact (Int.mul_eq_zero.mp h0).elim id id
      | inr h0 => omega
    exact ⟨(raw_eq_zero_iff pa).mpr na, (raw_eq_zero_iff pb).mpr nb,
           (raw_eq_zero_iff pc).mpr nc, (raw_eq_zero_iff pd).mpr nd⟩

end RatField

end Conjecture00000007620
