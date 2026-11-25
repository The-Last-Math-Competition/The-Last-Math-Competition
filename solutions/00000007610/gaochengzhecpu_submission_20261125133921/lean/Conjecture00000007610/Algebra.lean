/-
  Conjecture 00000007610 — Foundational Ring, Field, Algebra, and Center Theory
  Pure Lean 4.19.0 core (zero external dependencies).
-/

namespace Conjecture00000007610

universe u v w z

/-- Multiplicative unit typeclass supporting numeral `1`. -/
class One (α : Type u) where
  one : α

instance oneOfNat {α : Type u} [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

/-- Additive commutative group structure. -/
class AddCommGrp (G : Type u) extends Zero G, Add G, Neg G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : G, a + b = b + a
  zero_add : ∀ a : G, 0 + a = a
  neg_add_cancel : ∀ a : G, -a + a = 0

section AddCommGrpLemmas

variable {G : Type u} [AddCommGrp G]

theorem add_zero_grp (a : G) : a + 0 = a := by
  rw [AddCommGrp.add_comm, AddCommGrp.zero_add]

theorem add_neg_cancel_grp (a : G) : a + -a = 0 := by
  rw [AddCommGrp.add_comm, AddCommGrp.neg_add_cancel]

theorem add_left_cancel_grp {a b c : G} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← AddCommGrp.add_assoc, ← AddCommGrp.add_assoc, AddCommGrp.neg_add_cancel,
      AddCommGrp.zero_add, AddCommGrp.zero_add] at h1
  exact h1

theorem add_right_cancel_grp {a b c : G} (h : b + a = c + a) : b = c := by
  apply add_left_cancel_grp (a := a)
  rw [AddCommGrp.add_comm a b, AddCommGrp.add_comm a c]
  exact h

theorem neg_eq_of_add_eq_zero {a b : G} (h : a + b = 0) : -a = b := by
  apply add_left_cancel_grp (a := a)
  rw [add_neg_cancel_grp, h]

theorem neg_zero_grp : -(0 : G) = 0 :=
  neg_eq_of_add_eq_zero (AddCommGrp.zero_add (0 : G))

theorem neg_neg_grp (a : G) : -(-a) = a := by
  exact neg_eq_of_add_eq_zero (AddCommGrp.neg_add_cancel a)

theorem neg_add_grp (a b : G) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + (-a + -b) = b + a + (-a + -b) := by rw [AddCommGrp.add_comm a b]
    _ = b + (a + (-a + -b)) := by rw [AddCommGrp.add_assoc]
    _ = b + ((a + -a) + -b) := by rw [← AddCommGrp.add_assoc a (-a) (-b)]
    _ = b + (0 + -b) := by rw [add_neg_cancel_grp]
    _ = b + -b := by rw [AddCommGrp.zero_add]
    _ = 0 := by rw [add_neg_cancel_grp]

instance : Sub G where
  sub a b := a + -b

theorem sub_def_grp (a b : G) : a - b = a + -b := rfl

theorem sub_self_grp (a : G) : a - a = 0 := add_neg_cancel_grp a

end AddCommGrpLemmas

/-- Associative unital ring (not necessarily commutative). -/
class UnitalRing (R : Type u) extends AddCommGrp R, One R, Mul R where
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

section RingLemmas

variable {R : Type u} [UnitalRing R]

theorem mul_zero_ring (a : R) : a * 0 = 0 := by
  apply add_left_cancel_grp (a := a * 0)
  calc
    a * 0 + a * 0 = a * (0 + 0) := by rw [← UnitalRing.left_distrib]
    _ = a * 0 := by rw [AddCommGrp.zero_add]
    _ = a * 0 + 0 := by rw [add_zero_grp]

theorem zero_mul_ring (a : R) : 0 * a = 0 := by
  apply add_left_cancel_grp (a := 0 * a)
  calc
    0 * a + 0 * a = (0 + 0) * a := by rw [← UnitalRing.right_distrib]
    _ = 0 * a := by rw [AddCommGrp.zero_add]
    _ = 0 * a + 0 := by rw [add_zero_grp]

theorem mul_neg_ring (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← UnitalRing.left_distrib, add_neg_cancel_grp, mul_zero_ring]

theorem neg_mul_ring (a b : R) : (-a) * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← UnitalRing.right_distrib, add_neg_cancel_grp, zero_mul_ring]

theorem neg_mul_neg_ring (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul_ring, mul_neg_ring, neg_neg_grp]

end RingLemmas

/-- Commutative field with total inverse function (inv 0 = 0). -/
class FieldStructure (K : Type u) extends UnitalRing K where
  inv : K → K
  mul_comm : ∀ a b : K, a * b = b * a
  zero_ne_one : (0 : K) ≠ 1
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * inv a = 1
  inv_zero : inv 0 = 0

section FieldLemmas

variable {K : Type u} [FieldStructure K]

theorem one_ne_zero_field : (1 : K) ≠ 0 :=
  fun h => FieldStructure.zero_ne_one h.symm

theorem inv_mul_cancel_field {a : K} (ha : a ≠ 0) : FieldStructure.inv a * a = 1 := by
  rw [FieldStructure.mul_comm, FieldStructure.mul_inv_cancel a ha]

theorem mul_eq_zero_field {a b : K} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · apply Or.inr
    calc
      b = 1 * b := by rw [UnitalRing.one_mul]
      _ = (FieldStructure.inv a * a) * b := by rw [inv_mul_cancel_field ha]
      _ = FieldStructure.inv a * (a * b) := by rw [UnitalRing.mul_assoc]
      _ = FieldStructure.inv a * 0 := by rw [h]
      _ = 0 := by rw [mul_zero_ring]

theorem mul_ne_zero_field {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  cases mul_eq_zero_field h with
  | inl h1 => exact ha h1
  | inr h2 => exact hb h2

theorem inv_ne_zero_field {a : K} (ha : a ≠ 0) : FieldStructure.inv a ≠ 0 := by
  intro hinv
  have h1 : a * FieldStructure.inv a = 1 := FieldStructure.mul_inv_cancel a ha
  rw [hinv, mul_zero_ring] at h1
  exact FieldStructure.zero_ne_one h1

end FieldLemmas

/-- Unital ring homomorphism. -/
structure RingHom (R : Type u) (S : Type v) [UnitalRing R] [UnitalRing S] where
  toFun : R → S
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ x y : R, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y : R, toFun (x * y) = toFun x * toFun y

theorem RingHom.map_neg {R : Type u} {S : Type v} [UnitalRing R] [UnitalRing S]
    (f : RingHom R S) (x : R) : f.toFun (-x) = -(f.toFun x) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← f.map_add, add_neg_cancel_grp, f.map_zero]

def RingHom.id (R : Type u) [UnitalRing R] : RingHom R R where
  toFun x := x
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def RingHom.comp {R : Type u} {S : Type v} {T : Type w}
    [UnitalRing R] [UnitalRing S] [UnitalRing T]
    (g : RingHom S T) (f : RingHom R S) : RingHom R T where
  toFun x := g.toFun (f.toFun x)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_one := by rw [f.map_one, g.map_one]
  map_add x y := by rw [f.map_add, g.map_add]
  map_mul x y := by rw [f.map_mul, g.map_mul]

/-- Bijective unital ring isomorphism. -/
structure RingIso (R : Type u) (S : Type v) [UnitalRing R] [UnitalRing S]
    extends RingHom R S where
  invFun : S → R
  left_inv : ∀ x : R, invFun (toFun x) = x
  right_inv : ∀ y : S, toFun (invFun y) = y

def RingIso.refl (R : Type u) [UnitalRing R] : RingIso R R where
  toFun x := x
  invFun x := x
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def RingIso.symm {R : Type u} {S : Type v} [UnitalRing R] [UnitalRing S]
    (e : RingIso R S) : RingIso S R where
  toFun := e.invFun
  invFun := e.toFun
  map_zero := by
    calc
      e.invFun 0 = e.invFun (e.toFun 0) := by rw [e.map_zero]
      _ = 0 := e.left_inv 0
  map_one := by
    calc
      e.invFun 1 = e.invFun (e.toFun 1) := by rw [e.map_one]
      _ = 1 := e.left_inv 1
  map_add x y := by
    calc
      e.invFun (x + y) = e.invFun (e.toFun (e.invFun x) + e.toFun (e.invFun y)) := by
        rw [e.right_inv x, e.right_inv y]
      _ = e.invFun (e.toFun (e.invFun x + e.invFun y)) := by rw [← e.map_add]
      _ = e.invFun x + e.invFun y := e.left_inv _
  map_mul x y := by
    calc
      e.invFun (x * y) = e.invFun (e.toFun (e.invFun x) * e.toFun (e.invFun y)) := by
        rw [e.right_inv x, e.right_inv y]
      _ = e.invFun (e.toFun (e.invFun x * e.invFun y)) := by rw [← e.map_mul]
      _ = e.invFun x * e.invFun y := e.left_inv _
  left_inv := e.right_inv
  right_inv := e.left_inv

def RingIso.trans {R : Type u} {S : Type v} {T : Type w}
    [UnitalRing R] [UnitalRing S] [UnitalRing T]
    (e1 : RingIso R S) (e2 : RingIso S T) : RingIso R T where
  toRingHom := RingHom.comp e2.toRingHom e1.toRingHom
  invFun z := e1.invFun (e2.invFun z)
  left_inv x := by
    dsimp [RingHom.comp]
    rw [e2.left_inv, e1.left_inv]
  right_inv z := by
    dsimp [RingHom.comp]
    rw [e1.right_inv, e2.right_inv]

/-- Scalar multiplication carrier class without field parameter on projections. -/
class KSMul (K : Type u) (V : Type v) where
  smul : K → V → V

/-- K-vector space structure. -/
class KVectorSpace (K : Type u) [FieldStructure K] (V : Type v)
    extends AddCommGrp V, KSMul K V where
  one_smul : ∀ v : V, smul 1 v = v
  mul_smul : ∀ a b : K, ∀ v : V, smul (a * b) v = smul a (smul b v)
  smul_zero : ∀ a : K, smul a 0 = 0
  smul_add : ∀ a : K, ∀ v w : V, smul a (v + w) = smul a v + smul a w
  add_smul : ∀ a b : K, ∀ v : V, smul (a + b) v = smul a v + smul b v
  zero_smul : ∀ v : V, smul 0 v = 0

theorem smul_neg_vs {K : Type u} [FieldStructure K] {V : Type v} [KVectorSpace K V]
    (a : K) (v : V) : KSMul.smul a (-v) = -(KSMul.smul a v) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← KVectorSpace.smul_add, add_neg_cancel_grp, KVectorSpace.smul_zero]

theorem neg_smul_vs {K : Type u} [FieldStructure K] {V : Type v} [KVectorSpace K V]
    (a : K) (v : V) : KSMul.smul (-a) v = -(KSMul.smul a v) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← KVectorSpace.add_smul, add_neg_cancel_grp, KVectorSpace.zero_smul]

theorem smul_eq_zero_vs {K : Type u} [FieldStructure K] {V : Type v} [KVectorSpace K V]
    {a : K} {v : V} (h : KSMul.smul a v = 0) : a = 0 ∨ v = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · apply Or.inr
    calc
      v = KSMul.smul (1 : K) v := (KVectorSpace.one_smul v).symm
      _ = KSMul.smul (FieldStructure.inv a * a) v := by rw [inv_mul_cancel_field ha]
      _ = KSMul.smul (FieldStructure.inv a) (KSMul.smul a v) := by
        rw [KVectorSpace.mul_smul]
      _ = KSMul.smul (FieldStructure.inv a) 0 := by rw [h]
      _ = 0 := KVectorSpace.smul_zero _

/-- Associative unital K-algebra. -/
class KAlgebra (K : Type u) [FieldStructure K] (A : Type v)
    extends UnitalRing A, KSMul K A where
  one_smul : ∀ x : A, smul 1 x = x
  mul_smul : ∀ a b : K, ∀ x : A, smul (a * b) x = smul a (smul b x)
  smul_zero : ∀ a : K, smul a 0 = 0
  smul_add : ∀ a : K, ∀ x y : A, smul a (x + y) = smul a x + smul a y
  add_smul : ∀ a b : K, ∀ x : A, smul (a + b) x = smul a x + smul b x
  zero_smul : ∀ x : A, smul 0 x = 0
  smul_mul_assoc : ∀ a : K, ∀ x y : A, smul a x * y = smul a (x * y)
  mul_smul_comm : ∀ a : K, ∀ x y : A, x * smul a y = smul a (x * y)

instance algebraToVectorSpace (K : Type u) [FieldStructure K] (A : Type v) [KAlgebra K A] :
    KVectorSpace K A where
  smul := KSMul.smul
  one_smul := KAlgebra.one_smul
  mul_smul := KAlgebra.mul_smul
  smul_zero := KAlgebra.smul_zero
  smul_add := KAlgebra.smul_add
  add_smul := KAlgebra.add_smul
  zero_smul := KAlgebra.zero_smul

/-- Every field K is canonically a K-algebra over itself. -/
instance selfKAlgebra (K : Type u) [FieldStructure K] : KAlgebra K K where
  smul a x := a * x
  one_smul := UnitalRing.one_mul
  mul_smul := UnitalRing.mul_assoc
  smul_zero := mul_zero_ring
  smul_add := UnitalRing.left_distrib
  add_smul := UnitalRing.right_distrib
  zero_smul := zero_mul_ring
  smul_mul_assoc := UnitalRing.mul_assoc
  mul_smul_comm a x y := by
    calc
      x * (a * y) = (x * a) * y := (UnitalRing.mul_assoc x a y).symm
      _ = (a * x) * y := by rw [FieldStructure.mul_comm x a]
      _ = a * (x * y) := UnitalRing.mul_assoc a x y

/-- Canonical scalar embedding c ↦ c • 1_A. -/
def algebraMap (K : Type u) [FieldStructure K] {A : Type v} [KAlgebra K A] (c : K) : A :=
  KSMul.smul c 1

theorem algebraMap_commutes (K : Type u) [FieldStructure K] {A : Type v} [KAlgebra K A]
    (c : K) (x : A) : algebraMap K c * x = x * algebraMap K c := by
  unfold algebraMap
  rw [KAlgebra.smul_mul_assoc, UnitalRing.one_mul, KAlgebra.mul_smul_comm, UnitalRing.mul_one]

/-- Unital K-algebra homomorphism. -/
structure AlgHom (K : Type u) [FieldStructure K]
    (A : Type v) (B : Type w) [KAlgebra K A] [KAlgebra K B]
    extends RingHom A B where
  map_smul : ∀ c : K, ∀ x : A, toFun (KSMul.smul c x) = KSMul.smul c (toFun x)

/-- Bijective K-algebra isomorphism. -/
structure AlgIso (K : Type u) [FieldStructure K]
    (A : Type v) (B : Type w) [KAlgebra K A] [KAlgebra K B]
    extends AlgHom K A B where
  invFun : B → A
  left_inv : ∀ x : A, invFun (toFun x) = x
  right_inv : ∀ y : B, toFun (invFun y) = y

def AlgIso.toRingIso {K : Type u} [FieldStructure K]
    {A : Type v} {B : Type w} [KAlgebra K A] [KAlgebra K B]
    (e : AlgIso K A B) : RingIso A B where
  toRingHom := e.toRingHom
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv

def AlgIso.refl (K : Type u) [FieldStructure K] (A : Type v) [KAlgebra K A] : AlgIso K A A where
  toFun x := x
  invFun x := x
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_smul _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def AlgIso.symm {K : Type u} [FieldStructure K]
    {A : Type v} {B : Type w} [KAlgebra K A] [KAlgebra K B]
    (e : AlgIso K A B) : AlgIso K B A where
  toRingHom := (e.toRingIso.symm).toRingHom
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_smul c y := by
    change e.invFun (KSMul.smul c y) = KSMul.smul c (e.invFun y)
    calc
      e.invFun (KSMul.smul c y)
        = e.invFun (KSMul.smul c (e.toFun (e.invFun y))) := by rw [e.right_inv y]
      _ = e.invFun (e.toFun (KSMul.smul c (e.invFun y))) := by rw [← e.map_smul]
      _ = KSMul.smul c (e.invFun y) := e.left_inv _

def AlgIso.trans {K : Type u} [FieldStructure K]
    {A : Type v} {B : Type w} {C : Type z} [KAlgebra K A] [KAlgebra K B] [KAlgebra K C]
    (e1 : AlgIso K A B) (e2 : AlgIso K B C) : AlgIso K A C where
  toFun x := e2.toFun (e1.toFun x)
  invFun z := e1.invFun (e2.invFun z)
  map_zero := by rw [e1.map_zero, e2.map_zero]
  map_one := by rw [e1.map_one, e2.map_one]
  map_add x y := by rw [e1.map_add, e2.map_add]
  map_mul x y := by rw [e1.map_mul, e2.map_mul]
  left_inv x := by rw [e2.left_inv, e1.left_inv]
  right_inv z := by rw [e1.right_inv, e2.right_inv]
  map_smul c x := by rw [e1.map_smul, e2.map_smul]

/-- K-linear bijection between K-vector spaces. -/
structure KLinearIso (K : Type u) [FieldStructure K]
    (V : Type v) (W : Type w) [KVectorSpace K V] [KVectorSpace K W] where
  toFun : V → W
  invFun : W → V
  map_add : ∀ x y : V, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ c : K, ∀ x : V, toFun (KSMul.smul c x) = KSMul.smul c (toFun x)
  left_inv : ∀ x : V, invFun (toFun x) = x
  right_inv : ∀ y : W, toFun (invFun y) = y

def KLinearIso.refl (K : Type u) [FieldStructure K] (V : Type v) [KVectorSpace K V] :
    KLinearIso K V V where
  toFun x := x
  invFun x := x
  map_add _ _ := rfl
  map_smul _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def KLinearIso.symm {K : Type u} [FieldStructure K]
    {V : Type v} {W : Type w} [KVectorSpace K V] [KVectorSpace K W]
    (e : KLinearIso K V W) : KLinearIso K W V where
  toFun := e.invFun
  invFun := e.toFun
  map_add x y := by
    calc
      e.invFun (x + y) = e.invFun (e.toFun (e.invFun x) + e.toFun (e.invFun y)) := by
        rw [e.right_inv x, e.right_inv y]
      _ = e.invFun (e.toFun (e.invFun x + e.invFun y)) := by rw [← e.map_add]
      _ = e.invFun x + e.invFun y := e.left_inv _
  map_smul c x := by
    calc
      e.invFun (KSMul.smul c x)
        = e.invFun (KSMul.smul c (e.toFun (e.invFun x))) := by rw [e.right_inv x]
      _ = e.invFun (e.toFun (KSMul.smul c (e.invFun x))) := by rw [← e.map_smul]
      _ = KSMul.smul c (e.invFun x) := e.left_inv _
  left_inv := e.right_inv
  right_inv := e.left_inv

def KLinearIso.trans {K : Type u} [FieldStructure K]
    {U : Type u} {V : Type v} {W : Type w}
    [KVectorSpace K U] [KVectorSpace K V] [KVectorSpace K W]
    (e1 : KLinearIso K U V) (e2 : KLinearIso K V W) : KLinearIso K U W where
  toFun x := e2.toFun (e1.toFun x)
  invFun z := e1.invFun (e2.invFun z)
  map_add x y := by rw [e1.map_add, e2.map_add]
  map_smul c x := by rw [e1.map_smul, e2.map_smul]
  left_inv x := by rw [e2.left_inv, e1.left_inv]
  right_inv z := by rw [e1.right_inv, e2.right_inv]

def AlgIso.toKLinearIso {K : Type u} [FieldStructure K]
    {A : Type v} {B : Type w} [KAlgebra K A] [KAlgebra K B]
    (e : AlgIso K A B) : KLinearIso K A B where
  toFun := e.toFun
  invFun := e.invFun
  map_add := e.map_add
  map_smul := e.map_smul
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- Standard coordinate space Fin m → K as a K-vector space. -/
instance finVecSpace (K : Type u) [FieldStructure K] (m : Nat) :
    KVectorSpace K (Fin m → K) where
  zero := fun _ => 0
  add f g := fun i => f i + g i
  neg f := fun i => -(f i)
  add_assoc f g h := funext fun i => AddCommGrp.add_assoc (f i) (g i) (h i)
  add_comm f g := funext fun i => AddCommGrp.add_comm (f i) (g i)
  zero_add f := funext fun i => AddCommGrp.zero_add (f i)
  neg_add_cancel f := funext fun i => AddCommGrp.neg_add_cancel (f i)
  smul c f := fun i => c * f i
  one_smul f := funext fun i => UnitalRing.one_mul (f i)
  mul_smul a b f := funext fun i => UnitalRing.mul_assoc a b (f i)
  smul_zero a := funext fun _ => mul_zero_ring a
  smul_add a f g := funext fun i => UnitalRing.left_distrib a (f i) (g i)
  add_smul a b f := funext fun i => UnitalRing.right_distrib a b (f i)
  zero_smul f := funext fun i => zero_mul_ring (f i)

/-- Genuine K-vector space dimension: V has K-dimension m iff (Fin m → K) ≃ₗ[K] V. -/
def HasKDim (K : Type u) [FieldStructure K] (V : Type v) [KVectorSpace K V] (m : Nat) : Prop :=
  Nonempty (KLinearIso K (Fin m → K) V)

/-- Dimension 1 != Dimension 2 over any field K: ¬ ((Fin 1 → K) ≃ₗ[K] (Fin 2 → K)). -/
theorem not_kLinearIso_fin1_fin2 (K : Type u) [FieldStructure K] :
    ¬ Nonempty (KLinearIso K (Fin 1 → K) (Fin 2 → K)) := by
  intro ⟨e⟩
  let g := e.symm
  let e0 : Fin 2 → K := fun i => if i.val = 0 then 1 else 0
  let e1 : Fin 2 → K := fun i => if i.val = 1 then 1 else 0
  let a : K := g.toFun e0 ⟨0, by omega⟩
  let b : K := g.toFun e1 ⟨0, by omega⟩
  by_cases ha : a = 0
  · have hg0 : g.toFun e0 = (0 : Fin 1 → K) := by
      funext j
      have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hj]
      exact ha
    have he0 : e0 = 0 := by
      calc
        e0 = e.toFun (g.toFun e0) := (e.right_inv e0).symm
        _ = e.toFun (0 : Fin 1 → K) := by rw [hg0]
        _ = e.toFun (KSMul.smul (0 : K) (0 : Fin 1 → K)) := by
          rw [KVectorSpace.zero_smul]
        _ = KSMul.smul (0 : K) (e.toFun 0) := e.map_smul 0 0
        _ = 0 := KVectorSpace.zero_smul _
    have h10 : (1 : K) = 0 := congrFun he0 ⟨0, by omega⟩
    exact one_ne_zero_field h10
  · -- Construct nonzero v = b • e0 - a • e1 in K^2 mapped to 0 in K^1
    let v : Fin 2 → K := KSMul.smul b e0 + -(KSMul.smul a e1)
    have hgv : g.toFun v = 0 := by
      have hneg : g.toFun (-(KSMul.smul a e1)) = -(g.toFun (KSMul.smul a e1)) := by
        calc
          g.toFun (-(KSMul.smul a e1))
            = g.toFun (KSMul.smul (-1 : K) (KSMul.smul a e1)) := by
              rw [neg_smul_vs, KVectorSpace.one_smul]
          _ = KSMul.smul (-1 : K) (g.toFun (KSMul.smul a e1)) := g.map_smul (-1) _
          _ = -(g.toFun (KSMul.smul a e1)) := by rw [neg_smul_vs, KVectorSpace.one_smul]
      funext j
      have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hj]
      have hstep : g.toFun v = KSMul.smul b (g.toFun e0) + -(KSMul.smul a (g.toFun e1)) := by
        unfold v
        rw [g.map_add, g.map_smul, hneg, g.map_smul]
      rw [hstep]
      change b * a + -(a * b) = 0
      rw [FieldStructure.mul_comm b a, add_neg_cancel_grp]
    have hv0 : v = 0 := by
      calc
        v = e.toFun (g.toFun v) := (e.right_inv v).symm
        _ = e.toFun 0 := by rw [hgv]
        _ = e.toFun (KSMul.smul (0 : K) 0) := by rw [KVectorSpace.zero_smul]
        _ = KSMul.smul (0 : K) (e.toFun 0) := e.map_smul 0 0
        _ = 0 := KVectorSpace.zero_smul _
    have hv_at_1 : v ⟨1, by omega⟩ = -a := by
      change b * (0 : K) + -(a * (1 : K)) = -a
      rw [mul_zero_ring, UnitalRing.mul_one, AddCommGrp.zero_add]
    have h0_at_1 : v ⟨1, by omega⟩ = 0 := congrFun hv0 ⟨1, by omega⟩
    rw [hv_at_1] at h0_at_1
    have ha0 : a = 0 := by
      calc
        a = -(-a) := (neg_neg_grp a).symm
        _ = -(0 : K) := by rw [h0_at_1]
        _ = 0 := neg_zero_grp
    exact ha ha0

/-! ### Genuine Ring-Theoretic Center Z(A) -/

/-- An element z ∈ A is central iff it commutes with every element of A. -/
def IsCentral {A : Type u} [UnitalRing A] (z : A) : Prop :=
  ∀ x : A, z * x = x * z

/-- The genuine ring-theoretic center Z(A) = {z ∈ A | ∀ x ∈ A, z * x = x * z}. -/
structure Center (A : Type u) [UnitalRing A] where
  val : A
  property : IsCentral val

theorem Center.ext {A : Type u} [UnitalRing A] {z1 z2 : Center A}
    (h : z1.val = z2.val) : z1 = z2 := by
  cases z1
  cases z2
  cases h
  rfl

instance centerRing (A : Type u) [UnitalRing A] : UnitalRing (Center A) where
  zero := ⟨0, fun x => by rw [zero_mul_ring, mul_zero_ring]⟩
  one := ⟨1, fun x => by rw [UnitalRing.one_mul, UnitalRing.mul_one]⟩
  add z1 z2 := ⟨z1.val + z2.val, fun x => by
    rw [UnitalRing.right_distrib, z1.property x, z2.property x, UnitalRing.left_distrib]⟩
  neg z := ⟨-z.val, fun x => by
    rw [neg_mul_ring, z.property x, mul_neg_ring]⟩
  mul z1 z2 := ⟨z1.val * z2.val, fun x => by
    calc
      (z1.val * z2.val) * x = z1.val * (z2.val * x) := UnitalRing.mul_assoc _ _ _
      _ = z1.val * (x * z2.val) := by rw [z2.property x]
      _ = (z1.val * x) * z2.val := (UnitalRing.mul_assoc _ _ _).symm
      _ = (x * z1.val) * z2.val := by rw [z1.property x]
      _ = x * (z1.val * z2.val) := UnitalRing.mul_assoc _ _ _⟩
  add_assoc z1 z2 z3 := Center.ext (AddCommGrp.add_assoc z1.val z2.val z3.val)
  add_comm z1 z2 := Center.ext (AddCommGrp.add_comm z1.val z2.val)
  zero_add z := Center.ext (AddCommGrp.zero_add z.val)
  neg_add_cancel z := Center.ext (AddCommGrp.neg_add_cancel z.val)
  mul_assoc z1 z2 z3 := Center.ext (UnitalRing.mul_assoc z1.val z2.val z3.val)
  one_mul z := Center.ext (UnitalRing.one_mul z.val)
  mul_one z := Center.ext (UnitalRing.mul_one z.val)
  left_distrib z1 z2 z3 := Center.ext (UnitalRing.left_distrib z1.val z2.val z3.val)
  right_distrib z1 z2 z3 := Center.ext (UnitalRing.right_distrib z1.val z2.val z3.val)

theorem Center.mul_comm {A : Type u} [UnitalRing A] (z1 z2 : Center A) :
    z1 * z2 = z2 * z1 :=
  Center.ext (z1.property z2.val)

instance centerKAlgebra (K : Type u) [FieldStructure K] (A : Type v) [KAlgebra K A] :
    KAlgebra K (Center A) where
  smul c z := ⟨KSMul.smul c z.val, fun x => by
    rw [KAlgebra.smul_mul_assoc, z.property x, KAlgebra.mul_smul_comm]⟩
  one_smul z := Center.ext (KAlgebra.one_smul z.val)
  mul_smul a b z := Center.ext (KAlgebra.mul_smul a b z.val)
  smul_zero a := Center.ext (KAlgebra.smul_zero a)
  smul_add a z1 z2 := Center.ext (KAlgebra.smul_add a z1.val z2.val)
  add_smul a b z := Center.ext (KAlgebra.add_smul a b z.val)
  zero_smul z := Center.ext (KAlgebra.zero_smul z.val)
  smul_mul_assoc a z1 z2 := Center.ext (KAlgebra.smul_mul_assoc a z1.val z2.val)
  mul_smul_comm a z1 z2 := Center.ext (KAlgebra.mul_smul_comm a z1.val z2.val)

/-- Any ring isomorphism A ≃ B induces a ring isomorphism Z(A) ≃ Z(B). -/
def RingIso.centerIso {A : Type u} {B : Type v} [UnitalRing A] [UnitalRing B]
    (e : RingIso A B) : RingIso (Center A) (Center B) where
  toFun z := ⟨e.toFun z.val, fun y => by
    calc
      e.toFun z.val * y = e.toFun z.val * e.toFun (e.invFun y) := by rw [e.right_inv y]
      _ = e.toFun (z.val * e.invFun y) := (e.map_mul _ _).symm
      _ = e.toFun (e.invFun y * z.val) := by rw [z.property (e.invFun y)]
      _ = e.toFun (e.invFun y) * e.toFun z.val := e.map_mul _ _
      _ = y * e.toFun z.val := by rw [e.right_inv y]⟩
  invFun w := ⟨e.invFun w.val, fun x => by
    let es := e.symm
    calc
      es.toFun w.val * x = es.toFun w.val * es.toFun (es.invFun x) := by rw [es.right_inv x]
      _ = es.toFun (w.val * es.invFun x) := (es.map_mul _ _).symm
      _ = es.toFun (es.invFun x * w.val) := by rw [w.property (es.invFun x)]
      _ = es.toFun (es.invFun x) * es.toFun w.val := es.map_mul _ _
      _ = x * es.toFun w.val := by rw [es.right_inv x]⟩
  map_zero := Center.ext e.map_zero
  map_one := Center.ext e.map_one
  map_add z1 z2 := Center.ext (e.map_add z1.val z2.val)
  map_mul z1 z2 := Center.ext (e.map_mul z1.val z2.val)
  left_inv z := Center.ext (e.left_inv z.val)
  right_inv w := Center.ext (e.right_inv w.val)

/-- Any K-algebra isomorphism A ≃ₐ[K] B induces Z(A) ≃ₐ[K] Z(B). -/
def AlgIso.centerIso {K : Type u} [FieldStructure K]
    {A : Type v} {B : Type w} [KAlgebra K A] [KAlgebra K B]
    (e : AlgIso K A B) : AlgIso K (Center A) (Center B) where
  toRingHom := (e.toRingIso.centerIso).toRingHom
  invFun := (e.toRingIso.centerIso).invFun
  left_inv := (e.toRingIso.centerIso).left_inv
  right_inv := (e.toRingIso.centerIso).right_inv
  map_smul c z := Center.ext (e.map_smul c z.val)

/-- If A is commutative, then Z(A) ≃ₐ[K] A canonically. -/
def commCenterAlgIso {K : Type u} [FieldStructure K] (A : Type v) [KAlgebra K A]
    (hcomm : ∀ x y : A, x * y = y * x) : AlgIso K (Center A) A where
  toFun z := z.val
  invFun x := ⟨x, fun y => hcomm x y⟩
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_smul _ _ := rfl
  left_inv _ := Center.ext rfl
  right_inv _ := rfl

end Conjecture00000007610
