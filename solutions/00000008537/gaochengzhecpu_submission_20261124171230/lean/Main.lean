/-!
# Formal Disproof of Conjecture 00000008537

This file formalizes lattices, modular lattices, finite cardinality, lattice
embeddings, division rings, fields, vector spaces, linear dimension bounds, and
subspace lattices from first principles in Core Lean 4.19.0.

We construct an explicit 43-element modular lattice `CounterexampleLattice`
(the ordinal gluing of the 16-element Fano subspace lattice `Sub3 F2` and the
28-element ternary plane subspace lattice `Sub3 F3` at a single shared element),
as well as an infinite family `CounterexampleFamily m` of pairwise non-isomorphic
finite modular lattices of cardinality `43 * (m + 1)`.

We prove that any lattice embedding of `Sub3 F2` into a subspace lattice
`Subspace K V` over a division ring `K` forces `1 + 1 = 0` in `K`, while any
lattice embedding of `Sub3 F3` into `Subspace K V` forces `1 + 1 + 1 = 0` in `K`.
Consequently, `CounterexampleLattice` (and every `CounterexampleFamily m`) possesses
no lattice embedding into the subspace lattice of any vector space over any
field or division ring, of any finite or infinite dimension (and in particular
not of linear dimension at most `|L|`).
-/

namespace Conjecture8537

/-! ## 1. Lattices, Modularity, Finiteness, and Lattice Embeddings -/

class Lattice (L : Type u) where
  le : L → L → Prop
  inf : L → L → L
  sup : L → L → L
  le_refl : ∀ a : L, le a a
  le_trans : ∀ {a b c : L}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b
  inf_le_left : ∀ a b : L, le (inf a b) a
  inf_le_right : ∀ a b : L, le (inf a b) b
  le_inf : ∀ {a b c : L}, le c a → le c b → le c (inf a b)
  le_sup_left : ∀ a b : L, le a (sup a b)
  le_sup_right : ∀ a b : L, le b (sup a b)
  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c

scoped infix:50 " ≼ " => Lattice.le
scoped infixl:70 " ⊓ " => Lattice.inf
scoped infixl:65 " ⊔ " => Lattice.sup

section LatticeLemmas
variable {L : Type u} [Lattice L]

theorem inf_comm (a b : L) : a ⊓ b = b ⊓ a :=
  Lattice.le_antisymm
    (Lattice.le_inf (Lattice.inf_le_right a b) (Lattice.inf_le_left a b))
    (Lattice.le_inf (Lattice.inf_le_right b a) (Lattice.inf_le_left b a))

theorem sup_comm (a b : L) : a ⊔ b = b ⊔ a :=
  Lattice.le_antisymm
    (Lattice.sup_le (Lattice.le_sup_right b a) (Lattice.le_sup_left b a))
    (Lattice.sup_le (Lattice.le_sup_right a b) (Lattice.le_sup_left a b))

theorem inf_idem (a : L) : a ⊓ a = a :=
  Lattice.le_antisymm (Lattice.inf_le_left a a) (Lattice.le_inf (Lattice.le_refl a) (Lattice.le_refl a))

theorem sup_idem (a : L) : a ⊔ a = a :=
  Lattice.le_antisymm (Lattice.sup_le (Lattice.le_refl a) (Lattice.le_refl a)) (Lattice.le_sup_left a a)

theorem inf_eq_left {a b : L} : a ⊓ b = a ↔ a ≼ b := by
  constructor
  · intro h
    rw [← h]
    exact Lattice.inf_le_right a b
  · intro h
    exact Lattice.le_antisymm (Lattice.inf_le_left a b) (Lattice.le_inf (Lattice.le_refl a) h)

theorem sup_eq_right {a b : L} : a ⊔ b = b ↔ a ≼ b := by
  constructor
  · intro h
    rw [← h]
    exact Lattice.le_sup_left a b
  · intro h
    exact Lattice.le_antisymm (Lattice.sup_le h (Lattice.le_refl b)) (Lattice.le_sup_right a b)

theorem inf_sup_self (a b : L) : a ⊓ (a ⊔ b) = a :=
  inf_eq_left.mpr (Lattice.le_sup_left a b)

theorem sup_inf_self (a b : L) : a ⊔ (a ⊓ b) = a := by
  rw [sup_comm]
  exact sup_eq_right.mpr (Lattice.inf_le_left a b)

end LatticeLemmas

/-- Dedekind's modular law: `z ≼ x → x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ z`. -/
def IsModularLattice (L : Type u) [Lattice L] : Prop :=
  ∀ x y z : L, z ≼ x → x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ z

/-- Equivalence between the two standard textbook formulations of the modular law. -/
theorem isModular_iff_dual (L : Type u) [Lattice L] :
    IsModularLattice L ↔ ∀ a b c : L, a ≼ c → a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ c := by
  constructor
  · intro hmod a b c hac
    rw [inf_comm (a ⊔ b) c]
    rw [sup_comm a b]
    rw [hmod c b a hac]
    rw [inf_comm c b, sup_comm]
  · intro hdual x y z hzx
    rw [inf_comm x (y ⊔ z), sup_comm y z]
    rw [← hdual z y x hzx]
    rw [inf_comm y x, sup_comm]

/-- Direct product of two lattices. -/
instance prodLattice (L₁ : Type u) (L₂ : Type v) [Lattice L₁] [Lattice L₂] :
    Lattice (L₁ × L₂) where
  le p q := p.1 ≼ q.1 ∧ p.2 ≼ q.2
  inf p q := (p.1 ⊓ q.1, p.2 ⊓ q.2)
  sup p q := (p.1 ⊔ q.1, p.2 ⊔ q.2)
  le_refl p := ⟨Lattice.le_refl p.1, Lattice.le_refl p.2⟩
  le_trans h1 h2 := ⟨Lattice.le_trans h1.1 h2.1, Lattice.le_trans h1.2 h2.2⟩
  le_antisymm h1 h2 := Prod.ext (Lattice.le_antisymm h1.1 h2.1) (Lattice.le_antisymm h1.2 h2.2)
  inf_le_left p q := ⟨Lattice.inf_le_left p.1 q.1, Lattice.inf_le_left p.2 q.2⟩
  inf_le_right p q := ⟨Lattice.inf_le_right p.1 q.1, Lattice.inf_le_right p.2 q.2⟩
  le_inf h1 h2 := ⟨Lattice.le_inf h1.1 h2.1, Lattice.le_inf h1.2 h2.2⟩
  le_sup_left p q := ⟨Lattice.le_sup_left p.1 q.1, Lattice.le_sup_left p.2 q.2⟩
  le_sup_right p q := ⟨Lattice.le_sup_right p.1 q.1, Lattice.le_sup_right p.2 q.2⟩
  sup_le h1 h2 := ⟨Lattice.sup_le h1.1 h2.1, Lattice.sup_le h1.2 h2.2⟩

theorem prod_isModular {L₁ : Type u} {L₂ : Type v} [Lattice L₁] [Lattice L₂]
    (h₁ : IsModularLattice L₁) (h₂ : IsModularLattice L₂) :
    IsModularLattice (L₁ × L₂) := by
  intro x y z hzx
  exact Prod.ext (h₁ x.1 y.1 z.1 hzx.1) (h₂ x.2 y.2 z.2 hzx.2)

/-- Duplicate-free list predicate. -/
inductive ListNodup {α : Type u} : List α → Prop where
  | nil : ListNodup []
  | cons {x : α} {xs : List α} : (∀ y ∈ xs, x ≠ y) → ListNodup xs → ListNodup (x :: xs)

/-- Exact finite cardinality `|α| = n` witnessed by a duplicate-free exhaustive list. -/
def HasCardinality (α : Type u) (n : Nat) : Prop :=
  ∃ elems : List α, ListNodup elems ∧ (∀ x : α, x ∈ elems) ∧ elems.length = n

def IsFiniteType (α : Type u) : Prop :=
  ∃ n : Nat, HasCardinality α n

section CardinalityUniqueness
open Classical

noncomputable def removeFirst {α : Type u} (a : α) : List α → List α
  | [] => []
  | x :: xs => if a = x then xs else x :: removeFirst a xs

theorem mem_of_mem_removeFirst {α : Type u} {a y : α} :
    ∀ {l : List α}, y ∈ removeFirst a l → y ∈ l
  | [], h => nomatch h
  | x :: xs, h => by
    unfold removeFirst at h
    split at h
    · exact List.mem_cons_of_mem x h
    · cases h with
      | head => exact List.Mem.head xs
      | tail _ hm => exact List.mem_cons_of_mem x (mem_of_mem_removeFirst hm)

theorem mem_removeFirst_of_ne {α : Type u} {a y : α} (hne : y ≠ a) :
    ∀ {l : List α}, y ∈ l → y ∈ removeFirst a l
  | [], h => nomatch h
  | x :: xs, h => by
    unfold removeFirst
    split
    · next hax =>
      cases h with
      | head => exact False.elim (hne hax.symm)
      | tail _ hm => exact hm
    · cases h with
      | head => exact List.Mem.head _
      | tail _ hm => exact List.mem_cons_of_mem x (mem_removeFirst_of_ne hne hm)

theorem length_removeFirst_of_mem {α : Type u} {a : α} :
    ∀ {l : List α}, a ∈ l → (removeFirst a l).length + 1 = l.length
  | [], h => nomatch h
  | x :: xs, h => by
    unfold removeFirst
    split
    · rfl
    · next hne =>
      cases h with
      | head => exact False.elim (hne rfl)
      | tail _ hm =>
        simp only [List.length_cons]
        exact congrArg (· + 1) (length_removeFirst_of_mem hm)

theorem nodup_length_le_of_subset {α : Type u} :
    ∀ {l₁ l₂ : List α}, ListNodup l₁ → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, ListNodup.cons hnotmem hnd, hsub => by
    have hx : x ∈ l₂ := hsub x (List.Mem.head xs)
    have hlen : (removeFirst x l₂).length + 1 = l₂.length := length_removeFirst_of_mem hx
    have hsub' : ∀ y ∈ xs, y ∈ removeFirst x l₂ := by
      intro y hy
      have hy_ne : y ≠ x := fun h => hnotmem y hy h.symm
      exact mem_removeFirst_of_ne hy_ne (hsub y (List.mem_cons_of_mem x hy))
    have ih := nodup_length_le_of_subset hnd hsub'
    simp only [List.length_cons]
    omega

/-- Any two duplicate-free exhaustive enumerations of a type have the exact same length. -/
theorem hasCardinality_unique {α : Type u} {m n : Nat}
    (hm : HasCardinality α m) (hn : HasCardinality α n) : m = n := by
  rcases hm with ⟨l₁, hnd₁, hall₁, rfl⟩
  rcases hn with ⟨l₂, hnd₂, hall₂, rfl⟩
  have h12 : l₁.length ≤ l₂.length := nodup_length_le_of_subset hnd₁ (fun x _ => hall₂ x)
  have h21 : l₂.length ≤ l₁.length := nodup_length_le_of_subset hnd₂ (fun x _ => hall₁ x)
  omega

end CardinalityUniqueness

/-- An injective lattice homomorphism (preserving meet and join; need not preserve bounds). -/
structure LatticeEmbedding (L : Type u) (M : Type v) [Lattice L] [Lattice M] where
  toFun : L → M
  inj : ∀ {a b : L}, toFun a = toFun b → a = b
  map_inf : ∀ a b : L, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_sup : ∀ a b : L, toFun (a ⊔ b) = toFun a ⊔ toFun b

namespace LatticeEmbedding

def comp {L : Type u} {M : Type v} {N : Type w} [Lattice L] [Lattice M] [Lattice N]
    (g : LatticeEmbedding M N) (f : LatticeEmbedding L M) : LatticeEmbedding L N where
  toFun x := g.toFun (f.toFun x)
  inj h := f.inj (g.inj h)
  map_inf a b := by rw [f.map_inf, g.map_inf]
  map_sup a b := by rw [f.map_sup, g.map_sup]

theorem map_le_iff {L : Type u} {M : Type v} [Lattice L] [Lattice M]
    (f : LatticeEmbedding L M) {a b : L} : f.toFun a ≼ f.toFun b ↔ a ≼ b := by
  rw [← inf_eq_left, ← inf_eq_left, ← f.map_inf]
  constructor
  · exact fun h => f.inj h
  · exact fun h => congrArg f.toFun h

end LatticeEmbedding

/-! ## 2. Abelian Groups, Division Rings, Fields, Vector Spaces, and Subspaces -/

class AddCommGroup (G : Type u) extends Add G, Neg G where
  zero : G
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
  zero_add : ∀ a : G, zero + a = a
  add_zero : ∀ a : G, a + zero = a
  neg_add_cancel : ∀ a : G, (-a) + a = zero
  add_comm : ∀ a b : G, a + b = b + a

instance acgOfNatZero {G : Type u} [inst : AddCommGroup G] : OfNat G 0 := ⟨inst.zero⟩

section AddCommGroupLemmas
variable {G : Type u} [AddCommGroup G]

theorem acg_zero_add (a : G) : (0 : G) + a = a := AddCommGroup.zero_add a
theorem acg_add_zero (a : G) : a + (0 : G) = a := AddCommGroup.add_zero a
theorem acg_neg_add_cancel (a : G) : (-a) + a = 0 := AddCommGroup.neg_add_cancel a

theorem acg_add_neg_cancel (a : G) : a + (-a) = 0 := by
  rw [AddCommGroup.add_comm, acg_neg_add_cancel]

theorem acg_add_left_cancel {a b c : G} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun t => (-a) + t) h
  rw [← AddCommGroup.add_assoc, ← AddCommGroup.add_assoc,
      acg_neg_add_cancel, acg_zero_add, acg_zero_add] at h1
  exact h1

theorem acg_add_right_cancel {a b c : G} (h : a + c = b + c) : a = b := by
  apply acg_add_left_cancel (a := c)
  rw [AddCommGroup.add_comm c a, AddCommGroup.add_comm c b]
  exact h

theorem acg_neg_zero : -(0 : G) = 0 := by
  apply acg_add_left_cancel (a := (0 : G))
  rw [acg_add_neg_cancel, acg_add_zero]

theorem acg_neg_neg (a : G) : -(-a) = a := by
  apply acg_add_left_cancel (a := -a)
  rw [acg_add_neg_cancel, acg_neg_add_cancel]

theorem acg_neg_add (a b : G) : -(a + b) = (-a) + (-b) := by
  apply acg_add_left_cancel (a := a + b)
  have hcalc : (a + b) + ((-a) + (-b)) = 0 := by
    calc
      (a + b) + ((-a) + (-b)) = a + (b + ((-a) + (-b))) := AddCommGroup.add_assoc _ _ _
      _ = a + (b + ((-b) + (-a))) := by rw [AddCommGroup.add_comm (-a) (-b)]
      _ = a + ((b + (-b)) + (-a)) := by rw [← AddCommGroup.add_assoc b (-b) (-a)]
      _ = a + (0 + (-a)) := by rw [acg_add_neg_cancel]
      _ = a + (-a) := by rw [acg_zero_add]
      _ = 0 := acg_add_neg_cancel a
  rw [acg_add_neg_cancel, hcalc]

def gsub (a b : G) : G := a + (-b)
scoped infixl:65 " -₉ " => gsub

theorem gsub_self (a : G) : a -₉ a = 0 := acg_add_neg_cancel a

theorem add_gsub_cancel (a b : G) : (a + b) -₉ b = a := by
  unfold gsub
  rw [AddCommGroup.add_assoc, acg_add_neg_cancel, acg_add_zero]

theorem gsub_zero (a : G) : a -₉ 0 = a := by
  unfold gsub
  rw [acg_neg_zero, acg_add_zero]

theorem zero_gsub (a : G) : (0 : G) -₉ a = -a := by
  unfold gsub
  rw [acg_zero_add]

theorem neg_gsub (a b : G) : -(a -₉ b) = b -₉ a := by
  unfold gsub
  rw [acg_neg_add, acg_neg_neg, AddCommGroup.add_comm]

theorem gsub_add_gsub (a b c : G) : (a -₉ b) + (b -₉ c) = a -₉ c := by
  unfold gsub
  calc
    (a + (-b)) + (b + (-c)) = a + ((-b) + (b + (-c))) := AddCommGroup.add_assoc _ _ _
    _ = a + (((-b) + b) + (-c)) := by rw [← AddCommGroup.add_assoc (-b) b (-c)]
    _ = a + (0 + (-c)) := by rw [acg_neg_add_cancel]
    _ = a + (-c) := by rw [acg_zero_add]

theorem add_rearrange4 (a b c d : G) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := AddCommGroup.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := by rw [← AddCommGroup.add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [AddCommGroup.add_comm b c]
    _ = a + (c + (b + d)) := by rw [AddCommGroup.add_assoc c b d]
    _ = (a + c) + (b + d) := (AddCommGroup.add_assoc a c (b + d)).symm

theorem add_rearrange6 (a b c d e f : G) :
    ((a + b) + (c + d)) + (e + f) = ((a + c) + e) + ((b + d) + f) := by
  calc
    ((a + b) + (c + d)) + (e + f)
        = ((a + c) + (b + d)) + (e + f) := by rw [add_rearrange4 a b c d]
    _ = (a + c) + ((b + d) + (e + f)) := AddCommGroup.add_assoc (a + c) (b + d) (e + f)
    _ = (a + c) + ((e + (b + d)) + f) := by
      rw [← AddCommGroup.add_assoc (b + d) e f, AddCommGroup.add_comm (b + d) e]
    _ = (a + c) + (e + ((b + d) + f)) := by rw [AddCommGroup.add_assoc e (b + d) f]
    _ = ((a + c) + e) + ((b + d) + f) := (AddCommGroup.add_assoc (a + c) e ((b + d) + f)).symm

theorem gsub_add_distrib (x1 x2 y1 y2 : G) :
    (x1 + x2) -₉ (y1 + y2) = (x1 -₉ y1) + (x2 -₉ y2) := by
  unfold gsub
  rw [acg_neg_add, ← add_rearrange4]

theorem gsub_sum3 (x1 x2 x3 y1 y2 y3 : G) :
    ((x1 -₉ y1) + (x2 -₉ y2)) + (x3 -₉ y3) = ((x1 + x2) + x3) -₉ ((y1 + y2) + y3) := by
  unfold gsub
  rw [acg_neg_add (y1 + y2) y3, acg_neg_add y1 y2]
  exact add_rearrange6 x1 (-y1) x2 (-y2) x3 (-y3)

theorem gsub_sub_cancel_left (a b c : G) :
    (a + b) -₉ (a -₉ c) = b -₉ (-c) := by
  unfold gsub
  rw [acg_neg_add a (-c), AddCommGroup.add_comm a b,
      AddCommGroup.add_assoc b a ((-a) + (-(-c))),
      ← AddCommGroup.add_assoc a (-a) (-(-c)),
      acg_add_neg_cancel, acg_zero_add]

theorem gsub_neg_double (u : G) :
    u -₉ ((-u) + (-u)) = (u + u) + u := by
  unfold gsub
  rw [acg_neg_add (-u) (-u), acg_neg_neg u, ← AddCommGroup.add_assoc u u u]

end AddCommGroupLemmas

class DivisionRing (K : Type u) extends AddCommGroup K, Mul K where
  one : K
  inv : K → K
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  one_mul : ∀ a : K, one * a = a
  mul_one : ∀ a : K, a * one = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  one_ne_zero : one ≠ 0
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * inv a = one
  inv_mul_cancel : ∀ a : K, a ≠ 0 → inv a * a = one

instance drOfNatOne {K : Type u} [inst : DivisionRing K] : OfNat K 1 := ⟨inst.one⟩
scoped postfix:max "⁻¹" => DivisionRing.inv

class Field (K : Type u) extends DivisionRing K where
  mul_comm : ∀ a b : K, a * b = b * a

section DivisionRingLemmas
variable {K : Type u} [DivisionRing K]

theorem dr_one_mul (a : K) : (1 : K) * a = a := DivisionRing.one_mul a
theorem dr_mul_one (a : K) : a * (1 : K) = a := DivisionRing.mul_one a
theorem dr_one_ne_zero : (1 : K) ≠ 0 := DivisionRing.one_ne_zero
theorem dr_mul_inv_cancel {a : K} (ha : a ≠ 0) : a * a⁻¹ = 1 := DivisionRing.mul_inv_cancel a ha
theorem dr_inv_mul_cancel {a : K} (ha : a ≠ 0) : a⁻¹ * a = 1 := DivisionRing.inv_mul_cancel a ha

theorem mul_zero_dr (a : K) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← DivisionRing.left_distrib, acg_add_zero, acg_add_zero]
  exact acg_add_left_cancel h

theorem zero_mul_dr (a : K) : (0 : K) * a = 0 := by
  have h : (0 : K) * a + (0 : K) * a = (0 : K) * a + 0 := by
    rw [← DivisionRing.right_distrib, acg_zero_add, acg_add_zero]
  exact acg_add_left_cancel h

theorem neg_one_mul_dr (a : K) : (-1 : K) * a = -a := by
  have h : a + (-1 : K) * a = a + (-a) := by
    calc
      a + (-1 : K) * a = (1 : K) * a + (-1 : K) * a := by rw [dr_one_mul]
      _ = ((1 : K) + (-1 : K)) * a := by rw [← DivisionRing.right_distrib]
      _ = (0 : K) * a := by rw [acg_add_neg_cancel]
      _ = 0 := zero_mul_dr a
      _ = a + (-a) := (acg_add_neg_cancel a).symm
  exact acg_add_left_cancel h

theorem mul_neg_dr (a b : K) : a * (-b) = -(a * b) := by
  apply acg_add_left_cancel (a := a * b)
  rw [← DivisionRing.left_distrib, acg_add_neg_cancel, mul_zero_dr, acg_add_neg_cancel]

theorem neg_mul_dr (a b : K) : (-a) * b = -(a * b) := by
  apply acg_add_left_cancel (a := a * b)
  rw [← DivisionRing.right_distrib, acg_add_neg_cancel, zero_mul_dr, acg_add_neg_cancel]

theorem char_two_and_three_impossible
    (h2 : (1 : K) + 1 = 0) (h3 : ((1 : K) + 1) + 1 = 0) : False := by
  rw [h2, acg_zero_add] at h3
  exact dr_one_ne_zero h3

end DivisionRingLemmas

class VectorSpace (K : Type u) [DivisionRing K] (V : Type v) [AddCommGroup V] where
  smul : K → V → V
  one_smul : ∀ v : V, smul 1 v = v
  mul_smul : ∀ (a b : K) (v : V), smul (a * b) v = smul a (smul b v)
  add_smul : ∀ (a b : K) (v : V), smul (a + b) v = smul a v + smul b v
  smul_add : ∀ (a : K) (u v : V), smul a (u + v) = smul a u + smul a v

scoped infixr:73 " • " => VectorSpace.smul

section VectorSpaceLemmas
variable {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V]

theorem vs_zero_smul (v : V) : (0 : K) • v = 0 := by
  have h : (0 : K) • v + (0 : K) • v = (0 : K) • v + 0 := by
    rw [← VectorSpace.add_smul, acg_zero_add, acg_add_zero]
  exact acg_add_left_cancel h

theorem vs_smul_zero (c : K) : c • (0 : V) = 0 := by
  have h : c • (0 : V) + c • (0 : V) = c • (0 : V) + 0 := by
    rw [← VectorSpace.smul_add, acg_add_zero, acg_add_zero]
  exact acg_add_left_cancel h

theorem vs_neg_one_smul (v : V) : (-1 : K) • v = -v := by
  have h : v + (-1 : K) • v = v + (-v) := by
    calc
      v + (-1 : K) • v = (1 : K) • v + (-1 : K) • v := by rw [VectorSpace.one_smul]
      _ = ((1 : K) + (-1 : K)) • v := by rw [← VectorSpace.add_smul]
      _ = (0 : K) • v := by rw [acg_add_neg_cancel]
      _ = 0 := vs_zero_smul v
      _ = v + (-v) := (acg_add_neg_cancel v).symm
  exact acg_add_left_cancel h

theorem vs_smul_neg (c : K) (v : V) : c • (-v) = -(c • v) := by
  apply acg_add_left_cancel (a := c • v)
  rw [← VectorSpace.smul_add, acg_add_neg_cancel, vs_smul_zero, acg_add_neg_cancel]

theorem vs_neg_smul (c : K) (v : V) : (-c) • v = -(c • v) := by
  apply acg_add_left_cancel (a := c • v)
  rw [← VectorSpace.add_smul, acg_add_neg_cancel, vs_zero_smul, acg_add_neg_cancel]

end VectorSpaceLemmas

/-- Linear subspace of a left `K`-vector space `V`. -/
structure Subspace (K : Type u) [DivisionRing K] (V : Type v) [AddCommGroup V] [VectorSpace K V] where
  mem : V → Prop
  zero_mem : mem 0
  add_mem : ∀ {u v : V}, mem u → mem v → mem (u + v)
  smul_mem : ∀ (c : K) {v : V}, mem v → mem (c • v)

section SubspaceLattice
variable {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V]

theorem Subspace.ext {U W : Subspace K V} (h : ∀ v : V, U.mem v ↔ W.mem v) : U = W := by
  cases U with
  | mk mU zU aU sU =>
    cases W with
    | mk mW zW aW sW =>
      have hm : mU = mW := funext (fun v => propext (h v))
      subst hm
      rfl

theorem Subspace.neg_mem (W : Subspace K V) {v : V} (hv : W.mem v) : W.mem (-v) := by
  have h : (-1 : K) • v = -v := vs_neg_one_smul (K := K) v
  rw [← h]
  exact W.smul_mem (-1) hv

theorem Subspace.sub_mem (W : Subspace K V) {u v : V} (hu : W.mem u) (hv : W.mem v) :
    W.mem (u -₉ v) :=
  W.add_mem hu (W.neg_mem hv)

theorem Subspace.cancel_smul_mem (W : Subspace K V) {c : K} (hc : c ≠ 0) {v : V}
    (hcv : W.mem (c • v)) : W.mem v := by
  have h1 : W.mem (c⁻¹ • (c • v)) := W.smul_mem c⁻¹ hcv
  rw [← VectorSpace.mul_smul, dr_inv_mul_cancel hc, VectorSpace.one_smul] at h1
  exact h1

def subspaceInf (U W : Subspace K V) : Subspace K V where
  mem v := U.mem v ∧ W.mem v
  zero_mem := ⟨U.zero_mem, W.zero_mem⟩
  add_mem := fun ⟨hu1, hu2⟩ ⟨hv1, hv2⟩ => ⟨U.add_mem hu1 hv1, W.add_mem hu2 hv2⟩
  smul_mem := fun c {_} ⟨hv1, hv2⟩ => ⟨U.smul_mem c hv1, W.smul_mem c hv2⟩

def subspaceSup (U W : Subspace K V) : Subspace K V where
  mem v := ∃ u w : V, U.mem u ∧ W.mem w ∧ v = u + w
  zero_mem := ⟨0, 0, U.zero_mem, W.zero_mem, (acg_add_zero 0).symm⟩
  add_mem := by
    intro x y ⟨u1, w1, hu1, hw1, hx⟩ ⟨u2, w2, hu2, hw2, hy⟩
    refine ⟨u1 + u2, w1 + w2, U.add_mem hu1 hu2, W.add_mem hw1 hw2, ?_⟩
    subst hx; subst hy
    calc
      (u1 + w1) + (u2 + w2) = u1 + (w1 + (u2 + w2)) := AddCommGroup.add_assoc _ _ _
      _ = u1 + ((w1 + u2) + w2) := by rw [← AddCommGroup.add_assoc w1 u2 w2]
      _ = u1 + ((u2 + w1) + w2) := by rw [AddCommGroup.add_comm w1 u2]
      _ = u1 + (u2 + (w1 + w2)) := by rw [AddCommGroup.add_assoc u2 w1 w2]
      _ = (u1 + u2) + (w1 + w2) := (AddCommGroup.add_assoc u1 u2 (w1 + w2)).symm
  smul_mem := by
    intro c x ⟨u, w, hu, hw, hx⟩
    subst hx
    exact ⟨c • u, c • w, U.smul_mem c hu, W.smul_mem c hw, VectorSpace.smul_add c u w⟩

instance subspaceLattice : Lattice (Subspace K V) where
  le U W := ∀ v : V, U.mem v → W.mem v
  inf := subspaceInf
  sup := subspaceSup
  le_refl _ _ hv := hv
  le_trans h1 h2 v hv := h2 v (h1 v hv)
  le_antisymm h1 h2 := Subspace.ext (fun v => ⟨h1 v, h2 v⟩)
  inf_le_left _ _ _ hv := hv.1
  inf_le_right _ _ _ hv := hv.2
  le_inf h1 h2 v hv := ⟨h1 v hv, h2 v hv⟩
  le_sup_left U W v hv := ⟨v, 0, hv, W.zero_mem, (acg_add_zero v).symm⟩
  le_sup_right U W v hv := ⟨0, v, U.zero_mem, hv, (acg_zero_add v).symm⟩
  sup_le := by
    intro U W Z h1 h2 v ⟨u, w, hu, hw, hv⟩
    subst hv
    exact Z.add_mem (h1 u hu) (h2 w hw)

/-- Every subspace lattice `Subspace K V` is a modular lattice. -/
theorem subspace_isModular : IsModularLattice (Subspace K V) := by
  intro X Y Z hZX
  apply Subspace.ext
  intro v
  show (X.mem v ∧ ∃ y z : V, Y.mem y ∧ Z.mem z ∧ v = y + z) ↔
       (∃ y z : V, (X.mem y ∧ Y.mem y) ∧ Z.mem z ∧ v = y + z)
  constructor
  · rintro ⟨hvX, y, z, hyY, hzZ, rfl⟩
    have hzX : X.mem z := hZX z hzZ
    have hyX : X.mem y := by
      have hsub : X.mem ((y + z) -₉ z) := X.sub_mem hvX hzX
      rw [add_gsub_cancel] at hsub
      exact hsub
    exact ⟨y, z, ⟨hyX, hyY⟩, hzZ, rfl⟩
  · rintro ⟨y, z, ⟨hyX, hyY⟩, hzZ, rfl⟩
    exact ⟨X.add_mem hyX (hZX z hzZ), y, z, hyY, hzZ, rfl⟩

end SubspaceLattice

/-- Coordinate vector space `K^d` of linear dimension `d`. -/
def FinVec (K : Type u) (d : Nat) : Type u := Fin d → K

instance finVecAddCommGroup (K : Type u) [AddCommGroup K] (d : Nat) :
    AddCommGroup (FinVec K d) where
  zero := fun _ => 0
  add u v := fun i => u i + v i
  neg u := fun i => -(u i)
  add_assoc u v w := funext (fun i => AddCommGroup.add_assoc (u i) (v i) (w i))
  zero_add u := funext (fun i => acg_zero_add (u i))
  add_zero u := funext (fun i => acg_add_zero (u i))
  neg_add_cancel u := funext (fun i => acg_neg_add_cancel (u i))
  add_comm u v := funext (fun i => AddCommGroup.add_comm (u i) (v i))

instance finVecVectorSpace (K : Type u) [DivisionRing K] (d : Nat) :
    VectorSpace K (FinVec K d) where
  smul c u := fun i => c * u i
  one_smul u := funext (fun i => dr_one_mul (u i))
  mul_smul a b u := funext (fun i => DivisionRing.mul_assoc a b (u i))
  add_smul a b u := funext (fun i => DivisionRing.right_distrib a b (u i))
  smul_add a u v := funext (fun i => DivisionRing.left_distrib a (u i) (v i))

/-- Inductive linear span of a finite list of vectors in `V`. -/
inductive InSpan (K : Type u) [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V]
    (B : List V) : V → Prop where
  | zero : InSpan K B 0
  | gen {v : V} : v ∈ B → InSpan K B v
  | add {u w : V} : InSpan K B u → InSpan K B w → InSpan K B (u + w)
  | smul (c : K) {v : V} : InSpan K B v → InSpan K B (c • v)

/-- Linear combination of a list of vectors with coefficients from `K`. -/
def linComb (K : Type u) [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V] :
    List K → List V → V
  | [], _ => 0
  | _, [] => 0
  | c :: cs, v :: vs => c • v + linComb K cs vs

def LinearIndependent (K : Type u) [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V]
    (B : List V) : Prop :=
  ∀ cs : List K, cs.length = B.length → linComb K cs B = 0 → ∀ c ∈ cs, c = 0

/-- `V` has an explicit finite basis of length `d` (linear dimension `d`). -/
def HasLinearDimension (K : Type u) [DivisionRing K] (V : Type v) [AddCommGroup V] [VectorSpace K V]
    (d : Nat) : Prop :=
  ∃ B : List V, B.length = d ∧ LinearIndependent K B ∧ (∀ v : V, InSpan K B v)

/-- `V` is spanned by at most `n` vectors (holds whenever `dim_K(V) ≤ n`). -/
def HasDimensionAtMost (K : Type u) [DivisionRing K] (V : Type v) [AddCommGroup V] [VectorSpace K V]
    (n : Nat) : Prop :=
  ∃ B : List V, B.length ≤ n ∧ ∀ v : V, InSpan K B v

theorem hasDimensionAtMost_of_hasLinearDimension {K : Type u} [DivisionRing K]
    {V : Type v} [AddCommGroup V] [VectorSpace K V] {d n : Nat}
    (hd : HasLinearDimension K V d) (hle : d ≤ n) : HasDimensionAtMost K V n := by
  rcases hd with ⟨B, hlen, _, hspan⟩
  exact ⟨B, hlen ▸ hle, hspan⟩

/-! ## 3. Concrete Projective Plane Subspace Lattices `Sub3 F2` and `Sub3 F3` -/

/-- Boolean duplicate-free checker for decidable types. -/
def elemBool {α : Type u} [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | x :: xs => if a = x then true else elemBool a xs

theorem not_mem_of_elemBool_false {α : Type u} [DecidableEq α] {a : α} :
    ∀ {l : List α}, elemBool a l = false → ∀ y ∈ l, a ≠ y
  | [], _, _, hy => nomatch hy
  | x :: xs, h, y, hy => by
    unfold elemBool at h
    split at h
    · contradiction
    · next hne =>
      cases hy with
      | head => exact hne
      | tail _ hm => exact not_mem_of_elemBool_false h y hm

def nodupBool {α : Type u} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => (!elemBool x xs) && nodupBool xs

theorem nodup_of_nodupBool {α : Type u} [DecidableEq α] :
    ∀ {l : List α}, nodupBool l = true → ListNodup l
  | [], _ => ListNodup.nil
  | x :: xs, h => by
    unfold nodupBool at h
    cases h1 : elemBool x xs with
    | true =>
      rw [h1] at h
      contradiction
    | false =>
      rw [h1] at h
      have h2 : nodupBool xs = true := by simpa using h
      exact ListNodup.cons (not_mem_of_elemBool_false h1) (nodup_of_nodupBool h2)

/-- The two-element prime field `GF(2)`. -/
inductive F2 where
  | f0
  | f1
  deriving DecidableEq

def f2Add : F2 → F2 → F2
  | .f0, b => b
  | .f1, .f0 => .f1
  | .f1, .f1 => .f0

def f2Mul : F2 → F2 → F2
  | .f1, .f1 => .f1
  | _, _ => .f0

instance : Add F2 := ⟨f2Add⟩
instance : Neg F2 := ⟨fun a => a⟩
instance : Mul F2 := ⟨f2Mul⟩

instance : AddCommGroup F2 where
  zero := .f0
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl

instance : DivisionRing F2 where
  one := .f1
  inv a := a
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_ne_zero := by decide
  mul_inv_cancel a ha := by cases a with | f0 => exact False.elim (ha rfl) | f1 => rfl
  inv_mul_cancel a ha := by cases a with | f0 => exact False.elim (ha rfl) | f1 => rfl

instance : Field F2 where
  mul_comm a b := by cases a <;> cases b <;> rfl

/-- The three-element prime field `GF(3)`. -/
inductive F3 where
  | f0
  | f1
  | f2
  deriving DecidableEq

def f3Add : F3 → F3 → F3
  | .f0, b => b
  | a, .f0 => a
  | .f1, .f1 => .f2
  | .f1, .f2 => .f0
  | .f2, .f1 => .f0
  | .f2, .f2 => .f1

def f3Neg : F3 → F3
  | .f0 => .f0
  | .f1 => .f2
  | .f2 => .f1

def f3Mul : F3 → F3 → F3
  | .f0, _ => .f0
  | _, .f0 => .f0
  | .f1, b => b
  | a, .f1 => a
  | .f2, .f2 => .f1

instance : Add F3 := ⟨f3Add⟩
instance : Neg F3 := ⟨f3Neg⟩
instance : Mul F3 := ⟨f3Mul⟩

instance : AddCommGroup F3 where
  zero := .f0
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl

instance : DivisionRing F3 where
  one := .f1
  inv a := a
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_ne_zero := by decide
  mul_inv_cancel a ha := by cases a with | f0 => exact False.elim (ha rfl) | f1 => rfl | f2 => rfl
  inv_mul_cancel a ha := by cases a with | f0 => exact False.elim (ha rfl) | f1 => rfl | f2 => rfl

instance : Field F3 where
  mul_comm a b := by cases a <;> cases b <;> rfl

/-- Projectively normalized nonzero vectors in `F^3` (first nonzero entry equal to `1`). -/
inductive NormVec3 (F : Type) where
  | e0 (b c : F)
  | e1 (c : F)
  | e2
  deriving DecidableEq

/-- Canonical finite representation of all linear subspaces of `F^3`. -/
inductive Sub3 (F : Type) where
  | bot
  | line (p : NormVec3 F)
  | plane (n : NormVec3 F)
  | top
  deriving DecidableEq

abbrev Triple (F : Type) := F × F × F

theorem forall_of_list_all {α : Type u} {p : α → Bool} :
    ∀ {l : List α}, l.all p = true → ∀ x ∈ l, p x = true
  | [], _, _, hx => nomatch hx
  | a :: as, h, x, hx => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hx with
    | head => exact h.1
    | tail _ hm => exact forall_of_list_all h.2 x hm

def normVec3Elems (el : List F) : List (NormVec3 F) :=
  (el.flatMap fun b => el.map fun c => NormVec3.e0 b c) ++
  (el.map fun c => NormVec3.e1 c) ++
  [NormVec3.e2]

def sub3Elems (el : List F) : List (Sub3 F) :=
  let nvs := normVec3Elems el
  [Sub3.bot] ++ (nvs.map Sub3.line) ++ (nvs.map Sub3.plane) ++ [Sub3.top]

def toTriple {F : Type} (v : FinVec F 3) : Triple F :=
  (v ⟨0, by decide⟩, v ⟨1, by decide⟩, v ⟨2, by decide⟩)

def ofTriple {F : Type} (t : Triple F) : FinVec F 3
  | ⟨0, _⟩ => t.1
  | ⟨1, _⟩ => t.2.1
  | ⟨2, _⟩ => t.2.2

theorem ofTriple_toTriple {F : Type} (v : FinVec F 3) : ofTriple (toTriple v) = v := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem toTriple_ofTriple {F : Type} (t : Triple F) : toTriple (ofTriple t) = t := rfl

section Sub3General
variable {F : Type} [Field F]

def nvTriple : NormVec3 F → Triple F
  | .e0 b c => (1, b, c)
  | .e1 c   => (0, 1, c)
  | .e2     => (0, 0, 1)

def addT (u v : Triple F) : Triple F :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

def subT (u v : Triple F) : Triple F :=
  (u.1 -₉ v.1, u.2.1 -₉ v.2.1, u.2.2 -₉ v.2.2)

def smulT (c : F) (u : Triple F) : Triple F :=
  (c * u.1, c * u.2.1, c * u.2.2)

def dotT (u v : Triple F) : F :=
  (u.1 * v.1 + u.2.1 * v.2.1) + u.2.2 * v.2.2

def crossT (u v : Triple F) : Triple F :=
  (u.2.1 * v.2.2 -₉ u.2.2 * v.2.1,
   u.2.2 * v.1 -₉ u.1 * v.2.2,
   u.1 * v.2.1 -₉ u.2.1 * v.1)

def normT [DecidableEq F] (t : Triple F) : NormVec3 F :=
  if t.1 ≠ 0 then .e0 (t.1⁻¹ * t.2.1) (t.1⁻¹ * t.2.2)
  else if t.2.1 ≠ 0 then .e1 (t.2.1⁻¹ * t.2.2)
  else .e2

def sub3LeBool [DecidableEq F] : Sub3 F → Sub3 F → Bool
  | .bot, _ => true
  | _, .top => true
  | .line p, .line q => decide (p = q)
  | .line p, .plane n => decide (dotT (nvTriple n) (nvTriple p) = 0)
  | .plane n, .plane m => decide (n = m)
  | _, _ => false

def sub3Le [DecidableEq F] (a b : Sub3 F) : Prop :=
  sub3LeBool a b = true

def sub3Inf [DecidableEq F] : Sub3 F → Sub3 F → Sub3 F
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, b => b
  | a, .top => a
  | .line p, .line q => if p = q then .line p else .bot
  | .line p, .plane n => if dotT (nvTriple n) (nvTriple p) = 0 then .line p else .bot
  | .plane n, .line p => if dotT (nvTriple n) (nvTriple p) = 0 then .line p else .bot
  | .plane n, .plane m => if n = m then .plane n else .line (normT (crossT (nvTriple n) (nvTriple m)))

def sub3Sup [DecidableEq F] : Sub3 F → Sub3 F → Sub3 F
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .line p, .line q => if p = q then .line p else .plane (normT (crossT (nvTriple p) (nvTriple q)))
  | .line p, .plane n => if dotT (nvTriple n) (nvTriple p) = 0 then .plane n else .top
  | .plane n, .line p => if dotT (nvTriple n) (nvTriple p) = 0 then .plane n else .top
  | .plane n, .plane m => if n = m then .plane n else .top

theorem dotT_zero_right (u : Triple F) : dotT u (0, 0, 0) = 0 := by
  unfold dotT
  rw [mul_zero_dr, mul_zero_dr, mul_zero_dr, acg_add_zero, acg_add_zero]

theorem dotT_add_right (u v w : Triple F) :
    dotT u (addT v w) = dotT u v + dotT u w := by
  unfold dotT addT
  rw [DivisionRing.left_distrib, DivisionRing.left_distrib, DivisionRing.left_distrib]
  have rearrange : ∀ a b c d e f : F, ((a + b) + (c + d)) + (e + f) = ((a + c) + e) + ((b + d) + f) := by
    intro a b c d e f
    calc
      ((a + b) + (c + d)) + (e + f)
          = (a + (b + (c + d))) + (e + f) := by rw [AddCommGroup.add_assoc a b (c + d)]
      _ = (a + ((b + c) + d)) + (e + f) := by rw [← AddCommGroup.add_assoc b c d]
      _ = (a + ((c + b) + d)) + (e + f) := by rw [AddCommGroup.add_comm b c]
      _ = (a + (c + (b + d))) + (e + f) := by rw [AddCommGroup.add_assoc c b d]
      _ = ((a + c) + (b + d)) + (e + f) := by rw [← AddCommGroup.add_assoc a c (b + d)]
      _ = (a + c) + ((b + d) + (e + f)) := by rw [AddCommGroup.add_assoc (a + c) (b + d) (e + f)]
      _ = (a + c) + (((b + d) + e) + f) := by rw [← AddCommGroup.add_assoc (b + d) e f]
      _ = (a + c) + ((e + (b + d)) + f) := by rw [AddCommGroup.add_comm (b + d) e]
      _ = (a + c) + (e + ((b + d) + f)) := by rw [AddCommGroup.add_assoc e (b + d) f]
      _ = ((a + c) + e) + ((b + d) + f) := by rw [← AddCommGroup.add_assoc (a + c) e ((b + d) + f)]
  exact rearrange _ _ _ _ _ _

theorem dotT_smul_right (u : Triple F) (c : F) (v : Triple F) :
    dotT u (smulT c v) = c * dotT u v := by
  unfold dotT smulT
  have h1 : u.1 * (c * v.1) = c * (u.1 * v.1) := by
    rw [← DivisionRing.mul_assoc, Field.mul_comm u.1 c, DivisionRing.mul_assoc]
  have h2 : u.2.1 * (c * v.2.1) = c * (u.2.1 * v.2.1) := by
    rw [← DivisionRing.mul_assoc, Field.mul_comm u.2.1 c, DivisionRing.mul_assoc]
  have h3 : u.2.2 * (c * v.2.2) = c * (u.2.2 * v.2.2) := by
    rw [← DivisionRing.mul_assoc, Field.mul_comm u.2.2 c, DivisionRing.mul_assoc]
  rw [h1, h2, h3, ← DivisionRing.left_distrib, ← DivisionRing.left_distrib]

/-- Realization of each element of `Sub3 F` as an actual linear subspace of `FinVec F 3`. -/
def sub3ToSubspace : Sub3 F → Subspace F (FinVec F 3)
  | .bot => {
      mem := fun v => v = 0
      zero_mem := rfl
      add_mem := by intro u v hu hv; subst hu; subst hv; exact acg_add_zero (0 : FinVec F 3)
      smul_mem := by intro c v hv; subst hv; exact vs_smul_zero c
    }
  | .line p => {
      mem := fun v => ∃ t : F, v = t • ofTriple (nvTriple p)
      zero_mem := ⟨0, (vs_zero_smul _).symm⟩
      add_mem := by
        rintro u v ⟨t1, rfl⟩ ⟨t2, rfl⟩
        exact ⟨t1 + t2, (VectorSpace.add_smul t1 t2 _).symm⟩
      smul_mem := by
        rintro c v ⟨t, rfl⟩
        exact ⟨c * t, (VectorSpace.mul_smul c t _).symm⟩
    }
  | .plane n => {
      mem := fun v => dotT (nvTriple n) (toTriple v) = 0
      zero_mem := dotT_zero_right (nvTriple n)
      add_mem := by
        intro u v hu hv
        change dotT (nvTriple n) (addT (toTriple u) (toTriple v)) = 0
        rw [dotT_add_right, hu, hv, acg_add_zero]
      smul_mem := by
        intro c v hv
        change dotT (nvTriple n) (smulT c (toTriple v)) = 0
        rw [dotT_smul_right, hv, mul_zero_dr]
    }
  | .top => {
      mem := fun _ => True
      zero_mem := trivial
      add_mem := by intros; trivial
      smul_mem := by intros; trivial
    }

end Sub3General

/-! ### 3A. Lattice and Modularity Instances for `Sub3 F2` (16 elements) -/

def sub3ElemsF2 : List (Sub3 F2) := sub3Elems [F2.f0, F2.f1]

theorem mem_sub3ElemsF2 (s : Sub3 F2) : s ∈ sub3ElemsF2 := by
  cases s with
  | bot => decide
  | top => decide
  | line p => cases p with | e0 b c => cases b <;> cases c <;> decide | e1 c => cases c <;> decide | e2 => decide
  | plane n => cases n with | e0 b c => cases b <;> cases c <;> decide | e1 c => cases c <;> decide | e2 => decide

theorem sub3F2_hasCardinality : HasCardinality (Sub3 F2) 16 :=
  ⟨sub3ElemsF2, nodup_of_nodupBool (by decide), mem_sub3ElemsF2, rfl⟩

def inSub3F2 (s : Sub3 F2) (v : Triple F2) : Bool :=
  match s with
  | .bot => decide (v = (.f0, .f0, .f0))
  | .line p =>
    let u := nvTriple p
    decide (v = smulT .f0 u) || decide (v = smulT .f1 u)
  | .plane n => decide (dotT (nvTriple n) v = .f0)
  | .top => true

theorem inSub3F2_iff (s : Sub3 F2) (v : FinVec F2 3) :
    (sub3ToSubspace s).mem v ↔ inSub3F2 s (toTriple v) = true := by
  cases s with
  | bot =>
    simp only [sub3ToSubspace, inSub3F2, decide_eq_true_eq]
    constructor
    · intro h; subst h; rfl
    · intro h
      calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
        _ = ofTriple (.f0, .f0, .f0) := by rw [h]
        _ = 0 := by funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
  | line p =>
    simp only [sub3ToSubspace, inSub3F2, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨t, rfl⟩
      cases t with
      | f0 => exact Or.inl rfl
      | f1 => exact Or.inr rfl
    · intro h
      rcases h with h0 | h1
      · refine ⟨.f0, ?_⟩
        calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
          _ = ofTriple (smulT .f0 (nvTriple p)) := by rw [h0]
          _ = (.f0 : F2) • ofTriple (nvTriple p) := by
            funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
      · refine ⟨.f1, ?_⟩
        calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
          _ = ofTriple (smulT .f1 (nvTriple p)) := by rw [h1]
          _ = (.f1 : F2) • ofTriple (nvTriple p) := by
            funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
  | plane n =>
    simp only [sub3ToSubspace, inSub3F2, decide_eq_true_eq]
    rfl
  | top =>
    simp only [sub3ToSubspace, inSub3F2]

def allTriplesF2 : List (Triple F2) :=
  let el := [F2.f0, F2.f1]
  el.flatMap fun x => el.flatMap fun y => el.map fun z => (x, y, z)

theorem mem_allTriplesF2 (u : Triple F2) : u ∈ allTriplesF2 := by
  rcases u with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

def findWitnessF2 (p : Triple F2 → Bool) : Triple F2 :=
  match allTriplesF2.find? p with
  | some u => u
  | none => (.f0, .f0, .f0)

theorem f2_sep_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b =>
      decide (a = b) ||
      (let u := findWitnessF2 (fun u => inSub3F2 a u != inSub3F2 b u)
       inSub3F2 a u != inSub3F2 b u)) = true := by decide

theorem f2_inf_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b => allTriplesF2.all fun u =>
      decide (inSub3F2 (sub3Inf a b) u = (inSub3F2 a u && inSub3F2 b u))) = true := by decide

theorem f2_sup_le_l_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b => allTriplesF2.all fun u =>
      (!inSub3F2 a u) || inSub3F2 (sub3Sup a b) u) = true := by decide

theorem f2_sup_le_r_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b => allTriplesF2.all fun u =>
      (!inSub3F2 b u) || inSub3F2 (sub3Sup a b) u) = true := by decide

theorem f2_sup_split_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b => allTriplesF2.all fun v =>
      (!inSub3F2 (sub3Sup a b) v) ||
      (let u := findWitnessF2 (fun u => inSub3F2 a u && inSub3F2 b (subT v u))
       inSub3F2 a u && inSub3F2 b (subT v u))) = true := by decide

theorem f2_inf_eq_le_all :
    (sub3ElemsF2.all fun a => sub3ElemsF2.all fun b =>
      decide (decide (sub3Inf a b = a) = sub3LeBool a b)) = true := by decide

theorem sub3F2_toSubspace_inj {a b : Sub3 F2}
    (h : sub3ToSubspace a = sub3ToSubspace b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have h1 := forall_of_list_all (forall_of_list_all f2_sep_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b)
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h1
    rcases h1 with heq | hne
    · exact heq
    · let u := findWitnessF2 (fun u => inSub3F2 a u != inSub3F2 b u)
      have hmem : (sub3ToSubspace a).mem (ofTriple u) ↔ (sub3ToSubspace b).mem (ofTriple u) := by
        rw [h]
      rw [inSub3F2_iff, inSub3F2_iff, toTriple_ofTriple] at hmem
      have heq_b : inSub3F2 a u = inSub3F2 b u := Bool.eq_iff_iff.mpr hmem
      exact False.elim (hne heq_b)

theorem sub3F2_toSubspace_inf (a b : Sub3 F2) :
    sub3ToSubspace (sub3Inf a b) = sub3ToSubspace a ⊓ sub3ToSubspace b := by
  apply Subspace.ext
  intro v
  show (sub3ToSubspace (sub3Inf a b)).mem v ↔ (sub3ToSubspace a).mem v ∧ (sub3ToSubspace b).mem v
  have hall := forall_of_list_all
    (forall_of_list_all (forall_of_list_all f2_inf_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b))
    (toTriple v) (mem_allTriplesF2 (toTriple v))
  simp only [decide_eq_true_eq] at hall
  rw [inSub3F2_iff, inSub3F2_iff, inSub3F2_iff, hall, Bool.and_eq_true]

theorem sub3F2_toSubspace_sup (a b : Sub3 F2) :
    sub3ToSubspace (sub3Sup a b) = sub3ToSubspace a ⊔ sub3ToSubspace b := by
  apply Lattice.le_antisymm
  · intro v hv
    rw [inSub3F2_iff] at hv
    have hsp := forall_of_list_all
      (forall_of_list_all (forall_of_list_all f2_sup_split_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b))
      (toTriple v) (mem_allTriplesF2 (toTriple v))
    rw [hv] at hsp
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsp
    let uT := findWitnessF2 (fun u => inSub3F2 a u && inSub3F2 b (subT (toTriple v) u))
    let u := ofTriple uT
    let w := v -₉ u
    have hu : (sub3ToSubspace a).mem u := by
      rw [inSub3F2_iff, toTriple_ofTriple]; exact hsp.1
    have hwT : toTriple w = subT (toTriple v) uT := by
      unfold w u gsub toTriple subT ofTriple
      rfl
    have hw : (sub3ToSubspace b).mem w := by
      rw [inSub3F2_iff, hwT]; exact hsp.2
    have hsum : v = u + w := by
      unfold w gsub
      calc v = v + 0 := (acg_add_zero v).symm
        _ = v + (u + (-u)) := by rw [acg_add_neg_cancel]
        _ = u + (v + (-u)) := by
          rw [← AddCommGroup.add_assoc, AddCommGroup.add_comm v u, AddCommGroup.add_assoc]
    exact ⟨u, w, hu, hw, hsum⟩
  · apply Lattice.sup_le
    · intro v hv
      rw [inSub3F2_iff] at hv ⊢
      have hl := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f2_sup_le_l_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b))
        (toTriple v) (mem_allTriplesF2 (toTriple v))
      rw [hv] at hl
      simpa using hl
    · intro v hv
      rw [inSub3F2_iff] at hv ⊢
      have hr := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f2_sup_le_r_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b))
        (toTriple v) (mem_allTriplesF2 (toTriple v))
      rw [hv] at hr
      simpa using hr

theorem sub3F2_le_iff (a b : Sub3 F2) :
    sub3Le a b ↔ sub3ToSubspace a ≼ sub3ToSubspace b := by
  have h1 := forall_of_list_all (forall_of_list_all f2_inf_eq_le_all a (mem_sub3ElemsF2 a)) b (mem_sub3ElemsF2 b)
  simp only [decide_eq_true_eq] at h1
  have h2 : sub3Inf a b = a ↔ sub3Le a b := by
    unfold sub3Le
    rw [← h1, decide_eq_true_eq]
  rw [← h2, ← inf_eq_left, ← sub3F2_toSubspace_inf]
  constructor
  · exact fun h => congrArg sub3ToSubspace h
  · exact fun h => sub3F2_toSubspace_inj h

instance latticeSub3F2 : Lattice (Sub3 F2) where
  le := sub3Le
  inf := sub3Inf
  sup := sub3Sup
  le_refl a := (sub3F2_le_iff a a).mpr (Lattice.le_refl _)
  le_trans h1 h2 := (sub3F2_le_iff _ _).mpr
    (Lattice.le_trans ((sub3F2_le_iff _ _).mp h1) ((sub3F2_le_iff _ _).mp h2))
  le_antisymm h1 h2 := sub3F2_toSubspace_inj
    (Lattice.le_antisymm ((sub3F2_le_iff _ _).mp h1) ((sub3F2_le_iff _ _).mp h2))
  inf_le_left a b := (sub3F2_le_iff _ _).mpr (by rw [sub3F2_toSubspace_inf]; exact Lattice.inf_le_left _ _)
  inf_le_right a b := (sub3F2_le_iff _ _).mpr (by rw [sub3F2_toSubspace_inf]; exact Lattice.inf_le_right _ _)
  le_inf h1 h2 := (sub3F2_le_iff _ _).mpr
    (by rw [sub3F2_toSubspace_inf]; exact Lattice.le_inf ((sub3F2_le_iff _ _).mp h1) ((sub3F2_le_iff _ _).mp h2))
  le_sup_left a b := (sub3F2_le_iff _ _).mpr (by rw [sub3F2_toSubspace_sup]; exact Lattice.le_sup_left _ _)
  le_sup_right a b := (sub3F2_le_iff _ _).mpr (by rw [sub3F2_toSubspace_sup]; exact Lattice.le_sup_right _ _)
  sup_le h1 h2 := (sub3F2_le_iff _ _).mpr
    (by rw [sub3F2_toSubspace_sup]; exact Lattice.sup_le ((sub3F2_le_iff _ _).mp h1) ((sub3F2_le_iff _ _).mp h2))

theorem sub3F2_isModular : IsModularLattice (Sub3 F2) := by
  intro x y z hzx
  apply sub3F2_toSubspace_inj
  change sub3ToSubspace (sub3Inf x (sub3Sup y z)) = sub3ToSubspace (sub3Sup (sub3Inf x y) z)
  rw [sub3F2_toSubspace_inf, sub3F2_toSubspace_sup, sub3F2_toSubspace_sup, sub3F2_toSubspace_inf]
  exact subspace_isModular _ _ _ ((sub3F2_le_iff z x).mp hzx)

/-- Positive sanity check: `Sub3 F2` embeds into `Subspace F2 (FinVec F2 3)`. -/
def sub3F2CanonicalEmbedding : LatticeEmbedding (Sub3 F2) (Subspace F2 (FinVec F2 3)) where
  toFun := sub3ToSubspace
  inj := sub3F2_toSubspace_inj
  map_inf := sub3F2_toSubspace_inf
  map_sup := sub3F2_toSubspace_sup

/-! ### 3B. Lattice and Modularity Instances for `Sub3 F3` (28 elements) -/

def sub3ElemsF3 : List (Sub3 F3) := sub3Elems [F3.f0, F3.f1, F3.f2]

theorem mem_sub3ElemsF3 (s : Sub3 F3) : s ∈ sub3ElemsF3 := by
  cases s with
  | bot => decide
  | top => decide
  | line p => cases p with | e0 b c => cases b <;> cases c <;> decide | e1 c => cases c <;> decide | e2 => decide
  | plane n => cases n with | e0 b c => cases b <;> cases c <;> decide | e1 c => cases c <;> decide | e2 => decide

theorem sub3F3_hasCardinality : HasCardinality (Sub3 F3) 28 :=
  ⟨sub3ElemsF3, nodup_of_nodupBool (by decide), mem_sub3ElemsF3, rfl⟩

def inSub3F3 (s : Sub3 F3) (v : Triple F3) : Bool :=
  match s with
  | .bot => decide (v = (.f0, .f0, .f0))
  | .line p =>
    let u := nvTriple p
    decide (v = smulT .f0 u) || decide (v = smulT .f1 u) || decide (v = smulT .f2 u)
  | .plane n => decide (dotT (nvTriple n) v = .f0)
  | .top => true

theorem inSub3F3_iff (s : Sub3 F3) (v : FinVec F3 3) :
    (sub3ToSubspace s).mem v ↔ inSub3F3 s (toTriple v) = true := by
  cases s with
  | bot =>
    simp only [sub3ToSubspace, inSub3F3, decide_eq_true_eq]
    constructor
    · intro h; subst h; rfl
    · intro h
      calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
        _ = ofTriple (.f0, .f0, .f0) := by rw [h]
        _ = 0 := by funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
  | line p =>
    simp only [sub3ToSubspace, inSub3F3, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨t, rfl⟩
      cases t with
      | f0 => exact Or.inl (Or.inl rfl)
      | f1 => exact Or.inl (Or.inr rfl)
      | f2 => exact Or.inr rfl
    · intro h
      rcases h with (h0 | h1) | h2
      · refine ⟨.f0, ?_⟩
        calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
          _ = ofTriple (smulT .f0 (nvTriple p)) := by rw [h0]
          _ = (.f0 : F3) • ofTriple (nvTriple p) := by
            funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
      · refine ⟨.f1, ?_⟩
        calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
          _ = ofTriple (smulT .f1 (nvTriple p)) := by rw [h1]
          _ = (.f1 : F3) • ofTriple (nvTriple p) := by
            funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
      · refine ⟨.f2, ?_⟩
        calc v = ofTriple (toTriple v) := (ofTriple_toTriple v).symm
          _ = ofTriple (smulT .f2 (nvTriple p)) := by rw [h2]
          _ = (.f2 : F3) • ofTriple (nvTriple p) := by
            funext ⟨i, hi⟩; match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl
  | plane n =>
    simp only [sub3ToSubspace, inSub3F3, decide_eq_true_eq]
    rfl
  | top =>
    simp only [sub3ToSubspace, inSub3F3]

def allTriplesF3 : List (Triple F3) :=
  let el := [F3.f0, F3.f1, F3.f2]
  el.flatMap fun x => el.flatMap fun y => el.map fun z => (x, y, z)

theorem mem_allTriplesF3 (u : Triple F3) : u ∈ allTriplesF3 := by
  rcases u with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

def findWitnessF3 (p : Triple F3 → Bool) : Triple F3 :=
  match allTriplesF3.find? p with
  | some u => u
  | none => (.f0, .f0, .f0)

def sepPlaneVecF3 (n m : NormVec3 F3) : Triple F3 :=
  let tn := nvTriple n
  let tm := nvTriple m
  let d1 : Triple F3 := (-tn.2.1, tn.1, .f0)
  let d2 : Triple F3 := (-tn.2.2, .f0, tn.1)
  let d3 : Triple F3 := (.f0, -tn.2.2, tn.2.1)
  if dotT tm d1 != .f0 then d1
  else if dotT tm d2 != .f0 then d2
  else d3

def findSplitF3 (a b : Sub3 F3) (v : Triple F3) : Triple F3 :=
  match a, b with
  | .bot, _ => (.f0, .f0, .f0)
  | _, .bot => v
  | .top, _ => v
  | _, .top => (.f0, .f0, .f0)
  | .line p, .plane m =>
    let up := nvTriple p
    let dm := dotT (nvTriple m) up
    if dm == .f0 then (.f0, .f0, .f0)
    else smulT (dotT (nvTriple m) v * dm⁻¹) up
  | .plane n, .line q =>
    let uq := nvTriple q
    let dn := dotT (nvTriple n) uq
    if dn == .f0 then v
    else subT v (smulT (dotT (nvTriple n) v * dn⁻¹) uq)
  | .line p, .line q =>
    let u0 := nvTriple p
    if inSub3F3 (.line q) v then (.f0, .f0, .f0)
    else if inSub3F3 (.line q) (subT v u0) then u0
    else smulT .f2 u0
  | .plane n, .plane m =>
    if n = m then v
    else
      let d := sepPlaneVecF3 n m
      let dm := dotT (nvTriple m) d
      smulT (dotT (nvTriple m) v * dm⁻¹) d

def normVecsF3 : List (NormVec3 F3) := normVec3Elems [F3.f0, F3.f1, F3.f2]

theorem mem_normVecsF3 (p : NormVec3 F3) : p ∈ normVecsF3 := by
  cases p with
  | e0 b c => cases b <;> cases c <;> decide
  | e1 c => cases c <;> decide
  | e2 => decide

theorem f3_sep_all :
    (sub3ElemsF3.all fun a => sub3ElemsF3.all fun b =>
      decide (a = b) ||
      (let u := findWitnessF3 (fun u => inSub3F3 a u != inSub3F3 b u)
       inSub3F3 a u != inSub3F3 b u)) = true := by decide

theorem f3_inf_all :
    (sub3ElemsF3.all fun a => sub3ElemsF3.all fun b => allTriplesF3.all fun u =>
      decide (inSub3F3 (sub3Inf a b) u = (inSub3F3 a u && inSub3F3 b u))) = true := by decide

theorem f3_sup_le_l_all :
    (sub3ElemsF3.all fun a => sub3ElemsF3.all fun b => allTriplesF3.all fun u =>
      (!inSub3F3 a u) || inSub3F3 (sub3Sup a b) u) = true := by decide

theorem f3_sup_le_r_all :
    (sub3ElemsF3.all fun a => sub3ElemsF3.all fun b => allTriplesF3.all fun u =>
      (!inSub3F3 b u) || inSub3F3 (sub3Sup a b) u) = true := by decide

theorem f3_sup_split_ll :
    (normVecsF3.all fun p => normVecsF3.all fun q => allTriplesF3.all fun v =>
      (!inSub3F3 (sub3Sup (.line p) (.line q)) v) ||
      (let u := findSplitF3 (.line p) (.line q) v
       inSub3F3 (.line p) u && inSub3F3 (.line q) (subT v u))) = true := by decide

theorem f3_sup_split_lp :
    (normVecsF3.all fun p => normVecsF3.all fun m => allTriplesF3.all fun v =>
      (!inSub3F3 (sub3Sup (.line p) (.plane m)) v) ||
      (let u := findSplitF3 (.line p) (.plane m) v
       inSub3F3 (.line p) u && inSub3F3 (.plane m) (subT v u))) = true := by decide

theorem f3_sup_split_pl :
    (normVecsF3.all fun n => normVecsF3.all fun q => allTriplesF3.all fun v =>
      (!inSub3F3 (sub3Sup (.plane n) (.line q)) v) ||
      (let u := findSplitF3 (.plane n) (.line q) v
       inSub3F3 (.plane n) u && inSub3F3 (.line q) (subT v u))) = true := by decide

theorem f3_sup_split_pp :
    (normVecsF3.all fun n => normVecsF3.all fun m => allTriplesF3.all fun v =>
      (!inSub3F3 (sub3Sup (.plane n) (.plane m)) v) ||
      (let u := findSplitF3 (.plane n) (.plane m) v
       inSub3F3 (.plane n) u && inSub3F3 (.plane m) (subT v u))) = true := by decide

theorem inSub3F3_zero (s : Sub3 F3) : inSub3F3 s (.f0, .f0, .f0) = true := by
  have hz : (.f0, .f0, .f0) = toTriple (0 : FinVec F3 3) := rfl
  rw [hz, ← inSub3F3_iff]
  exact (sub3ToSubspace s).zero_mem

theorem f3_sup_split_pointwise (a b : Sub3 F3) (v : Triple F3)
    (hv : inSub3F3 (sub3Sup a b) v = true) :
    let u := findSplitF3 a b v
    inSub3F3 a u = true ∧ inSub3F3 b (subT v u) = true := by
  have sub_zero_f3 : subT v (.f0, .f0, .f0) = v := by
    rcases v with ⟨x, y, z⟩; cases x <;> cases y <;> cases z <;> rfl
  have sub_self_f3 : subT v v = (.f0, .f0, .f0) := by
    rcases v with ⟨x, y, z⟩; cases x <;> cases y <;> cases z <;> rfl
  cases a with
  | bot =>
    cases b <;> (dsimp [findSplitF3]; rw [sub_zero_f3]; exact ⟨rfl, hv⟩)
  | top =>
    cases b <;> (dsimp [findSplitF3]; rw [sub_self_f3]; exact ⟨rfl, inSub3F3_zero _⟩)
  | line p =>
    cases b with
    | bot => dsimp [findSplitF3]; rw [sub_self_f3]; exact ⟨hv, rfl⟩
    | top => dsimp [findSplitF3]; rw [sub_zero_f3]; exact ⟨inSub3F3_zero _, rfl⟩
    | line q =>
      have h := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_split_ll p (mem_normVecsF3 p)) q (mem_normVecsF3 q))
        v (mem_allTriplesF3 v)
      rw [hv] at h
      simpa using h
    | plane m =>
      have h := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_split_lp p (mem_normVecsF3 p)) m (mem_normVecsF3 m))
        v (mem_allTriplesF3 v)
      rw [hv] at h
      simpa using h
  | plane n =>
    cases b with
    | bot => dsimp [findSplitF3]; rw [sub_self_f3]; exact ⟨hv, rfl⟩
    | top => dsimp [findSplitF3]; rw [sub_zero_f3]; exact ⟨inSub3F3_zero _, rfl⟩
    | line q =>
      have h := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_split_pl n (mem_normVecsF3 n)) q (mem_normVecsF3 q))
        v (mem_allTriplesF3 v)
      rw [hv] at h
      simpa using h
    | plane m =>
      have h := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_split_pp n (mem_normVecsF3 n)) m (mem_normVecsF3 m))
        v (mem_allTriplesF3 v)
      rw [hv] at h
      simpa using h

theorem f3_inf_eq_le_all :
    (sub3ElemsF3.all fun a => sub3ElemsF3.all fun b =>
      decide (decide (sub3Inf a b = a) = sub3LeBool a b)) = true := by decide

theorem sub3F3_toSubspace_inj {a b : Sub3 F3}
    (h : sub3ToSubspace a = sub3ToSubspace b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have h1 := forall_of_list_all (forall_of_list_all f3_sep_all a (mem_sub3ElemsF3 a)) b (mem_sub3ElemsF3 b)
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h1
    rcases h1 with heq | hne
    · exact heq
    · let u := findWitnessF3 (fun u => inSub3F3 a u != inSub3F3 b u)
      have hmem : (sub3ToSubspace a).mem (ofTriple u) ↔ (sub3ToSubspace b).mem (ofTriple u) := by
        rw [h]
      rw [inSub3F3_iff, inSub3F3_iff, toTriple_ofTriple] at hmem
      have heq_b : inSub3F3 a u = inSub3F3 b u := Bool.eq_iff_iff.mpr hmem
      exact False.elim (hne heq_b)

theorem sub3F3_toSubspace_inf (a b : Sub3 F3) :
    sub3ToSubspace (sub3Inf a b) = sub3ToSubspace a ⊓ sub3ToSubspace b := by
  apply Subspace.ext
  intro v
  show (sub3ToSubspace (sub3Inf a b)).mem v ↔ (sub3ToSubspace a).mem v ∧ (sub3ToSubspace b).mem v
  have hall := forall_of_list_all
    (forall_of_list_all (forall_of_list_all f3_inf_all a (mem_sub3ElemsF3 a)) b (mem_sub3ElemsF3 b))
    (toTriple v) (mem_allTriplesF3 (toTriple v))
  simp only [decide_eq_true_eq] at hall
  rw [inSub3F3_iff, inSub3F3_iff, inSub3F3_iff, hall, Bool.and_eq_true]

theorem sub3F3_toSubspace_sup (a b : Sub3 F3) :
    sub3ToSubspace (sub3Sup a b) = sub3ToSubspace a ⊔ sub3ToSubspace b := by
  apply Lattice.le_antisymm
  · intro v hv
    rw [inSub3F3_iff] at hv
    have hsp := f3_sup_split_pointwise a b (toTriple v) hv
    dsimp only at hsp
    let uT := findSplitF3 a b (toTriple v)
    let u := ofTriple uT
    let w := v -₉ u
    have hu : (sub3ToSubspace a).mem u := by
      rw [inSub3F3_iff, toTriple_ofTriple]; exact hsp.1
    have hwT : toTriple w = subT (toTriple v) uT := by
      unfold w u gsub toTriple subT ofTriple
      rfl
    have hw : (sub3ToSubspace b).mem w := by
      rw [inSub3F3_iff, hwT]; exact hsp.2
    have hsum : v = u + w := by
      unfold w gsub
      calc v = v + 0 := (acg_add_zero v).symm
        _ = v + (u + (-u)) := by rw [acg_add_neg_cancel]
        _ = u + (v + (-u)) := by
          rw [← AddCommGroup.add_assoc, AddCommGroup.add_comm v u, AddCommGroup.add_assoc]
    exact ⟨u, w, hu, hw, hsum⟩
  · apply Lattice.sup_le
    · intro v hv
      rw [inSub3F3_iff] at hv ⊢
      have hl := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_le_l_all a (mem_sub3ElemsF3 a)) b (mem_sub3ElemsF3 b))
        (toTriple v) (mem_allTriplesF3 (toTriple v))
      rw [hv] at hl
      simpa using hl
    · intro v hv
      rw [inSub3F3_iff] at hv ⊢
      have hr := forall_of_list_all
        (forall_of_list_all (forall_of_list_all f3_sup_le_r_all a (mem_sub3ElemsF3 a)) b (mem_sub3ElemsF3 b))
        (toTriple v) (mem_allTriplesF3 (toTriple v))
      rw [hv] at hr
      simpa using hr

theorem sub3F3_le_iff (a b : Sub3 F3) :
    sub3Le a b ↔ sub3ToSubspace a ≼ sub3ToSubspace b := by
  have h1 := forall_of_list_all (forall_of_list_all f3_inf_eq_le_all a (mem_sub3ElemsF3 a)) b (mem_sub3ElemsF3 b)
  simp only [decide_eq_true_eq] at h1
  have h2 : sub3Inf a b = a ↔ sub3Le a b := by
    unfold sub3Le
    rw [← h1, decide_eq_true_eq]
  rw [← h2, ← inf_eq_left, ← sub3F3_toSubspace_inf]
  constructor
  · exact fun h => congrArg sub3ToSubspace h
  · exact fun h => sub3F3_toSubspace_inj h

instance latticeSub3F3 : Lattice (Sub3 F3) where
  le := sub3Le
  inf := sub3Inf
  sup := sub3Sup
  le_refl a := (sub3F3_le_iff a a).mpr (Lattice.le_refl _)
  le_trans h1 h2 := (sub3F3_le_iff _ _).mpr
    (Lattice.le_trans ((sub3F3_le_iff _ _).mp h1) ((sub3F3_le_iff _ _).mp h2))
  le_antisymm h1 h2 := sub3F3_toSubspace_inj
    (Lattice.le_antisymm ((sub3F3_le_iff _ _).mp h1) ((sub3F3_le_iff _ _).mp h2))
  inf_le_left a b := (sub3F3_le_iff _ _).mpr (by rw [sub3F3_toSubspace_inf]; exact Lattice.inf_le_left _ _)
  inf_le_right a b := (sub3F3_le_iff _ _).mpr (by rw [sub3F3_toSubspace_inf]; exact Lattice.inf_le_right _ _)
  le_inf h1 h2 := (sub3F3_le_iff _ _).mpr
    (by rw [sub3F3_toSubspace_inf]; exact Lattice.le_inf ((sub3F3_le_iff _ _).mp h1) ((sub3F3_le_iff _ _).mp h2))
  le_sup_left a b := (sub3F3_le_iff _ _).mpr (by rw [sub3F3_toSubspace_sup]; exact Lattice.le_sup_left _ _)
  le_sup_right a b := (sub3F3_le_iff _ _).mpr (by rw [sub3F3_toSubspace_sup]; exact Lattice.le_sup_right _ _)
  sup_le h1 h2 := (sub3F3_le_iff _ _).mpr
    (by rw [sub3F3_toSubspace_sup]; exact Lattice.sup_le ((sub3F3_le_iff _ _).mp h1) ((sub3F3_le_iff _ _).mp h2))

theorem sub3F3_isModular : IsModularLattice (Sub3 F3) := by
  intro x y z hzx
  apply sub3F3_toSubspace_inj
  change sub3ToSubspace (sub3Inf x (sub3Sup y z)) = sub3ToSubspace (sub3Sup (sub3Inf x y) z)
  rw [sub3F3_toSubspace_inf, sub3F3_toSubspace_sup, sub3F3_toSubspace_sup, sub3F3_toSubspace_inf]
  exact subspace_isModular _ _ _ ((sub3F3_le_iff z x).mp hzx)

/-- Positive sanity check: `Sub3 F3` embeds into `Subspace F3 (FinVec F3 3)`. -/
def sub3F3CanonicalEmbedding : LatticeEmbedding (Sub3 F3) (Subspace F3 (FinVec F3 3)) where
  toFun := sub3ToSubspace
  inj := sub3F3_toSubspace_inj
  map_inf := sub3F3_toSubspace_inf
  map_sup := sub3F3_toSubspace_sup

/-! ## 4. Characteristic-Forcing Theorems for Arbitrary Subspace Lattice Embeddings -/

section CharacteristicForcing
variable {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V]

def modEq (W0 : Subspace K V) (x y : V) : Prop :=
  W0.mem (x -₉ y)

theorem mod_refl (W0 : Subspace K V) (x : V) : modEq W0 x x := by
  unfold modEq
  rw [gsub_self]
  exact W0.zero_mem

theorem mod_symm {W0 : Subspace K V} {x y : V} (h : modEq W0 x y) : modEq W0 y x := by
  unfold modEq at h ⊢
  rw [← neg_gsub]
  exact W0.neg_mem h

theorem mod_trans {W0 : Subspace K V} {x y z : V}
    (h1 : modEq W0 x y) (h2 : modEq W0 y z) : modEq W0 x z := by
  unfold modEq at h1 h2 ⊢
  rw [← gsub_add_gsub x y z]
  exact W0.add_mem h1 h2

theorem mod_add {W0 : Subspace K V} {x1 y1 x2 y2 : V}
    (h1 : modEq W0 x1 y1) (h2 : modEq W0 x2 y2) : modEq W0 (x1 + x2) (y1 + y2) := by
  unfold modEq at h1 h2 ⊢
  rw [gsub_add_distrib]
  exact W0.add_mem h1 h2

theorem mod_zero_iff {W0 : Subspace K V} {x : V} : modEq W0 x 0 ↔ W0.mem x := by
  unfold modEq
  rw [gsub_zero]

open Classical in
theorem not_le_exists_mem {A B : Subspace K V} (h : ¬ (A ≼ B)) :
    ∃ v : V, A.mem v ∧ ¬ B.mem v := by
  by_cases hex : ∃ v : V, A.mem v ∧ ¬ B.mem v
  · exact hex
  · exfalso
    apply h
    intro v hvA
    by_cases hvB : B.mem v
    · exact hvB
    · exact False.elim (hex ⟨v, hvA, hvB⟩)

theorem frame_direct_sum_mod {W0 A1 A2 A3 : Subspace K V}
    (h01 : W0 ≼ A1) (h02 : W0 ≼ A2)
    (hind1 : A1 ⊓ (A2 ⊔ A3) = W0)
    (hind2 : A2 ⊓ (A1 ⊔ A3) = W0)
    (hind3 : A3 ⊓ (A1 ⊔ A2) = W0)
    {x1 x2 x3 : V} (hx1 : A1.mem x1) (hx2 : A2.mem x2) (hx3 : A3.mem x3)
    (hsum : W0.mem ((x1 + x2) + x3)) :
    W0.mem x1 ∧ W0.mem x2 ∧ W0.mem x3 := by
  have hw1 : W0.mem x1 := by
    have h23 : (A2 ⊔ A3).mem (x2 + x3) := ⟨x2, x3, hx2, hx3, rfl⟩
    have hs23 : (A2 ⊔ A3).mem ((x1 + x2) + x3) :=
      Lattice.le_trans h02 (Lattice.le_sup_left A2 A3) _ hsum
    have hsub : (A2 ⊔ A3).mem (((x1 + x2) + x3) -₉ (x2 + x3)) := (A2 ⊔ A3).sub_mem hs23 h23
    have heq : ((x1 + x2) + x3) -₉ (x2 + x3) = x1 := by
      rw [AddCommGroup.add_assoc x1 x2 x3, add_gsub_cancel]
    rw [heq] at hsub
    have hinf : (A1 ⊓ (A2 ⊔ A3)).mem x1 := ⟨hx1, hsub⟩
    rw [hind1] at hinf
    exact hinf
  have hw2 : W0.mem x2 := by
    have h13 : (A1 ⊔ A3).mem (x1 + x3) := ⟨x1, x3, hx1, hx3, rfl⟩
    have hs13 : (A1 ⊔ A3).mem ((x2 + x1) + x3) := by
      rw [AddCommGroup.add_comm x2 x1]
      exact Lattice.le_trans h01 (Lattice.le_sup_left A1 A3) _ hsum
    have hsub : (A1 ⊔ A3).mem (((x2 + x1) + x3) -₉ (x1 + x3)) := (A1 ⊔ A3).sub_mem hs13 h13
    have heq : ((x2 + x1) + x3) -₉ (x1 + x3) = x2 := by
      rw [AddCommGroup.add_assoc x2 x1 x3, add_gsub_cancel]
    rw [heq] at hsub
    have hinf : (A2 ⊓ (A1 ⊔ A3)).mem x2 := ⟨hx2, hsub⟩
    rw [hind2] at hinf
    exact hinf
  have hw3 : W0.mem x3 := by
    have h12 : (A1 ⊔ A2).mem (x1 + x2) := ⟨x1, x2, hx1, hx2, rfl⟩
    have hs12 : (A1 ⊔ A2).mem (x3 + (x1 + x2)) := by
      rw [AddCommGroup.add_comm x3 (x1 + x2)]
      exact Lattice.le_trans h01 (Lattice.le_sup_left A1 A2) _ hsum
    have hsub : (A1 ⊔ A2).mem ((x3 + (x1 + x2)) -₉ (x1 + x2)) := (A1 ⊔ A2).sub_mem hs12 h12
    rw [add_gsub_cancel] at hsub
    have hinf : (A3 ⊓ (A1 ⊔ A2)).mem x3 := ⟨hx3, hsub⟩
    rw [hind3] at hinf
    exact hinf
  exact ⟨hw1, hw2, hw3⟩

theorem frame_eq_mod {W0 A1 A2 A3 : Subspace K V}
    (h01 : W0 ≼ A1) (h02 : W0 ≼ A2)
    (hind1 : A1 ⊓ (A2 ⊔ A3) = W0)
    (hind2 : A2 ⊓ (A1 ⊔ A3) = W0)
    (hind3 : A3 ⊓ (A1 ⊔ A2) = W0)
    {x1 x2 x3 y1 y2 y3 : V}
    (hx1 : A1.mem x1) (hx2 : A2.mem x2) (hx3 : A3.mem x3)
    (hy1 : A1.mem y1) (hy2 : A2.mem y2) (hy3 : A3.mem y3)
    (heq : (x1 + x2) + x3 = (y1 + y2) + y3) :
    modEq W0 x1 y1 ∧ modEq W0 x2 y2 ∧ modEq W0 x3 y3 := by
  have hsum : W0.mem (((x1 -₉ y1) + (x2 -₉ y2)) + (x3 -₉ y3)) := by
    rw [gsub_sum3, heq, gsub_self]
    exact W0.zero_mem
  exact frame_direct_sum_mod h01 h02 hind1 hind2 hind3
    (A1.sub_mem hx1 hy1) (A2.sub_mem hx2 hy2) (A3.sub_mem hx3 hy3) hsum

theorem frame_D_from_1 {W0 A1 A2 A3 D : Subspace K V}
    (h01 : W0 ≼ A1) (h02 : W0 ≼ A2) (h0D : W0 ≼ D)
    (hind1 : A1 ⊓ (A2 ⊔ A3) = W0)
    (hind2 : A2 ⊓ (A1 ⊔ A3) = W0)
    (hind3 : A3 ⊓ (A1 ⊔ A2) = W0)
    (hD1 : D ⊓ (A2 ⊔ A3) = W0)
    {x1 x2 x3 y1 y2 y3 : V}
    (hx2 : A2.mem x2) (hx3 : A3.mem x3)
    (hy2 : A2.mem y2) (hy3 : A3.mem y3)
    (hDx : D.mem ((x1 + x2) + x3)) (hDy : D.mem ((y1 + y2) + y3))
    (hm1 : modEq W0 x1 y1) :
    modEq W0 x2 y2 ∧ modEq W0 x3 y3 := by
  have hDdiff : D.mem (((x1 -₉ y1) + (x2 -₉ y2)) + (x3 -₉ y3)) := by
    rw [gsub_sum3]
    exact D.sub_mem hDx hDy
  have hD1mem : D.mem (x1 -₉ y1) := h0D _ hm1
  have hD23 : D.mem ((x2 -₉ y2) + (x3 -₉ y3)) := by
    have hsub : D.mem ((((x1 -₉ y1) + (x2 -₉ y2)) + (x3 -₉ y3)) -₉ (x1 -₉ y1)) :=
      D.sub_mem hDdiff hD1mem
    have heq : (((x1 -₉ y1) + (x2 -₉ y2)) + (x3 -₉ y3)) -₉ (x1 -₉ y1) = (x2 -₉ y2) + (x3 -₉ y3) := by
      rw [AddCommGroup.add_assoc (x1 -₉ y1), AddCommGroup.add_comm (x1 -₉ y1), add_gsub_cancel]
    rw [heq] at hsub
    exact hsub
  have hA23 : (A2 ⊔ A3).mem ((x2 -₉ y2) + (x3 -₉ y3)) :=
    ⟨x2 -₉ y2, x3 -₉ y3, A2.sub_mem hx2 hy2, A3.sub_mem hx3 hy3, rfl⟩
  have hW23 : W0.mem ((x2 -₉ y2) + (x3 -₉ y3)) := by
    have hinf : (D ⊓ (A2 ⊔ A3)).mem ((x2 -₉ y2) + (x3 -₉ y3)) := ⟨hD23, hA23⟩
    rw [hD1] at hinf
    exact hinf
  have hWsum : W0.mem ((0 + (x2 -₉ y2)) + (x3 -₉ y3)) := by
    rw [acg_zero_add]
    exact hW23
  have hds := frame_direct_sum_mod h01 h02 hind1 hind2 hind3
    A1.zero_mem (A2.sub_mem hx2 hy2) (A3.sub_mem hx3 hy3) hWsum
  exact ⟨hds.2.1, hds.2.2⟩

theorem frame_D_from_2 {W0 A1 A2 A3 D : Subspace K V}
    (h01 : W0 ≼ A1) (h02 : W0 ≼ A2) (h0D : W0 ≼ D)
    (hind1 : A1 ⊓ (A2 ⊔ A3) = W0)
    (hind2 : A2 ⊓ (A1 ⊔ A3) = W0)
    (hind3 : A3 ⊓ (A1 ⊔ A2) = W0)
    (hD2 : D ⊓ (A1 ⊔ A3) = W0)
    {x1 x2 x3 y1 y2 y3 : V}
    (hx1 : A1.mem x1) (hx3 : A3.mem x3)
    (hy1 : A1.mem y1) (hy3 : A3.mem y3)
    (hDx : D.mem ((x1 + x2) + x3)) (hDy : D.mem ((y1 + y2) + y3))
    (hm2 : modEq W0 x2 y2) :
    modEq W0 x1 y1 ∧ modEq W0 x3 y3 := by
  have hind3' : A3 ⊓ (A2 ⊔ A1) = W0 := by rw [sup_comm A2 A1]; exact hind3
  have hDx' : D.mem ((x2 + x1) + x3) := by rw [AddCommGroup.add_comm x2 x1]; exact hDx
  have hDy' : D.mem ((y2 + y1) + y3) := by rw [AddCommGroup.add_comm y2 y1]; exact hDy
  exact frame_D_from_1 h02 h01 h0D hind2 hind1 hind3' hD2
    hx1 hx3 hy1 hy3 hDx' hDy' hm2

theorem frame_D_from_3 {W0 A1 A2 A3 D : Subspace K V}
    (h01 : W0 ≼ A1) (h03 : W0 ≼ A3) (h0D : W0 ≼ D)
    (hind1 : A1 ⊓ (A2 ⊔ A3) = W0)
    (hind2 : A2 ⊓ (A1 ⊔ A3) = W0)
    (hind3 : A3 ⊓ (A1 ⊔ A2) = W0)
    (hD3 : D ⊓ (A1 ⊔ A2) = W0)
    {x1 x2 x3 y1 y2 y3 : V}
    (hx1 : A1.mem x1) (hx2 : A2.mem x2)
    (hy1 : A1.mem y1) (hy2 : A2.mem y2)
    (hDx : D.mem ((x1 + x2) + x3)) (hDy : D.mem ((y1 + y2) + y3))
    (hm3 : modEq W0 x3 y3) :
    modEq W0 x1 y1 ∧ modEq W0 x2 y2 := by
  have hind1' : A1 ⊓ (A3 ⊔ A2) = W0 := by rw [sup_comm A3 A2]; exact hind1
  have hind2' : A2 ⊓ (A3 ⊔ A1) = W0 := by rw [sup_comm A3 A1]; exact hind2
  have rearrange312 : ∀ a b c : V, (c + a) + b = (a + b) + c := by
    intro a b c
    rw [AddCommGroup.add_assoc c a b, AddCommGroup.add_comm c (a + b)]
  have hDx' : D.mem ((x3 + x1) + x2) := by rw [rearrange312]; exact hDx
  have hDy' : D.mem ((y3 + y1) + y2) := by rw [rearrange312]; exact hDy
  exact frame_D_from_1 h03 h01 h0D hind3 hind1' hind2' hD3
    hx1 hx2 hy1 hy2 hDx' hDy' hm3

theorem unpack_B12 {A1 A2 A3 D : Subspace K V} {y : V}
    (hy : ((A1 ⊔ A2) ⊓ (A3 ⊔ D)).mem y) :
    ∃ y1 y2 y3 : V, A1.mem y1 ∧ A2.mem y2 ∧ A3.mem y3 ∧
      y = y1 + y2 ∧ D.mem ((y1 + y2) + y3) := by
  rcases hy with ⟨⟨y1, y2, hy1, hy2, hy12⟩, ⟨a3, d, ha3, hd, hy3d⟩⟩
  refine ⟨y1, y2, -a3, hy1, hy2, A3.neg_mem ha3, hy12, ?_⟩
  have heq : (y1 + y2) + (-a3) = d := by
    rw [← hy12, hy3d, AddCommGroup.add_comm a3 d, AddCommGroup.add_assoc, acg_add_neg_cancel, acg_add_zero]
  rw [heq]
  exact hd

theorem unpack_B13 {A1 A2 A3 D : Subspace K V} {z : V}
    (hz : ((A1 ⊔ A3) ⊓ (A2 ⊔ D)).mem z) :
    ∃ z1 z2 z3 : V, A1.mem z1 ∧ A2.mem z2 ∧ A3.mem z3 ∧
      z = z1 + z3 ∧ D.mem ((z1 + z2) + z3) := by
  rcases hz with ⟨⟨z1, z3, hz1, hz3, hz13⟩, ⟨a2, d, ha2, hd, hz2d⟩⟩
  refine ⟨z1, -a2, z3, hz1, A2.neg_mem ha2, hz3, hz13, ?_⟩
  have heq : (z1 + (-a2)) + z3 = d := by
    calc
      (z1 + (-a2)) + z3 = (z1 + z3) + (-a2) := by
        rw [AddCommGroup.add_assoc, AddCommGroup.add_comm (-a2) z3, ← AddCommGroup.add_assoc]
      _ = (a2 + d) + (-a2) := by rw [← hz13, hz2d]
      _ = d := by rw [AddCommGroup.add_comm a2 d, AddCommGroup.add_assoc, acg_add_neg_cancel, acg_add_zero]
  rw [heq]
  exact hd

theorem unpack_B23 {A1 A2 A3 D : Subspace K V} {q : V}
    (hq : ((A2 ⊔ A3) ⊓ (A1 ⊔ D)).mem q) :
    ∃ q1 q2 q3 : V, A1.mem q1 ∧ A2.mem q2 ∧ A3.mem q3 ∧
      q = q2 + q3 ∧ D.mem ((q1 + q2) + q3) := by
  rcases hq with ⟨⟨q2, q3, hq2, hq3, hq23⟩, ⟨a1, d, ha1, hd, hq1d⟩⟩
  refine ⟨-a1, q2, q3, A1.neg_mem ha1, hq2, hq3, hq23, ?_⟩
  have heq : ((-a1) + q2) + q3 = d := by
    calc
      ((-a1) + q2) + q3 = (-a1) + (q2 + q3) := AddCommGroup.add_assoc _ _ _
      _ = (-a1) + (a1 + d) := by rw [← hq23, hq1d]
      _ = d := by rw [← AddCommGroup.add_assoc, acg_neg_add_cancel, acg_zero_add]
  rw [heq]
  exact hd

/-- Any lattice embedding of `Sub3 F2` into `Subspace K V` forces `1 + 1 = 0` in `K`. -/
theorem embed_sub3_F2_forces_char2
    (φ : LatticeEmbedding (Sub3 F2) (Subspace K V)) : (1 : K) + 1 = 0 := by
  let s0 : Sub3 F2 := .bot
  let s1 : Sub3 F2 := .line (.e0 .f0 .f0)
  let s2 : Sub3 F2 := .line (.e1 .f0)
  let s3 : Sub3 F2 := .line .e2
  let sd : Sub3 F2 := .line (.e0 .f1 .f1)
  let sb12 : Sub3 F2 := .line (.e0 .f1 .f0)
  let sb13 : Sub3 F2 := .line (.e0 .f0 .f1)
  let sb23 : Sub3 F2 := .line (.e1 .f1)

  let W0 := φ.toFun s0
  let A1 := φ.toFun s1
  let A2 := φ.toFun s2
  let A3 := φ.toFun s3
  let D  := φ.toFun sd
  let B12 := φ.toFun sb12
  let B13 := φ.toFun sb13
  let B23 := φ.toFun sb23

  have h01 : W0 ≼ A1 := φ.map_le_iff.mpr (rfl : s0 ≼ s1)
  have h02 : W0 ≼ A2 := φ.map_le_iff.mpr (rfl : s0 ≼ s2)
  have h03 : W0 ≼ A3 := φ.map_le_iff.mpr (rfl : s0 ≼ s3)
  have h0D : W0 ≼ D  := φ.map_le_iff.mpr (rfl : s0 ≼ sd)
  have hne1 : ¬ (A1 ≼ W0) := fun h => Bool.noConfusion (φ.map_le_iff.mp h)

  have hcov1 : A1 ≼ D ⊔ (A2 ⊔ A3) := by
    have hs : s1 ≼ sd ⊔ (s2 ⊔ s3) := rfl
    have hmap := φ.map_le_iff.mpr hs
    rw [φ.map_sup, φ.map_sup] at hmap
    exact hmap

  have hind1 : A1 ⊓ (A2 ⊔ A3) = W0 := by
    have hs : s1 ⊓ (s2 ⊔ s3) = s0 := rfl
    calc A1 ⊓ (A2 ⊔ A3) = φ.toFun (s1 ⊓ (s2 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hind2 : A2 ⊓ (A1 ⊔ A3) = W0 := by
    have hs : s2 ⊓ (s1 ⊔ s3) = s0 := rfl
    calc A2 ⊓ (A1 ⊔ A3) = φ.toFun (s2 ⊓ (s1 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hind3 : A3 ⊓ (A1 ⊔ A2) = W0 := by
    have hs : s3 ⊓ (s1 ⊔ s2) = s0 := rfl
    calc A3 ⊓ (A1 ⊔ A2) = φ.toFun (s3 ⊓ (s1 ⊔ s2)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs

  have hD2 : D ⊓ (A1 ⊔ A3) = W0 := by
    have hs : sd ⊓ (s1 ⊔ s3) = s0 := rfl
    calc D ⊓ (A1 ⊔ A3) = φ.toFun (sd ⊓ (s1 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hD3 : D ⊓ (A1 ⊔ A2) = W0 := by
    have hs : sd ⊓ (s1 ⊔ s2) = s0 := rfl
    calc D ⊓ (A1 ⊔ A2) = φ.toFun (sd ⊓ (s1 ⊔ s2)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs

  have hB12_eq : (A1 ⊔ A2) ⊓ (A3 ⊔ D) = B12 := by
    have hs : (s1 ⊔ s2) ⊓ (s3 ⊔ sd) = sb12 := rfl
    calc (A1 ⊔ A2) ⊓ (A3 ⊔ D) = φ.toFun ((s1 ⊔ s2) ⊓ (s3 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B12 := congrArg φ.toFun hs
  have hB13_eq : (A1 ⊔ A3) ⊓ (A2 ⊔ D) = B13 := by
    have hs : (s1 ⊔ s3) ⊓ (s2 ⊔ sd) = sb13 := rfl
    calc (A1 ⊔ A3) ⊓ (A2 ⊔ D) = φ.toFun ((s1 ⊔ s3) ⊓ (s2 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B13 := congrArg φ.toFun hs
  have hB23_eq : (A2 ⊔ A3) ⊓ (A1 ⊔ D) = B23 := by
    have hs : (s2 ⊔ s3) ⊓ (s1 ⊔ sd) = sb23 := rfl
    calc (A2 ⊔ A3) ⊓ (A1 ⊔ D) = φ.toFun ((s2 ⊔ s3) ⊓ (s1 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B23 := congrArg φ.toFun hs

  have hFano : B23 ≼ B12 ⊔ B13 := by
    have hs : sb23 ≼ sb12 ⊔ sb13 := rfl
    have hmap := φ.map_le_iff.mpr hs
    rw [φ.map_sup] at hmap
    exact hmap

  rcases not_le_exists_mem hne1 with ⟨u1, hu1, hnotW0_u1⟩
  rcases hcov1 u1 hu1 with ⟨d0, a23, hd0, ⟨a2, a3, ha2, ha3, rfl⟩, hu1_eq⟩
  let u2 := -a2
  let u3 := -a3
  have hu2 : A2.mem u2 := A2.neg_mem ha2
  have hu3 : A3.mem u3 := A3.neg_mem ha3
  have hDu : D.mem ((u1 + u2) + u3) := by
    have heq : (u1 + u2) + u3 = d0 := by
      unfold u2 u3
      rw [AddCommGroup.add_assoc u1 (-a2) (-a3), ← acg_neg_add, hu1_eq,
          AddCommGroup.add_assoc d0 (a2 + a3), acg_add_neg_cancel, acg_add_zero]
    rw [heq]
    exact hd0

  have hu23_in_B23 : B23.mem (u2 + u3) := by
    rw [← hB23_eq]
    refine ⟨⟨u2, u3, hu2, hu3, rfl⟩, ⟨-u1, (u1 + u2) + u3, A1.neg_mem hu1, hDu, ?_⟩⟩
    rw [AddCommGroup.add_assoc u1 u2 u3, ← AddCommGroup.add_assoc (-u1) u1 (u2 + u3),
        acg_neg_add_cancel, acg_zero_add]

  rcases hFano (u2 + u3) hu23_in_B23 with ⟨y, z, hyB12, hzB13, hyz_eq⟩
  rw [← hB12_eq] at hyB12
  rw [← hB13_eq] at hzB13
  rcases unpack_B12 hyB12 with ⟨y1, y2, y3, hy1, hy2, hy3, rfl, hDy⟩
  rcases unpack_B13 hzB13 with ⟨z1, z2, z3, hz1, hz2, hz3, rfl, hDz⟩

  have hsum_eq : ((y1 + z1) + y2) + z3 = (0 + u2) + u3 := by
    calc
      ((y1 + z1) + y2) + z3 = (y1 + y2) + (z1 + z3) := by
        rw [AddCommGroup.add_assoc (y1 + z1) y2 z3, add_rearrange4 y1 z1 y2 z3]
      _ = u2 + u3 := hyz_eq.symm
      _ = (0 + u2) + u3 := by rw [acg_zero_add]

  have hmod := frame_eq_mod h01 h02 hind1 hind2 hind3
    (A1.add_mem hy1 hz1) hy2 hz3 A1.zero_mem hu2 hu3 hsum_eq

  have hy1_u1 : modEq W0 y1 u1 :=
    (frame_D_from_2 h01 h02 h0D hind1 hind2 hind3 hD2
      hy1 hy3 hu1 hu3 hDy hDu hmod.2.1).1
  have hz1_u1 : modEq W0 z1 u1 :=
    (frame_D_from_3 h01 h03 h0D hind1 hind2 hind3 hD3
      hz1 hz2 hu1 hu2 hDz hDu hmod.2.2).1

  have hyz_2u1 : modEq W0 (y1 + z1) (u1 + u1) := mod_add hy1_u1 hz1_u1
  have h2u1_0 : modEq W0 (u1 + u1) 0 := mod_trans (mod_symm hyz_2u1) hmod.1
  have hW_2u1 : W0.mem (((1 : K) + 1) • u1) := by
    rw [VectorSpace.add_smul (1 : K) 1 u1, VectorSpace.one_smul (K := K) u1]
    exact mod_zero_iff.mp h2u1_0

  by_cases hchar2 : (1 : K) + 1 = 0
  · exact hchar2
  · exact False.elim (hnotW0_u1 (W0.cancel_smul_mem hchar2 hW_2u1))

/-- Any lattice embedding of `Sub3 F3` into `Subspace K V` forces `1 + 1 + 1 = 0` in `K`. -/
theorem embed_sub3_F3_forces_char3
    (φ : LatticeEmbedding (Sub3 F3) (Subspace K V)) : ((1 : K) + 1) + 1 = 0 := by
  let s0 : Sub3 F3 := .bot
  let s1 : Sub3 F3 := .line (.e0 .f0 .f0)
  let s2 : Sub3 F3 := .line (.e1 .f0)
  let s3 : Sub3 F3 := .line .e2
  let sd : Sub3 F3 := .line (.e0 .f1 .f1)
  let sb12 : Sub3 F3 := .line (.e0 .f1 .f0)
  let sb13 : Sub3 F3 := .line (.e0 .f0 .f1)
  let sb23 : Sub3 F3 := .line (.e1 .f1)
  let sc12 : Sub3 F3 := .line (.e0 .f2 .f0)
  let sdp  : Sub3 F3 := .line (.e0 .f2 .f1)

  let W0 := φ.toFun s0
  let A1 := φ.toFun s1
  let A2 := φ.toFun s2
  let A3 := φ.toFun s3
  let D  := φ.toFun sd
  let B12 := φ.toFun sb12
  let B13 := φ.toFun sb13
  let B23 := φ.toFun sb23
  let C12 := φ.toFun sc12
  let Dp  := φ.toFun sdp

  have h01 : W0 ≼ A1 := φ.map_le_iff.mpr (rfl : s0 ≼ s1)
  have h02 : W0 ≼ A2 := φ.map_le_iff.mpr (rfl : s0 ≼ s2)
  have h03 : W0 ≼ A3 := φ.map_le_iff.mpr (rfl : s0 ≼ s3)
  have h0D : W0 ≼ D  := φ.map_le_iff.mpr (rfl : s0 ≼ sd)
  have hne1 : ¬ (A1 ≼ W0) := fun h => Bool.noConfusion (φ.map_le_iff.mp h)

  have hcov1 : A1 ≼ D ⊔ (A2 ⊔ A3) := by
    have hs : s1 ≼ sd ⊔ (s2 ⊔ s3) := rfl
    have hmap := φ.map_le_iff.mpr hs
    rw [φ.map_sup, φ.map_sup] at hmap
    exact hmap

  have hind1 : A1 ⊓ (A2 ⊔ A3) = W0 := by
    have hs : s1 ⊓ (s2 ⊔ s3) = s0 := rfl
    calc A1 ⊓ (A2 ⊔ A3) = φ.toFun (s1 ⊓ (s2 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hind2 : A2 ⊓ (A1 ⊔ A3) = W0 := by
    have hs : s2 ⊓ (s1 ⊔ s3) = s0 := rfl
    calc A2 ⊓ (A1 ⊔ A3) = φ.toFun (s2 ⊓ (s1 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hind3 : A3 ⊓ (A1 ⊔ A2) = W0 := by
    have hs : s3 ⊓ (s1 ⊔ s2) = s0 := rfl
    calc A3 ⊓ (A1 ⊔ A2) = φ.toFun (s3 ⊓ (s1 ⊔ s2)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs

  have hD1 : D ⊓ (A2 ⊔ A3) = W0 := by
    have hs : sd ⊓ (s2 ⊔ s3) = s0 := rfl
    calc D ⊓ (A2 ⊔ A3) = φ.toFun (sd ⊓ (s2 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hD2 : D ⊓ (A1 ⊔ A3) = W0 := by
    have hs : sd ⊓ (s1 ⊔ s3) = s0 := rfl
    calc D ⊓ (A1 ⊔ A3) = φ.toFun (sd ⊓ (s1 ⊔ s3)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs
  have hD3 : D ⊓ (A1 ⊔ A2) = W0 := by
    have hs : sd ⊓ (s1 ⊔ s2) = s0 := rfl
    calc D ⊓ (A1 ⊔ A2) = φ.toFun (sd ⊓ (s1 ⊔ s2)) := by rw [φ.map_inf, φ.map_sup]
      _ = W0 := congrArg φ.toFun hs

  have hB12_eq : (A1 ⊔ A2) ⊓ (A3 ⊔ D) = B12 := by
    have hs : (s1 ⊔ s2) ⊓ (s3 ⊔ sd) = sb12 := rfl
    calc (A1 ⊔ A2) ⊓ (A3 ⊔ D) = φ.toFun ((s1 ⊔ s2) ⊓ (s3 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B12 := congrArg φ.toFun hs
  have hB13_eq : (A1 ⊔ A3) ⊓ (A2 ⊔ D) = B13 := by
    have hs : (s1 ⊔ s3) ⊓ (s2 ⊔ sd) = sb13 := rfl
    calc (A1 ⊔ A3) ⊓ (A2 ⊔ D) = φ.toFun ((s1 ⊔ s3) ⊓ (s2 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B13 := congrArg φ.toFun hs
  have hB23_eq : (A2 ⊔ A3) ⊓ (A1 ⊔ D) = B23 := by
    have hs : (s2 ⊔ s3) ⊓ (s1 ⊔ sd) = sb23 := rfl
    calc (A2 ⊔ A3) ⊓ (A1 ⊔ D) = φ.toFun ((s2 ⊔ s3) ⊓ (s1 ⊔ sd)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = B23 := congrArg φ.toFun hs
  have hC12_eq : (B13 ⊔ B23) ⊓ (A1 ⊔ A2) = C12 := by
    have hs : (sb13 ⊔ sb23) ⊓ (s1 ⊔ s2) = sc12 := rfl
    calc (B13 ⊔ B23) ⊓ (A1 ⊔ A2) = φ.toFun ((sb13 ⊔ sb23) ⊓ (s1 ⊔ s2)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = C12 := congrArg φ.toFun hs
  have hDp_eq : (C12 ⊔ A3) ⊓ (B13 ⊔ A2) = Dp := by
    have hs : (sc12 ⊔ s3) ⊓ (sb13 ⊔ s2) = sdp := rfl
    calc (C12 ⊔ A3) ⊓ (B13 ⊔ A2) = φ.toFun ((sc12 ⊔ s3) ⊓ (sb13 ⊔ s2)) := by
          rw [φ.map_inf, φ.map_sup, φ.map_sup]
      _ = Dp := congrArg φ.toFun hs

  have hTernary : B12 ≼ Dp ⊔ B23 := by
    have hs : sb12 ≼ sdp ⊔ sb23 := rfl
    have hmap := φ.map_le_iff.mpr hs
    rw [φ.map_sup] at hmap
    exact hmap

  rcases not_le_exists_mem hne1 with ⟨u1, hu1, hnotW0_u1⟩
  rcases hcov1 u1 hu1 with ⟨d0, a23, hd0, ⟨a2, a3, ha2, ha3, rfl⟩, hu1_eq⟩
  let u2 := -a2
  let u3 := -a3
  have hu2 : A2.mem u2 := A2.neg_mem ha2
  have hu3 : A3.mem u3 := A3.neg_mem ha3
  have hDu : D.mem ((u1 + u2) + u3) := by
    have heq : (u1 + u2) + u3 = d0 := by
      unfold u2 u3
      rw [AddCommGroup.add_assoc u1 (-a2) (-a3), ← acg_neg_add, hu1_eq,
          AddCommGroup.add_assoc d0 (a2 + a3), acg_add_neg_cancel, acg_add_zero]
    rw [heq]
    exact hd0
  have hDu_neg : D.mem (((-u1) + (-u2)) + (-u3)) := by
    rw [← acg_neg_add u1 u2, ← acg_neg_add (u1 + u2) u3]
    exact D.neg_mem hDu

  have hnotW0_u2 : ¬ W0.mem u2 := by
    intro hWu2
    have hm2 : modEq W0 u2 0 := mod_zero_iff.mpr hWu2
    have hD0 : D.mem (((0 : V) + 0) + 0) := by rw [acg_add_zero, acg_add_zero]; exact D.zero_mem
    have hm1 := (frame_D_from_2 h01 h02 h0D hind1 hind2 hind3 hD2
      hu1 hu3 A1.zero_mem A3.zero_mem hDu hD0 hm2).1
    exact hnotW0_u1 (mod_zero_iff.mp hm1)

  have hu12_in_B12 : B12.mem (u1 + u2) := by
    rw [← hB12_eq]
    refine ⟨⟨u1, u2, hu1, hu2, rfl⟩, ⟨-u3, (u1 + u2) + u3, A3.neg_mem hu3, hDu, ?_⟩⟩
    rw [AddCommGroup.add_comm (-u3), AddCommGroup.add_assoc (u1 + u2) u3 (-u3),
        acg_add_neg_cancel, acg_add_zero]

  rcases hTernary (u1 + u2) hu12_in_B12 with ⟨p, q, hpDp, hqB23, hpq_eq⟩
  rw [← hDp_eq] at hpDp
  rw [← hB23_eq] at hqB23
  rcases unpack_B23 hqB23 with ⟨q1, q2, q3, hq1, hq2, hq3, rfl, hDq⟩

  rcases hpDp with ⟨⟨c, p3, hcC12, hp3, rfl⟩, ⟨t, a2tilde, htB13, ha2tilde, hp_t_eq⟩⟩
  rw [← hC12_eq] at hcC12
  rw [← hB13_eq] at htB13
  rcases hcC12 with ⟨⟨r, s, hrB13, hsB23, hrs_eq⟩, ⟨c1, c2, hc1, hc2, rfl⟩⟩
  rw [← hB13_eq] at hrB13
  rw [← hB23_eq] at hsB23
  rcases unpack_B13 hrB13 with ⟨r1, r2, r3, hr1, hr2, hr3, rfl, hDr⟩
  rcases unpack_B23 hsB23 with ⟨s1v, s2v, s3v, hs1, hs2, hs3, rfl, hDs⟩
  rcases unpack_B13 htB13 with ⟨t1, t2, t3, ht1, ht2, ht3, rfl, hDt⟩

  -- Step A: Compare c1 + c2 = (r1 + r3) + (s2v + s3v)
  have hc_rs_eq : (c1 + c2) + 0 = (r1 + s2v) + (r3 + s3v) := by
    calc (c1 + c2) + 0 = c1 + c2 := acg_add_zero _
      _ = (r1 + r3) + (s2v + s3v) := hrs_eq
      _ = (r1 + s2v) + (r3 + s3v) := add_rearrange4 r1 r3 s2v s3v
  have hmod_c_rs := frame_eq_mod h01 h02 hind1 hind2 hind3
    hc1 hc2 A3.zero_mem hr1 hs2 (A3.add_mem hr3 hs3) hc_rs_eq

  -- Step B: Compare (c1 + c2) + p3 = (t1 + t3) + a2tilde
  have hc_t_eq : (c1 + c2) + p3 = (t1 + a2tilde) + t3 := by
    calc (c1 + c2) + p3 = (t1 + t3) + a2tilde := hp_t_eq
      _ = t1 + (t3 + a2tilde) := AddCommGroup.add_assoc t1 t3 a2tilde
      _ = t1 + (a2tilde + t3) := by rw [AddCommGroup.add_comm t3 a2tilde]
      _ = (t1 + a2tilde) + t3 := (AddCommGroup.add_assoc t1 a2tilde t3).symm
  have hmod_c_t := frame_eq_mod h01 h02 hind1 hind2 hind3
    hc1 hc2 hp3 ht1 ha2tilde ht3 hc_t_eq

  -- Step C: Compare u1 + u2 = ((c1 + c2) + p3) + (q2 + q3)
  have hu_pq_eq : (u1 + u2) + 0 = (c1 + (c2 + q2)) + (p3 + q3) := by
    calc (u1 + u2) + 0 = u1 + u2 := acg_add_zero _
      _ = ((c1 + c2) + p3) + (q2 + q3) := hpq_eq
      _ = ((c1 + c2) + q2) + (p3 + q3) := add_rearrange4 (c1 + c2) p3 q2 q3
      _ = (c1 + (c2 + q2)) + (p3 + q3) := by rw [AddCommGroup.add_assoc c1 c2 q2]
  have hmod_u_pq := frame_eq_mod h01 h02 hind1 hind2 hind3
    hu1 hu2 A3.zero_mem hc1 (A2.add_mem hc2 hq2) (A3.add_mem hp3 hq3) hu_pq_eq

  -- Step D: Chase all coordinates modulo W0
  have hr1_u1 : modEq W0 r1 u1 :=
    mod_trans (mod_symm hmod_c_rs.1) (mod_symm hmod_u_pq.1)
  have hr3_u3 : modEq W0 r3 u3 :=
    (frame_D_from_1 h01 h02 h0D hind1 hind2 hind3 hD1
      hr2 hr3 hu2 hu3 hDr hDu hr1_u1).2

  have hs3_negu3 : modEq W0 s3v (-u3) := by
    have h0_rs3 : W0.mem ((r3 + s3v) -₉ 0) := mod_symm hmod_c_rs.2.2
    rw [gsub_zero] at h0_rs3
    have hsub : W0.mem ((r3 + s3v) -₉ (r3 -₉ u3)) := W0.sub_mem h0_rs3 hr3_u3
    rw [gsub_sub_cancel_left] at hsub
    exact hsub

  have hs2_negu2 : modEq W0 s2v (-u2) :=
    (frame_D_from_3 h01 h03 h0D hind1 hind2 hind3 hD3
      hs1 hs2 (A1.neg_mem hu1) (A2.neg_mem hu2)
      hDs hDu_neg hs3_negu3).2

  have hc2_negu2 : modEq W0 c2 (-u2) := mod_trans hmod_c_rs.2.1 hs2_negu2

  have ht1_u1 : modEq W0 t1 u1 :=
    mod_trans (mod_symm hmod_c_t.1) (mod_symm hmod_u_pq.1)
  have ht3_u3 : modEq W0 t3 u3 :=
    (frame_D_from_1 h01 h02 h0D hind1 hind2 hind3 hD1
      ht2 ht3 hu2 hu3 hDt hDu ht1_u1).2
  have hp3_u3 : modEq W0 p3 u3 := mod_trans hmod_c_t.2.2 ht3_u3

  have hq3_negu3 : modEq W0 q3 (-u3) := by
    have h0_pq3 : W0.mem ((p3 + q3) -₉ 0) := mod_symm hmod_u_pq.2.2
    rw [gsub_zero] at h0_pq3
    have hsub : W0.mem ((p3 + q3) -₉ (p3 -₉ u3)) := W0.sub_mem h0_pq3 hp3_u3
    rw [gsub_sub_cancel_left] at hsub
    exact hsub

  have hq2_negu2 : modEq W0 q2 (-u2) :=
    (frame_D_from_3 h01 h03 h0D hind1 hind2 hind3 hD3
      hq1 hq2 (A1.neg_mem hu1) (A2.neg_mem hu2)
      hDq hDu_neg hq3_negu3).2

  have hcq2_neg2u2 : modEq W0 (c2 + q2) ((-u2) + (-u2)) := mod_add hc2_negu2 hq2_negu2
  have hu2_neg2u2 : modEq W0 u2 ((-u2) + (-u2)) := mod_trans hmod_u_pq.2.1 hcq2_neg2u2

  have hW_3u2 : W0.mem ((((1 : K) + 1) + 1) • u2) := by
    have hmem : W0.mem (u2 -₉ ((-u2) + (-u2))) := hu2_neg2u2
    rw [gsub_neg_double] at hmem
    rw [VectorSpace.add_smul ((1 : K) + 1) 1 u2, VectorSpace.add_smul (1 : K) 1 u2,
        VectorSpace.one_smul (K := K) u2]
    exact hmem

  by_cases hchar3 : ((1 : K) + 1) + 1 = 0
  · exact hchar3
  · exact False.elim (hnotW0_u2 (W0.cancel_smul_mem hchar3 hW_3u2))

end CharacteristicForcing

/-! ## 5. The 43-Element Modular Lattice, Infinite Family, and Formal Disproofs -/

/-- Ordinal gluing predicate identifying `top` of `Sub3 F2` with `bot` of `Sub3 F3`. -/
def isGlueElem (p : Sub3 F2 × Sub3 F3) : Bool :=
  decide (p.2 = .bot) || decide (p.1 = .top)

/-- The 43-element modular lattice obtained by gluing `Sub3 F2` beneath `Sub3 F3`. -/
abbrev CounterexampleLattice : Type :=
  { p : Sub3 F2 × Sub3 F3 // isGlueElem p = true }

theorem glue_inf_closed {p q : Sub3 F2 × Sub3 F3}
    (hp : isGlueElem p = true) (hq : isGlueElem q = true) :
    isGlueElem (p ⊓ q) = true := by
  unfold isGlueElem at hp hq ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hp hq ⊢
  change (sub3Inf p.2 q.2 = .bot) ∨ (sub3Inf p.1 q.1 = .top)
  rcases hp with hp2 | hp1
  · left; rw [hp2]; cases q.2 <;> rfl
  · rcases hq with hq2 | hq1
    · left; rw [hq2]; cases p.2 <;> rfl
    · right; rw [hp1, hq1]; rfl

theorem glue_sup_closed {p q : Sub3 F2 × Sub3 F3}
    (hp : isGlueElem p = true) (hq : isGlueElem q = true) :
    isGlueElem (p ⊔ q) = true := by
  unfold isGlueElem at hp hq ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hp hq ⊢
  change (sub3Sup p.2 q.2 = .bot) ∨ (sub3Sup p.1 q.1 = .top)
  rcases hp with hp2 | hp1
  · rcases hq with hq2 | hq1
    · left; rw [hp2, hq2]; rfl
    · right; rw [hq1]; cases p.1 <;> rfl
  · right; rw [hp1]; cases q.1 <;> rfl

instance counterexampleLatticeInst : Lattice CounterexampleLattice where
  le a b := a.val ≼ b.val
  inf a b := ⟨a.val ⊓ b.val, glue_inf_closed a.property b.property⟩
  sup a b := ⟨a.val ⊔ b.val, glue_sup_closed a.property b.property⟩
  le_refl a := Lattice.le_refl a.val
  le_trans h1 h2 := Lattice.le_trans h1 h2
  le_antisymm h1 h2 := Subtype.ext (Lattice.le_antisymm h1 h2)
  inf_le_left a b := Lattice.inf_le_left a.val b.val
  inf_le_right a b := Lattice.inf_le_right a.val b.val
  le_inf h1 h2 := Lattice.le_inf h1 h2
  le_sup_left a b := Lattice.le_sup_left a.val b.val
  le_sup_right a b := Lattice.le_sup_right a.val b.val
  sup_le h1 h2 := Lattice.sup_le h1 h2

/-- `CounterexampleLattice` satisfies Dedekind's modular law. -/
theorem counterexample_isModular : IsModularLattice CounterexampleLattice := by
  intro x y z hzx
  apply Subtype.ext
  exact prod_isModular sub3F2_isModular sub3F3_isModular x.val y.val z.val hzx

/-- Lower canonical lattice embedding `Sub3 F2 ↪ CounterexampleLattice`. -/
def embedF2IntoCounterexample : LatticeEmbedding (Sub3 F2) CounterexampleLattice where
  toFun x := ⟨(x, .bot), by simp [isGlueElem]⟩
  inj h := by
    have hv := congrArg Subtype.val h
    exact congrArg Prod.fst hv
  map_inf a b := Subtype.ext (Prod.ext rfl rfl)
  map_sup a b := Subtype.ext (Prod.ext rfl rfl)

/-- Upper canonical lattice embedding `Sub3 F3 ↪ CounterexampleLattice`. -/
def embedF3IntoCounterexample : LatticeEmbedding (Sub3 F3) CounterexampleLattice where
  toFun y := ⟨(.top, y), by simp [isGlueElem]⟩
  inj h := by
    have hv := congrArg Subtype.val h
    exact congrArg Prod.snd hv
  map_inf a b := Subtype.ext (Prod.ext rfl rfl)
  map_sup a b := Subtype.ext (Prod.ext rfl rfl)

def nonBotListF3 : List (Sub3 F3) :=
  (normVecsF3.map Sub3.line) ++ (normVecsF3.map Sub3.plane) ++ [Sub3.top]

theorem mem_nonBotListF3 (y : Sub3 F3) (hy : y ≠ .bot) : y ∈ nonBotListF3 := by
  cases y with
  | bot => exact False.elim (hy rfl)
  | line p =>
    cases p with
    | e0 b c => cases b <;> cases c <;> decide
    | e1 c => cases c <;> decide
    | e2 => decide
  | plane n =>
    cases n with
    | e0 b c => cases b <;> cases c <;> decide
    | e1 c => cases c <;> decide
    | e2 => decide
  | top => decide

theorem mem_map_of_mem_custom {α : Type u} {β : Type v} (f : α → β) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ∈ l.map f
  | [], h => nomatch h
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ hm => List.mem_cons_of_mem _ (mem_map_of_mem_custom f hm)

def counterexampleElems : List CounterexampleLattice :=
  (sub3ElemsF2.map embedF2IntoCounterexample.toFun) ++
  (nonBotListF3.map embedF3IntoCounterexample.toFun)

theorem mem_counterexampleElems (z : CounterexampleLattice) : z ∈ counterexampleElems := by
  rcases z with ⟨⟨x, y⟩, hz⟩
  unfold counterexampleElems
  by_cases hy : y = .bot
  · subst hy
    apply List.mem_append_left
    exact mem_map_of_mem_custom embedF2IntoCounterexample.toFun (mem_sub3ElemsF2 x)
  · have hx : x = .top := by
      unfold isGlueElem at hz
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hz
      rcases hz with hbot | htop
      · exact False.elim (hy hbot)
      · exact htop
    subst hx
    apply List.mem_append_right
    exact mem_map_of_mem_custom embedF3IntoCounterexample.toFun (mem_nonBotListF3 y hy)

/-- `CounterexampleLattice` is finite with exact cardinality `|L| = 43`. -/
theorem counterexample_hasCardinality : HasCardinality CounterexampleLattice 43 :=
  ⟨counterexampleElems, nodup_of_nodupBool (by decide), mem_counterexampleElems, rfl⟩

theorem counterexample_isFinite : IsFiniteType CounterexampleLattice :=
  ⟨43, counterexample_hasCardinality⟩

/-- Core impossibility theorem: `CounterexampleLattice` possesses NO lattice embedding
    into `Subspace K V` for ANY division ring (or field) `K` and ANY `K`-vector space `V`
    of ANY dimension (finite or infinite). -/
theorem counterexample_no_subspace_embedding
    {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V] :
    ¬ Nonempty (LatticeEmbedding CounterexampleLattice (Subspace K V)) := by
  rintro ⟨Φ⟩
  have h2 : (1 : K) + 1 = 0 :=
    embed_sub3_F2_forces_char2 (Φ.comp embedF2IntoCounterexample)
  have h3 : ((1 : K) + 1) + 1 = 0 :=
    embed_sub3_F3_forces_char3 (Φ.comp embedF3IntoCounterexample)
  exact char_two_and_three_impossible h2 h3

/-! ### Infinite Family of Pairwise Non-Isomorphic Finite Modular Counterexamples -/

/-- Finite chain `{0, 1, ..., m}` of cardinality `m + 1`. -/
abbrev FinChain (m : Nat) : Type := Fin (m + 1)

instance finChainLattice (m : Nat) : Lattice (FinChain m) where
  le a b := a.val ≤ b.val
  inf a b := if a.val ≤ b.val then a else b
  sup a b := if a.val ≤ b.val then b else a
  le_refl a := Nat.le_refl a.val
  le_trans h1 h2 := Nat.le_trans h1 h2
  le_antisymm h1 h2 := Fin.ext (Nat.le_antisymm h1 h2)
  inf_le_left a b := by show (if a.val ≤ b.val then a else b).val ≤ a.val; split <;> omega
  inf_le_right a b := by show (if a.val ≤ b.val then a else b).val ≤ b.val; split <;> omega
  le_inf {a b c} h1 h2 := by
    show c.val ≤ (if a.val ≤ b.val then a else b).val
    change c.val ≤ a.val at h1; change c.val ≤ b.val at h2
    split <;> omega
  le_sup_left a b := by show a.val ≤ (if a.val ≤ b.val then b else a).val; split <;> omega
  le_sup_right a b := by show b.val ≤ (if a.val ≤ b.val then b else a).val; split <;> omega
  sup_le {a b c} h1 h2 := by
    show (if a.val ≤ b.val then b else a).val ≤ c.val
    change a.val ≤ c.val at h1; change b.val ≤ c.val at h2
    split <;> omega

theorem finChain_isModular (m : Nat) : IsModularLattice (FinChain m) := by
  rintro ⟨xv, hxv⟩ ⟨yv, hyv⟩ ⟨zv, hzv⟩ hzx
  change zv ≤ xv at hzx
  apply Fin.ext
  let yz : Fin (m + 1) := if yv ≤ zv then ⟨zv, hzv⟩ else ⟨yv, hyv⟩
  let xy : Fin (m + 1) := if xv ≤ yv then ⟨xv, hxv⟩ else ⟨yv, hyv⟩
  show (if xv ≤ yz.val then (⟨xv, hxv⟩ : Fin (m + 1)) else yz).val =
       (if xy.val ≤ zv then (⟨zv, hzv⟩ : Fin (m + 1)) else xy).val
  have hyz_val : yz.val = if yv ≤ zv then zv else yv := by unfold yz; split <;> rfl
  have hxy_val : xy.val = if xv ≤ yv then xv else yv := by unfold xy; split <;> rfl
  have hl : (if xv ≤ yz.val then (⟨xv, hxv⟩ : Fin (m + 1)) else yz).val =
            if xv ≤ yz.val then xv else yz.val := by split <;> rfl
  have hr : (if xy.val ≤ zv then (⟨zv, hzv⟩ : Fin (m + 1)) else xy).val =
            if xy.val ≤ zv then zv else xy.val := by split <;> rfl
  rw [hl, hr, hyz_val, hxy_val]
  by_cases h1 : yv ≤ zv <;> by_cases h2 : xv ≤ yv <;> by_cases h3 : xv ≤ zv <;> simp [h1, h2, h3] <;> omega

def finChainElems : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finChainElems n).map Fin.succ

theorem length_finChainElems : ∀ n : Nat, (finChainElems n).length = n
  | 0 => rfl
  | n + 1 => by simp [finChainElems, length_finChainElems n]

theorem mem_finChainElems : ∀ {n : Nat} (i : Fin n), i ∈ finChainElems n
  | 0, ⟨_, h⟩ => nomatch h
  | n + 1, ⟨0, _⟩ => List.Mem.head _
  | n + 1, ⟨k + 1, hk⟩ => by
    unfold finChainElems
    apply List.mem_cons_of_mem
    exact mem_map_of_mem_custom Fin.succ (mem_finChainElems ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

theorem mem_map_succ_val_pos {n : Nat} {x : Fin (n + 1)} :
    ∀ {l : List (Fin n)}, x ∈ l.map Fin.succ → 0 < x.val
  | [], h => nomatch h
  | a :: _, h => by
    simp only [List.map] at h
    cases h with
    | head => exact Nat.zero_lt_succ a.val
    | tail _ hm => exact mem_map_succ_val_pos hm

theorem exists_mem_of_mem_map {α : Type u} {β : Type v} {f : α → β} {y : β} :
    ∀ {l : List α}, y ∈ l.map f → ∃ z ∈ l, f z = y
  | [], hm => nomatch hm
  | w :: _, hm => by
    simp only [List.map] at hm
    cases hm with
    | head => exact ⟨w, List.Mem.head _, rfl⟩
    | tail _ hmw =>
      rcases exists_mem_of_mem_map hmw with ⟨z, hz, hfz⟩
      exact ⟨z, List.mem_cons_of_mem w hz, hfz⟩

theorem nodup_map_inj {α : Type u} {β : Type v} {f : α → β}
    (hinj : ∀ a b : α, f a = f b → a = b) :
    ∀ {l : List α}, ListNodup l → ListNodup (l.map f)
  | [], _ => ListNodup.nil
  | x :: _, ListNodup.cons hnot hnd => by
    refine ListNodup.cons ?_ (nodup_map_inj hinj hnd)
    intro y hy hfx
    rcases exists_mem_of_mem_map hy with ⟨z, hz, rfl⟩
    exact hnot z hz (hinj x z hfx)

theorem nodup_finChainElems : ∀ n : Nat, ListNodup (finChainElems n)
  | 0 => ListNodup.nil
  | n + 1 => by
    unfold finChainElems
    refine ListNodup.cons ?_ (nodup_map_inj (fun a b h => Fin.ext (Nat.succ.inj (congrArg Fin.val h))) (nodup_finChainElems n))
    intro y hy h0
    have hpos := mem_map_succ_val_pos hy
    subst h0
    exact Nat.lt_irrefl 0 hpos

/-- Infinite family of finite modular counterexamples indexed by `m : Nat`,
    with strictly increasing cardinalities `43 * (m + 1)`. -/
abbrev CounterexampleFamily (m : Nat) : Type :=
  CounterexampleLattice × FinChain m

theorem counterexampleFamily_isModular (m : Nat) :
    IsModularLattice (CounterexampleFamily m) :=
  prod_isModular counterexample_isModular (finChain_isModular m)

theorem nodup_append_disjoint {α : Type u} :
    ∀ {l₁ l₂ : List α}, ListNodup l₁ → ListNodup l₂ →
      (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) → ListNodup (l₁ ++ l₂)
  | [], _, _, hnd₂, _ => hnd₂
  | x :: xs, l₂, ListNodup.cons hnot hnd₁, hnd₂, hdisj => by
    refine ListNodup.cons ?_ (nodup_append_disjoint hnd₁ hnd₂ (fun a ha b hb => hdisj a (List.mem_cons_of_mem x ha) b hb))
    intro y hy hxy
    rcases List.mem_append.mp hy with hy1 | hy2
    · exact hnot y hy1 hxy
    · exact hdisj x (List.Mem.head xs) y hy2 hxy

def listProd {α : Type u} {β : Type v} : List α → List β → List (α × β)
  | [], _ => []
  | x :: xs, lb => lb.map (fun b => (x, b)) ++ listProd xs lb

theorem length_listProd {α : Type u} {β : Type v} :
    ∀ (la : List α) (lb : List β), (listProd la lb).length = la.length * lb.length
  | [], _ => by simp [listProd]
  | _ :: xs, lb => by
    simp only [listProd, List.length_append, List.length_map, List.length_cons, length_listProd xs lb]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (xs.length * lb.length)]

theorem mem_listProd_of_mem {α : Type u} {β : Type v} {a : α} {b : β} :
    ∀ {la : List α} {lb : List β}, a ∈ la → b ∈ lb → (a, b) ∈ listProd la lb
  | [], _, ha, _ => nomatch ha
  | _ :: _, _, List.Mem.head _, hb =>
    List.mem_append_left _ (mem_map_of_mem_custom (fun b => (_, b)) hb)
  | _ :: _, _, List.Mem.tail _ haxs, hb =>
    List.mem_append_right _ (mem_listProd_of_mem haxs hb)

theorem fst_mem_of_mem_map_pair {α : Type u} {β : Type v} {x : α} {p : α × β} :
    ∀ {lb : List β}, p ∈ lb.map (fun b => (x, b)) → p.1 = x
  | [], h => nomatch h
  | _ :: _, h => by
    simp only [List.map] at h
    cases h with
    | head => rfl
    | tail _ ht => exact fst_mem_of_mem_map_pair ht

theorem fst_mem_of_mem_listProd {α : Type u} {β : Type v} {p : α × β} :
    ∀ {la : List α} {lb : List β}, p ∈ listProd la lb → p.1 ∈ la
  | [], _, h => nomatch h
  | x :: xs, lb, h => by
    rcases List.mem_append.mp h with h1 | h2
    · rw [fst_mem_of_mem_map_pair h1]
      exact List.Mem.head xs
    · exact List.mem_cons_of_mem x (fst_mem_of_mem_listProd h2)

theorem nodup_listProd {α : Type u} {β : Type v} {lb : List β} (hndb : ListNodup lb) :
    ∀ {la : List α}, ListNodup la → ListNodup (listProd la lb)
  | [], _ => ListNodup.nil
  | x :: xs, ListNodup.cons hnot hnd => by
    unfold listProd
    apply nodup_append_disjoint
    · exact nodup_map_inj (fun _ _ h => congrArg Prod.snd h) hndb
    · exact nodup_listProd hndb hnd
    · intro p hp q hq hpq
      have hp1 : p.1 = x := fst_mem_of_mem_map_pair hp
      have hq1 : q.1 ∈ xs := fst_mem_of_mem_listProd hq
      have heq1 : x = q.1 := by rw [← hp1, hpq]
      exact hnot q.1 hq1 heq1

theorem prod_hasCardinality {α : Type u} {β : Type v} {m n : Nat}
    (hm : HasCardinality α m) (hn : HasCardinality β n) :
    HasCardinality (α × β) (m * n) := by
  rcases hm with ⟨la, hnda, halla, rfl⟩
  rcases hn with ⟨lb, hndb, hallb, rfl⟩
  refine ⟨listProd la lb, nodup_listProd hndb hnda, ?_, length_listProd la lb⟩
  intro ⟨a, b⟩
  exact mem_listProd_of_mem (halla a) (hallb b)

theorem finChain_hasCardinality (m : Nat) : HasCardinality (FinChain m) (m + 1) :=
  ⟨finChainElems (m + 1), nodup_finChainElems (m + 1), mem_finChainElems, length_finChainElems (m + 1)⟩

theorem counterexampleFamily_hasCardinality (m : Nat) :
    HasCardinality (CounterexampleFamily m) (43 * (m + 1)) :=
  prod_hasCardinality counterexample_hasCardinality (finChain_hasCardinality m)

theorem counterexampleFamily_isFinite (m : Nat) :
    IsFiniteType (CounterexampleFamily m) :=
  ⟨43 * (m + 1), counterexampleFamily_hasCardinality m⟩

/-- Lattice isomorphism between two lattices. -/
structure LatticeIso (L : Type u) (M : Type v) [Lattice L] [Lattice M] where
  toFun : L → M
  invFun : M → L
  left_inv : ∀ x : L, invFun (toFun x) = x
  right_inv : ∀ y : M, toFun (invFun y) = y
  map_inf : ∀ a b : L, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_sup : ∀ a b : L, toFun (a ⊔ b) = toFun a ⊔ toFun b

/-- Distinct members of `CounterexampleFamily` are pairwise non-isomorphic. -/
theorem counterexampleFamily_pairwise_noniso {m₁ m₂ : Nat} (hne : m₁ ≠ m₂) :
    ¬ Nonempty (LatticeIso (CounterexampleFamily m₁) (CounterexampleFamily m₂)) := by
  rintro ⟨iso⟩
  rcases counterexampleFamily_hasCardinality m₁ with ⟨l₁, hnd₁, hall₁, hlen₁⟩
  have hcard2 : HasCardinality (CounterexampleFamily m₂) (43 * (m₁ + 1)) := by
    refine ⟨l₁.map iso.toFun, ?_, ?_, ?_⟩
    · exact nodup_map_inj (fun a b h => by rw [← iso.left_inv a, ← iso.left_inv b, h]) hnd₁
    · intro y
      rw [← iso.right_inv y]
      exact mem_map_of_mem_custom iso.toFun (hall₁ (iso.invFun y))
    · rw [List.length_map, hlen₁]
  have heq : 43 * (m₁ + 1) = 43 * (m₂ + 1) :=
    hasCardinality_unique hcard2 (counterexampleFamily_hasCardinality m₂)
  omega

/-- Canonical embedding of `CounterexampleLattice` into `CounterexampleFamily m`. -/
def embedIntoFamily (m : Nat) :
    LatticeEmbedding CounterexampleLattice (CounterexampleFamily m) where
  toFun z := (z, ⟨0, Nat.zero_lt_succ m⟩)
  inj h := congrArg Prod.fst h
  map_inf a b := Prod.ext rfl (by
    show (if (0 : Nat) ≤ 0 then (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) else ⟨0, Nat.zero_lt_succ m⟩) = _
    rfl)
  map_sup a b := Prod.ext rfl (by
    show (if (0 : Nat) ≤ 0 then (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) else ⟨0, Nat.zero_lt_succ m⟩) = _
    rfl)

/-- Every member of the infinite family `CounterexampleFamily m` possesses NO lattice
    embedding into `Subspace K V` for ANY division ring (or field) `K` and ANY `V`. -/
theorem counterexampleFamily_no_subspace_embedding (m : Nat)
    {K : Type u} [DivisionRing K] {V : Type v} [AddCommGroup V] [VectorSpace K V] :
    ¬ Nonempty (LatticeEmbedding (CounterexampleFamily m) (Subspace K V)) := by
  rintro ⟨Φ⟩
  exact counterexample_no_subspace_embedding ⟨Φ.comp (embedIntoFamily m)⟩

/-! ## 6. Official Conjecture Statements and Main Disproof Theorems -/

/-- Formulation 1 (Coordinate vector space over a commutative field, `dim ≤ |L|`):
    Every finite modular lattice `L` of cardinality `n = |L|` embeds into the
    subspace lattice `Subspace K (FinVec K d)` of `K^d` for some field `K` and `d ≤ n`. -/
def Conjecture8537_CoordField : Prop :=
  ∀ (L : Type) [Lattice L], IsModularLattice L →
    ∀ (n : Nat), HasCardinality L n →
      ∃ (K : Type) (_ : Field K) (d : Nat),
        d ≤ n ∧ Nonempty (LatticeEmbedding L (Subspace K (FinVec K d)))

/-- Formulation 2 (Abstract vector space with explicit basis of length `d ≤ |L|`, over a field):
    Every finite modular lattice `L` of cardinality `n = |L|` embeds into `Subspace K V`
    for some field `K` and `K`-vector space `V` of linear dimension `d ≤ n`. -/
def Conjecture8537_BasisField : Prop :=
  ∀ (L : Type) [Lattice L], IsModularLattice L →
    ∀ (n : Nat), HasCardinality L n →
      ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : VectorSpace K V) (d : Nat),
        d ≤ n ∧ HasLinearDimension K V d ∧ Nonempty (LatticeEmbedding L (Subspace K V))

/-- Formulation 3 (Abstract vector space spanned by at most `|L|` vectors, over a division ring):
    Every finite modular lattice `L` of cardinality `n = |L|` embeds into `Subspace K V`
    for some division ring `K` and `K`-vector space `V` with `HasDimensionAtMost K V n`. -/
def Conjecture8537_SpanDivisionRing : Prop :=
  ∀ (L : Type) [Lattice L], IsModularLattice L →
    ∀ (n : Nat), HasCardinality L n →
      ∃ (K : Type) (_ : DivisionRing K) (V : Type) (_ : AddCommGroup V) (_ : VectorSpace K V),
        HasDimensionAtMost K V n ∧ Nonempty (LatticeEmbedding L (Subspace K V))

/-- Formulation 4 (Unrestricted dimension, over any division ring or field):
    Every finite modular lattice `L` embeds into `Subspace K V` for some division ring `K`
    and `K`-vector space `V` (even without any upper bound on linear dimension). -/
def EveryFiniteModularEmbedsInSubspace : Prop :=
  ∀ (L : Type) [Lattice L], IsModularLattice L → IsFiniteType L →
    ∃ (K : Type) (_ : DivisionRing K) (V : Type) (_ : AddCommGroup V) (_ : VectorSpace K V),
      Nonempty (LatticeEmbedding L (Subspace K V))

/-- Full two-clause statement of Conjecture 00000008537 parameterized by any predicate
    `MinimalIsProjectiveGeometryType` representing the second clause ("and the minimal
    embeddings are of projective geometry type"). -/
def Conjecture8537_Full
    (MinimalIsProjectiveGeometryType :
      ∀ (L : Type) [Lattice L], Prop) : Prop :=
  Conjecture8537_CoordField ∧
    (∀ (L : Type) [Lattice L], IsModularLattice L → IsFiniteType L →
      MinimalIsProjectiveGeometryType L)

theorem disproof_everyFiniteModularEmbedsInSubspace :
    ¬ EveryFiniteModularEmbedsInSubspace := by
  intro h
  rcases h CounterexampleLattice counterexample_isModular counterexample_isFinite with
    ⟨K, instK, V, instACG, instVS, hEmb⟩
  exact @counterexample_no_subspace_embedding K instK V instACG instVS hEmb

theorem disproof_conjecture8537_spanDivisionRing :
    ¬ Conjecture8537_SpanDivisionRing := by
  intro h
  rcases h CounterexampleLattice counterexample_isModular 43 counterexample_hasCardinality with
    ⟨K, instK, V, instACG, instVS, _, hEmb⟩
  exact @counterexample_no_subspace_embedding K instK V instACG instVS hEmb

theorem disproof_conjecture8537_basisField :
    ¬ Conjecture8537_BasisField := by
  intro h
  rcases h CounterexampleLattice counterexample_isModular 43 counterexample_hasCardinality with
    ⟨K, instF, V, instACG, instVS, _, _, _, hEmb⟩
  exact @counterexample_no_subspace_embedding K instF.toDivisionRing V instACG instVS hEmb

theorem disproof_conjecture8537_coordField :
    ¬ Conjecture8537_CoordField := by
  intro h
  rcases h CounterexampleLattice counterexample_isModular 43 counterexample_hasCardinality with
    ⟨K, instF, d, _, hEmb⟩
  let _ : Field K := instF
  exact counterexample_no_subspace_embedding (K := K) (V := FinVec K d) hEmb

theorem disproof_conjecture8537_full
    (MinimalIsProjectiveGeometryType : ∀ (L : Type) [Lattice L], Prop) :
    ¬ Conjecture8537_Full MinimalIsProjectiveGeometryType := by
  rintro ⟨h1, _⟩
  exact disproof_conjecture8537_coordField h1

/-! ### Non-Vacuity Verification: `Sub3 F2` Satisfies Every Positive Predicate -/

def stdBasisF2 : List (FinVec F2 3) :=
  [ofTriple (.f1, .f0, .f0), ofTriple (.f0, .f1, .f0), ofTriple (.f0, .f0, .f1)]

theorem finVecF2_3_hasLinearDimension : HasLinearDimension F2 (FinVec F2 3) 3 := by
  refine ⟨stdBasisF2, rfl, ?_, ?_⟩
  · intro cs hlen hcomb c hc
    match cs, hlen with
    | [c0, c1, c2], _ =>
      have h0 : linComb F2 [c0, c1, c2] stdBasisF2 ⟨0, by decide⟩ = .f0 := congrFun hcomb ⟨0, by decide⟩
      have h1 : linComb F2 [c0, c1, c2] stdBasisF2 ⟨1, by decide⟩ = .f0 := congrFun hcomb ⟨1, by decide⟩
      have h2 : linComb F2 [c0, c1, c2] stdBasisF2 ⟨2, by decide⟩ = .f0 := congrFun hcomb ⟨2, by decide⟩
      have hc0 : c0 = .f0 := by cases c0 <;> cases c1 <;> cases c2 <;> first | rfl | contradiction
      have hc1 : c1 = .f0 := by cases c0 <;> cases c1 <;> cases c2 <;> first | rfl | contradiction
      have hc2 : c2 = .f0 := by cases c0 <;> cases c1 <;> cases c2 <;> first | rfl | contradiction
      subst hc0; subst hc1; subst hc2
      cases hc with
      | head => rfl
      | tail _ htail =>
        cases htail with
        | head => rfl
        | tail _ htail2 =>
          cases htail2 with
          | head => rfl
          | tail _ hnil => nomatch hnil
  · intro v
    let b0 := ofTriple (F2.f1, F2.f0, F2.f0)
    let b1 := ofTriple (F2.f0, F2.f1, F2.f0)
    let b2 := ofTriple (F2.f0, F2.f0, F2.f1)
    let v0 := v ⟨0, by decide⟩
    let v1 := v ⟨1, by decide⟩
    let v2 := v ⟨2, by decide⟩
    have hb0 : b0 ∈ stdBasisF2 := List.Mem.head _
    have hb1 : b1 ∈ stdBasisF2 := List.Mem.tail _ (List.Mem.head _)
    have hb2 : b2 ∈ stdBasisF2 := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    have hspan : InSpan F2 stdBasisF2 ((v0 • b0 + v1 • b1) + v2 • b2) :=
      InSpan.add
        (InSpan.add (InSpan.smul v0 (InSpan.gen hb0)) (InSpan.smul v1 (InSpan.gen hb1)))
        (InSpan.smul v2 (InSpan.gen hb2))
    have heq : (v0 • b0 + v1 • b1) + v2 • b2 = v := by
      funext ⟨i, hi⟩
      match i, hi with
      | 0, _ => show (v0 * F2.f1 + v1 * F2.f0) + v2 * F2.f0 = v0; cases v0 <;> cases v1 <;> cases v2 <;> rfl
      | 1, _ => show (v0 * F2.f0 + v1 * F2.f1) + v2 * F2.f0 = v1; cases v0 <;> cases v1 <;> cases v2 <;> rfl
      | 2, _ => show (v0 * F2.f0 + v1 * F2.f0) + v2 * F2.f1 = v2; cases v0 <;> cases v1 <;> cases v2 <;> rfl
    rw [heq] at hspan
    exact hspan

/-- Non-vacuity witness: `Sub3 F2` (cardinality 16) satisfies all positive predicates
    of `Conjecture8537_BasisField`, `Conjecture8537_CoordField`, and
    `Conjecture8537_SpanDivisionRing` at dimension `d = 3 ≤ 16`. -/
theorem sub3F2_positive_witness :
    IsModularLattice (Sub3 F2) ∧
    HasCardinality (Sub3 F2) 16 ∧
    (3 ≤ 16) ∧
    HasLinearDimension F2 (FinVec F2 3) 3 ∧
    HasDimensionAtMost F2 (FinVec F2 3) 16 ∧
    Nonempty (LatticeEmbedding (Sub3 F2) (Subspace F2 (FinVec F2 3))) :=
  ⟨sub3F2_isModular,
   sub3F2_hasCardinality,
   by decide,
   finVecF2_3_hasLinearDimension,
   hasDimensionAtMost_of_hasLinearDimension finVecF2_3_hasLinearDimension (by decide),
   ⟨sub3F2CanonicalEmbedding⟩⟩

#print axioms sub3F2_positive_witness

#print axioms hasCardinality_unique
#print axioms subspace_isModular
#print axioms sub3F2_isModular
#print axioms sub3F3_isModular
#print axioms embed_sub3_F2_forces_char2
#print axioms embed_sub3_F3_forces_char3
#print axioms counterexample_isModular
#print axioms counterexample_hasCardinality
#print axioms counterexample_no_subspace_embedding
#print axioms counterexampleFamily_isModular
#print axioms counterexampleFamily_hasCardinality
#print axioms counterexampleFamily_pairwise_noniso
#print axioms counterexampleFamily_no_subspace_embedding
#print axioms disproof_everyFiniteModularEmbedsInSubspace
#print axioms disproof_conjecture8537_spanDivisionRing
#print axioms disproof_conjecture8537_basisField
#print axioms disproof_conjecture8537_coordField
#print axioms disproof_conjecture8537_full

end Conjecture8537
