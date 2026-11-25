/-
  Conjecture 00000007628 — Field Foundations, Finite Field F₃, and Group Isomorphism Invariants
  Core Lean 4.19.0 (zero external dependencies)
-/

namespace Conjecture00000007628

/-- Carrier constants `0` and `1` providing `OfNat K 0` and `OfNat K 1` in Core Lean 4.19.0. -/
class ZeroOne (K : Type) where
  zero : K
  one  : K

instance {K : Type} [ZeroOne K] : OfNat K 0 := ⟨ZeroOne.zero⟩
instance {K : Type} [ZeroOne K] : OfNat K 1 := ⟨ZeroOne.one⟩

/-- Minimal self-contained commutative field typeclass in Core Lean 4.19.0. -/
class CommField (K : Type) extends ZeroOne K, Add K, Neg K, Sub K, Mul K where
  inv : K → K
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  neg_add_cancel : ∀ a : K, (-a) + a = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + (-b)
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : K, a * b = b * a
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  zero_ne_one : (0 : K) ≠ 1
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * inv a = 1

namespace CommField

section BasicLemmas
variable {K : Type} [CommField K]

theorem add_neg_cancel (a : K) : a + (-a) = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : K} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : K} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

theorem mul_zero (a : K) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : K) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

theorem neg_zero : (-(0 : K)) = 0 := by
  apply add_right_cancel (c := 0)
  rw [neg_add_cancel, add_zero]

theorem neg_neg (a : K) : -(-a) = a := by
  apply add_left_cancel (a := -a)
  rw [add_neg_cancel, neg_add_cancel]

theorem eq_neg_of_add_eq_zero {a b : K} (h : a + b = 0) : b = -a := by
  apply add_left_cancel (a := a)
  rw [h, add_neg_cancel]

theorem neg_add (a b : K) : -(a + b) = (-a) + (-b) := by
  symm
  apply eq_neg_of_add_eq_zero
  calc
    (a + b) + ((-a) + (-b)) = a + (b + ((-b) + (-a))) := by
      rw [add_comm (-a) (-b), add_assoc]
    _ = a + ((b + (-b)) + (-a)) := by rw [← add_assoc b (-b) (-a)]
    _ = a + (0 + (-a)) := by rw [add_neg_cancel]
    _ = a + (-a) := by rw [zero_add]
    _ = 0 := add_neg_cancel a

theorem mul_neg (a b : K) : a * (-b) = -(a * b) := by
  apply eq_neg_of_add_eq_zero
  rw [← left_distrib, add_neg_cancel, mul_zero]

theorem neg_mul (a b : K) : (-a) * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : K) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul (a : K) : (-1 : K) * a = -a := by
  rw [neg_mul, one_mul]

theorem sub_self (a : K) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_zero (a : K) : a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

theorem zero_sub (a : K) : 0 - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem eq_of_sub_eq_zero {a b : K} (h : a - b = 0) : a = b := by
  apply add_right_cancel (c := -b)
  rw [← sub_eq_add_neg, h, add_neg_cancel]

theorem sub_eq_zero_of_eq {a b : K} (h : a = b) : a - b = 0 := by
  rw [h, sub_self]

theorem mul_sub (a b c : K) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : K) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem inv_mul_cancel {a : K} (ha : a ≠ 0) : inv a * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel a ha

theorem inv_ne_zero {a : K} (ha : a ≠ 0) : inv a ≠ 0 := by
  intro hinv
  have h1 : a * inv a = 1 := mul_inv_cancel a ha
  rw [hinv, mul_zero] at h1
  exact zero_ne_one h1

theorem mul_eq_zero {a b : K} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h1 : inv a * (a * b) = inv a * 0 := congrArg (fun x => inv a * x) h
    rw [← mul_assoc, inv_mul_cancel ha, one_mul, mul_zero] at h1
    exact h1

theorem mul_left_cancel {a b c : K} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have hsub : a * (b - c) = 0 := by
    rw [mul_sub, h, sub_self]
  cases mul_eq_zero hsub with
  | inl h0 => exact absurd h0 ha
  | inr hbc => exact eq_of_sub_eq_zero hbc

theorem sq_eq_zero {a : K} (h : a * a = 0) : a = 0 := by
  cases mul_eq_zero h with
  | inl h0 => exact h0
  | inr h0 => exact h0

theorem neg_eq_self_iff_two_mul_zero (a : K) : (-a = a) ↔ ((1 + 1 : K) * a = 0) := by
  constructor
  · intro h
    rw [right_distrib, one_mul]
    have h2 : a + a = (-a) + a := by rw [h]
    rw [h2, neg_add_cancel]
  · intro h
    rw [right_distrib, one_mul] at h
    symm
    exact eq_neg_of_add_eq_zero h

theorem one_ne_neg_one (hchar : (1 : K) + 1 ≠ 0) : (1 : K) ≠ -1 := by
  intro h
  have h2 : (-1 : K) = 1 := h.symm
  have h3 := (neg_eq_self_iff_two_mul_zero (1 : K)).mp h2
  rw [mul_one] at h3
  exact hchar h3

def two (K : Type) [CommField K] : K := (1 : K) + 1
def half (K : Type) [CommField K] : K := inv (two K)

theorem two_mul_half {K : Type} [CommField K] (hchar : (1 : K) + 1 ≠ 0) :
    two K * half K = 1 :=
  mul_inv_cancel (two K) hchar

theorem half_mul_two {K : Type} [CommField K] (hchar : (1 : K) + 1 ≠ 0) :
    half K * two K = 1 :=
  inv_mul_cancel hchar

theorem half_add_half {K : Type} [CommField K] (hchar : (1 : K) + 1 ≠ 0) (a : K) :
    half K * a + half K * a = a := by
  calc
    half K * a + half K * a = (half K + half K) * a := (right_distrib _ _ _).symm
    _ = (half K * (1 + 1)) * a := by rw [left_distrib, mul_one]
    _ = (half K * two K) * a := rfl
    _ = 1 * a := by rw [half_mul_two hchar]
    _ = a := one_mul a

end BasicLemmas
end CommField

/-! ### Exact Finite Field `F3` (`𝔽₃ = {0, 1, 2}`, characteristic `3 ≠ 2`) -/

inductive F3 where
  | zero : F3
  | one  : F3
  | two  : F3
  deriving DecidableEq, Repr

namespace F3

def add : F3 → F3 → F3
  | zero, x => x
  | x, zero => x
  | one, one => two
  | one, two => zero
  | two, one => zero
  | two, two => one

def neg : F3 → F3
  | zero => zero
  | one  => two
  | two  => one

def sub (a b : F3) : F3 := add a (neg b)

def mul : F3 → F3 → F3
  | zero, _ => zero
  | _, zero => zero
  | one, x  => x
  | x, one  => x
  | two, two => one

def inv : F3 → F3
  | zero => zero
  | one  => one
  | two  => two

instance : ZeroOne F3 := ⟨zero, one⟩
instance : Add F3 := ⟨add⟩
instance : Neg F3 := ⟨neg⟩
instance : Sub F3 := ⟨sub⟩
instance : Mul F3 := ⟨mul⟩

instance : CommField F3 where
  inv  := inv
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv_cancel a ha := by
    cases a with
    | zero => exact absurd rfl ha
    | one => rfl
    | two => rfl

theorem char_ne_two : (1 : F3) + 1 ≠ 0 := by decide

def elems : List F3 := [zero, one, two]

theorem mem_elems (x : F3) : x ∈ elems := by
  cases x <;> decide

end F3

/-! ### Abstract Group Isomorphism & Finite Cardinality Obstructions -/

/-- Multiplicative equivalence (isomorphism) between two operations `(G, mulG)` and `(H, mulH)`. -/
structure MulEquiv (G : Type) (mulG : G → G → G) (H : Type) (mulH : H → H → H) where
  toFun   : G → H
  invFun  : H → G
  left_inv  : ∀ x : G, invFun (toFun x) = x
  right_inv : ∀ y : H, toFun (invFun y) = y
  map_mul   : ∀ x y : G, toFun (mulG x y) = mulH (toFun x) (toFun y)

/-- Obstruction 1: An abelian group cannot be isomorphic to a non-abelian group. -/
theorem no_mulEquiv_of_abelian_nonabelian
    {G : Type} {mulG : G → G → G}
    {H : Type} {mulH : H → H → H}
    (hab : ∀ x y : G, mulG x y = mulG y x)
    (hnonab : ∃ u v : H, mulH u v ≠ mulH v u) :
    MulEquiv G mulG H mulH → False := by
  intro iso
  rcases hnonab with ⟨u, v, huv⟩
  have hcomm : mulG (iso.invFun u) (iso.invFun v) = mulG (iso.invFun v) (iso.invFun u) :=
    hab (iso.invFun u) (iso.invFun v)
  have hmap : iso.toFun (mulG (iso.invFun u) (iso.invFun v)) =
      iso.toFun (mulG (iso.invFun v) (iso.invFun u)) := congrArg iso.toFun hcomm
  rw [iso.map_mul, iso.map_mul, iso.right_inv, iso.right_inv] at hmap
  exact huv hmap

/-- Obstruction 2: A group with trivial center cannot be isomorphic to a group with two
    distinct central elements. -/
theorem no_mulEquiv_of_trivial_center
    {G : Type} {mulG : G → G → G} (oneG : G)
    {H : Type} {mulH : H → H → H}
    (htriv : ∀ z : G, (∀ x : G, mulG z x = mulG x z) → z = oneG)
    (hz : ∃ z₁ z₂ : H, z₁ ≠ z₂ ∧
      (∀ y : H, mulH z₁ y = mulH y z₁) ∧
      (∀ y : H, mulH z₂ y = mulH y z₂)) :
    MulEquiv G mulG H mulH → False := by
  intro iso
  rcases hz with ⟨z₁, z₂, hne, hz₁, hz₂⟩
  have hc₁ : ∀ x : G, mulG (iso.invFun z₁) x = mulG x (iso.invFun z₁) := by
    intro x
    have h := hz₁ (iso.toFun x)
    have h' : iso.toFun (mulG (iso.invFun z₁) x) = iso.toFun (mulG x (iso.invFun z₁)) := by
      rw [iso.map_mul, iso.map_mul, iso.right_inv]
      exact h
    have h'' : iso.invFun (iso.toFun (mulG (iso.invFun z₁) x)) =
        iso.invFun (iso.toFun (mulG x (iso.invFun z₁))) := congrArg iso.invFun h'
    rw [iso.left_inv, iso.left_inv] at h''
    exact h''
  have hc₂ : ∀ x : G, mulG (iso.invFun z₂) x = mulG x (iso.invFun z₂) := by
    intro x
    have h := hz₂ (iso.toFun x)
    have h' : iso.toFun (mulG (iso.invFun z₂) x) = iso.toFun (mulG x (iso.invFun z₂)) := by
      rw [iso.map_mul, iso.map_mul, iso.right_inv]
      exact h
    have h'' : iso.invFun (iso.toFun (mulG (iso.invFun z₂) x)) =
        iso.invFun (iso.toFun (mulG x (iso.invFun z₂))) := congrArg iso.invFun h'
    rw [iso.left_inv, iso.left_inv] at h''
    exact h''
  have heq : iso.invFun z₁ = iso.invFun z₂ := by
    rw [htriv (iso.invFun z₁) hc₁, htriv (iso.invFun z₂) hc₂]
  have hz_eq : z₁ = z₂ := by
    rw [← iso.right_inv z₁, ← iso.right_inv z₂, heq]
  exact hne hz_eq

/-- Group structure extending `mul` with identity and two-sided inverse, for commutator invariants. -/
structure GroupStruct (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : G, mul one a = a
  mul_one   : ∀ a : G, mul a one = a
  mul_left_inv  : ∀ a : G, mul (inv a) a = one
  mul_right_inv : ∀ a : G, mul a (inv a) = one

namespace GroupStruct

def comm {G : Type} (S : GroupStruct G) (a b : G) : G :=
  S.mul (S.mul a b) (S.mul (S.inv a) (S.inv b))

theorem map_one {G H : Type} (SG : GroupStruct G) (SH : GroupStruct H)
    (iso : MulEquiv G SG.mul H SH.mul) : iso.toFun SG.one = SH.one := by
  have h1 : SH.mul (iso.toFun SG.one) (iso.toFun SG.one) = iso.toFun SG.one := by
    rw [← iso.map_mul, SG.one_mul]
  have h2 : SH.mul (SH.inv (iso.toFun SG.one)) (SH.mul (iso.toFun SG.one) (iso.toFun SG.one)) =
      SH.mul (SH.inv (iso.toFun SG.one)) (iso.toFun SG.one) :=
    congrArg (fun y => SH.mul (SH.inv (iso.toFun SG.one)) y) h1
  rw [← SH.mul_assoc, SH.mul_left_inv, SH.one_mul] at h2
  exact h2

theorem map_inv {G H : Type} (SG : GroupStruct G) (SH : GroupStruct H)
    (iso : MulEquiv G SG.mul H SH.mul) (a : G) :
    iso.toFun (SG.inv a) = SH.inv (iso.toFun a) := by
  have h1 : SH.mul (iso.toFun (SG.inv a)) (iso.toFun a) = SH.one := by
    rw [← iso.map_mul, SG.mul_left_inv, map_one SG SH iso]
  have h2 : SH.mul (SH.mul (iso.toFun (SG.inv a)) (iso.toFun a)) (SH.inv (iso.toFun a)) =
      SH.mul SH.one (SH.inv (iso.toFun a)) :=
    congrArg (fun z => SH.mul z (SH.inv (iso.toFun a))) h1
  rw [SH.mul_assoc, SH.mul_right_inv, SH.mul_one, SH.one_mul] at h2
  exact h2

theorem map_comm {G H : Type} (SG : GroupStruct G) (SH : GroupStruct H)
    (iso : MulEquiv G SG.mul H SH.mul) (a b : G) :
    iso.toFun (SG.comm a b) = SH.comm (iso.toFun a) (iso.toFun b) := by
  unfold comm
  rw [iso.map_mul, iso.map_mul, iso.map_mul, map_inv SG SH iso, map_inv SG SH iso]

/-- Obstruction 3 (2-step solvability): A metabelian group (whose commutators pairwise commute)
    cannot be isomorphic to a group possessing two non-commuting commutators. -/
theorem no_mulEquiv_of_metabelian_vs_nonmetabelian
    {G H : Type} (SG : GroupStruct G) (SH : GroupStruct H)
    (hmeta : ∀ a₁ b₁ a₂ b₂ : G,
      SG.mul (SG.comm a₁ b₁) (SG.comm a₂ b₂) = SG.mul (SG.comm a₂ b₂) (SG.comm a₁ b₁))
    (hnonmeta : ∃ u₁ v₁ u₂ v₂ : H,
      SH.mul (SH.comm u₁ v₁) (SH.comm u₂ v₂) ≠ SH.mul (SH.comm u₂ v₂) (SH.comm u₁ v₁)) :
    MulEquiv G SG.mul H SH.mul → False := by
  intro iso
  rcases hnonmeta with ⟨u₁, v₁, u₂, v₂, hne⟩
  have h := hmeta (iso.invFun u₁) (iso.invFun v₁) (iso.invFun u₂) (iso.invFun v₂)
  have h' : iso.toFun (SG.mul (SG.comm (iso.invFun u₁) (iso.invFun v₁))
                               (SG.comm (iso.invFun u₂) (iso.invFun v₂))) =
            iso.toFun (SG.mul (SG.comm (iso.invFun u₂) (iso.invFun v₂))
                               (SG.comm (iso.invFun u₁) (iso.invFun v₁))) :=
    congrArg iso.toFun h
  rw [iso.map_mul, iso.map_mul,
      map_comm SG SH iso, map_comm SG SH iso,
      iso.right_inv, iso.right_inv, iso.right_inv, iso.right_inv] at h'
  exact hne h'

end GroupStruct

/-! ### Finite List Pigeonhole & Exact Cardinality Non-Bijection -/

section FiniteCardinality

inductive NodupList {α : Type} : List α → Prop where
  | nil  : NodupList []
  | cons : ∀ {a : α} {l : List α}, a ∉ l → NodupList l → NodupList (a :: l)

def nodupBool {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: l => (!l.contains a) && nodupBool l

theorem nodupList_of_nodupBool {α : Type} [DecidableEq α] :
    ∀ {l : List α}, nodupBool l = true → NodupList l
  | [], _ => NodupList.nil
  | a :: l, h => by
    unfold nodupBool at h
    cases hc : l.contains a with
    | true =>
      rw [hc] at h
      contradiction
    | false =>
      rw [hc] at h
      have hsub : nodupBool l = true := by
        simpa using h
      have hnotmem : a ∉ l := by
        intro hm
        have hc' : l.contains a = true := List.contains_iff_mem.mpr hm
        rw [hc] at hc'
        contradiction
      exact NodupList.cons hnotmem (nodupList_of_nodupBool hsub)

theorem nodupList_map {α β : Type} {f : α → β}
    (hinj : ∀ x y : α, f x = f y → x = y) :
    ∀ {l : List α}, NodupList l → NodupList (l.map f)
  | [], NodupList.nil => NodupList.nil
  | a :: l, NodupList.cons hnotmem htl => by
    refine NodupList.cons ?_ (nodupList_map hinj htl)
    intro hm
    rcases List.mem_map.mp hm with ⟨x, hxmem, hfxeq⟩
    have hxa : x = a := hinj x a hfxeq
    rw [hxa] at hxmem
    exact hnotmem hxmem

theorem length_erase_of_mem {α : Type} [DecidableEq α] (a : α) :
    ∀ (l : List α), a ∈ l → l.length = (l.erase a).length + 1
  | [], h => nomatch h
  | b :: t, h => by
    unfold List.erase
    cases hba : (b == a) with
    | true => rfl
    | false =>
      have hne : a ≠ b := by
        intro heq
        have hbtrue : (b == a) = true := beq_iff_eq.mpr heq.symm
        rw [hba] at hbtrue
        contradiction
      cases h with
      | head => exact absurd rfl hne
      | tail _ ht =>
        have ih := length_erase_of_mem a t ht
        simp [ih]

theorem mem_erase_of_ne {α : Type} [DecidableEq α] {a x : α}
    (hne : x ≠ a) : ∀ {l : List α}, x ∈ l → x ∈ l.erase a
  | [], h => nomatch h
  | b :: t, h => by
    unfold List.erase
    cases hba : (b == a) with
    | true =>
      have hbeq : b = a := beq_iff_eq.mp hba
      cases h with
      | head => exact absurd hbeq hne
      | tail _ ht => exact ht
    | false =>
      cases h with
      | head => exact List.Mem.head _
      | tail _ ht => exact List.Mem.tail _ (mem_erase_of_ne hne ht)

theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), NodupList l₁ → (∀ x : α, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, NodupList.cons hnotmem htl, hsub => by
    have hal₂ : a ∈ l₂ := hsub a (List.Mem.head _)
    have hlen : l₂.length = (l₂.erase a).length + 1 := length_erase_of_mem a l₂ hal₂
    have hsub' : ∀ x : α, x ∈ t → x ∈ l₂.erase a := by
      intro x hxt
      have hxne : x ≠ a := by
        intro heq
        rw [heq] at hxt
        exact hnotmem hxt
      exact mem_erase_of_ne hxne (hsub x (List.Mem.tail _ hxt))
    have ih := nodup_length_le t (l₂.erase a) htl hsub'
    rw [hlen]
    exact Nat.succ_le_succ ih

/-- Obstruction 4 (Exact finite cardinality): If `α` and `β` admit duplicate-free complete
    enumerations of distinct lengths, no bijection exists between `α` and `β`. -/
theorem no_bij_of_card_ne {α β : Type} [DecidableEq α] [DecidableEq β]
    (lα : List α) (lβ : List β)
    (hndα : nodupBool lα = true) (hndβ : nodupBool lβ = true)
    (hcovα : ∀ x : α, x ∈ lα) (hcovβ : ∀ y : β, y ∈ lβ)
    (hne : lα.length ≠ lβ.length)
    (f : α → β) (g : β → α)
    (hleft : ∀ x : α, g (f x) = x)
    (hright : ∀ y : β, f (g y) = y) : False := by
  have hinj_f : ∀ x₁ x₂ : α, f x₁ = f x₂ → x₁ = x₂ := by
    intro x₁ x₂ hf
    rw [← hleft x₁, ← hleft x₂, hf]
  have hinj_g : ∀ y₁ y₂ : β, g y₁ = g y₂ → y₁ = y₂ := by
    intro y₁ y₂ hg
    rw [← hright y₁, ← hright y₂, hg]
  have hle1 : lα.length ≤ lβ.length := by
    have hmap := nodupList_map hinj_f (nodupList_of_nodupBool hndα)
    have hlen_map : (lα.map f).length = lα.length := by simp
    rw [← hlen_map]
    exact nodup_length_le (lα.map f) lβ hmap (fun y _ => hcovβ y)
  have hle2 : lβ.length ≤ lα.length := by
    have hmap := nodupList_map hinj_g (nodupList_of_nodupBool hndβ)
    have hlen_map : (lβ.map g).length = lβ.length := by simp
    rw [← hlen_map]
    exact nodup_length_le (lβ.map g) lα hmap (fun x _ => hcovα x)
  exact hne (Nat.le_antisymm hle1 hle2)

end FiniteCardinality

end Conjecture00000007628
