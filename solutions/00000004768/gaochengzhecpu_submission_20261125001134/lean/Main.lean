/-!
# Formal Disproof of Conjecture 00000004768

This file formalizes set partitions of `Fin n`, noncrossing partitions, the
noncrossing partition lattice `NCPartition n` (and full partition lattice
`SetPartition n`) under refinement, poset linear extensions (both list and
bijection formulations), certified dynamic programming over order ideals,
hook-length product formulas, block-size products, and prime-factor obstructions
from first principles in Core Lean 4.19.0 with zero external dependencies and
zero `native_decide`.
-/

namespace Conjecture4768

/-! ## 1. Finite Cardinality and Basic List Combinatorics -/

/-- Duplicate-free list predicate. -/
inductive ListNodup {α : Type u} : List α → Prop where
  | nil : ListNodup []
  | cons {x : α} {xs : List α} : (∀ y ∈ xs, x ≠ y) → ListNodup xs → ListNodup (x :: xs)

/-- Exact finite cardinality `|α| = n` witnessed by a duplicate-free exhaustive list. -/
def HasCardinality (α : Type u) (n : Nat) : Prop :=
  ∃ elems : List α, ListNodup elems ∧ (∀ x : α, x ∈ elems) ∧ elems.length = n

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

theorem mem_of_filter {α : Type u} {p : α → Bool} {x : α} {l : List α}
    (h : x ∈ l.filter p) : x ∈ l :=
  (List.mem_filter.mp h).1

theorem pred_of_filter {α : Type u} {p : α → Bool} {x : α} {l : List α}
    (h : x ∈ l.filter p) : p x = true :=
  (List.mem_filter.mp h).2

theorem nodup_append {α : Type u} :
    ∀ {l₁ l₂ : List α}, ListNodup l₁ → ListNodup l₂ →
      (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) → ListNodup (l₁ ++ l₂)
  | [], _, _, h₂, _ => h₂
  | x :: xs, l₂, ListNodup.cons hnx h₁, h₂, hdisj => by
    refine ListNodup.cons ?_ (nodup_append h₁ h₂ (fun a ha b hb => hdisj a (List.mem_cons_of_mem x ha) b hb))
    intro y hy
    rcases List.mem_append.mp hy with hy1 | hy2
    · exact hnx y hy1
    · exact hdisj x (List.Mem.head xs) y hy2

theorem nodup_map_on {α : Type u} {β : Type v} {f : α → β} :
    ∀ {l : List α}, ListNodup l →
      (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → ListNodup (l.map f)
  | [], _, _ => ListNodup.nil
  | x :: xs, ListNodup.cons hnx hnd, hinj => by
    refine ListNodup.cons ?_ (nodup_map_on hnd (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)))
    intro y hy hfy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact hnx z hz (hinj x (List.Mem.head xs) z (List.mem_cons_of_mem x hz) hfy)

theorem nodup_map {α : Type u} {β : Type v} {f : α → β}
    (hinj : ∀ {a b : α}, f a = f b → a = b) {l : List α} (hnd : ListNodup l) :
    ListNodup (l.map f) :=
  nodup_map_on hnd (fun _ _ _ _ h => hinj h)

theorem nodup_filter {α : Type u} (p : α → Bool) :
    ∀ {l : List α}, ListNodup l → ListNodup (l.filter p)
  | [], _ => ListNodup.nil
  | x :: xs, ListNodup.cons hnx hnd => by
    simp only [List.filter]
    split
    · refine ListNodup.cons ?_ (nodup_filter p hnd)
      intro y hy
      exact hnx y (mem_of_filter hy)
    · exact nodup_filter p hnd

/-- Computable attachment of subtype proofs to list elements (without matching on `Prop`). -/
def subtypeList {α : Type u} {P : α → Prop} :
    ∀ (l : List α), (∀ x ∈ l, P x) → List { x : α // P x }
  | [], _ => []
  | x :: xs, hall =>
    ⟨x, hall x (List.Mem.head xs)⟩ ::
      subtypeList xs (fun y hy => hall y (List.mem_cons_of_mem x hy))

theorem subtypeList_length {α : Type u} {P : α → Prop} :
    ∀ (l : List α) (hall : ∀ x ∈ l, P x),
      (subtypeList l hall).length = l.length
  | [], _ => rfl
  | _ :: xs, hall =>
    congrArg (· + 1) (subtypeList_length xs (fun y hy => hall y (List.mem_cons_of_mem _ hy)))

theorem subtypeList_val_mem {α : Type u} {P : α → Prop} :
    ∀ {l : List α} {hall : ∀ z ∈ l, P z} {u : { z // P z }},
      u ∈ subtypeList l hall → u.val ∈ l
  | [], _, _, h => nomatch h
  | x :: xs, _, _, h => by
    cases h with
    | head => exact List.Mem.head xs
    | tail _ htail => exact List.mem_cons_of_mem x (subtypeList_val_mem htail)

theorem subtypeList_nodup {α : Type u} {P : α → Prop} :
    ∀ (l : List α), ListNodup l → ∀ (hall : ∀ x ∈ l, P x),
      ListNodup (subtypeList l hall)
  | [], _, _ => ListNodup.nil
  | x :: xs, ListNodup.cons hnx hnd, hall => by
    refine ListNodup.cons ?_ (subtypeList_nodup xs hnd (fun y hy => hall y (List.mem_cons_of_mem x hy)))
    intro y hy heq
    exact hnx y.val (subtypeList_val_mem hy) (congrArg Subtype.val heq)

theorem subtypeList_mem {α : Type u} {P : α → Prop} :
    ∀ (l : List α) (hall : ∀ x ∈ l, P x) (u : { x : α // P x }),
      u.val ∈ l → u ∈ subtypeList l hall
  | [], _, _, h => nomatch h
  | x :: xs, hall, ⟨_, _⟩, h => by
    cases h with
    | head => exact List.Mem.head _
    | tail _ hm => exact List.mem_cons_of_mem _ (subtypeList_mem xs _ _ hm)

def listFlatMap {α : Type u} {β : Type v} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ listFlatMap f xs

theorem mem_listFlatMap {α : Type u} {β : Type v} {f : α → List β} {y : β} :
    ∀ {l : List α}, y ∈ listFlatMap f l ↔ ∃ x ∈ l, y ∈ f x
  | [] => ⟨(fun h => nomatch h), (fun ⟨_, hx, _⟩ => nomatch hx)⟩
  | x :: xs => by
    simp only [listFlatMap, List.mem_append, mem_listFlatMap]
    constructor
    · rintro (hy | ⟨z, hz, hy⟩)
      · exact ⟨x, List.Mem.head xs, hy⟩
      · exact ⟨z, List.mem_cons_of_mem x hz, hy⟩
    · rintro ⟨z, hz, hy⟩
      cases hz with
      | head => exact Or.inl hy
      | tail _ hm => exact Or.inr ⟨z, hm, hy⟩

theorem nodup_listFlatMap {α : Type u} {β : Type v} {f : α → List β} :
    ∀ {l : List α}, ListNodup l →
      (∀ x ∈ l, ListNodup (f x)) →
      (∀ x₁ ∈ l, ∀ x₂ ∈ l, x₁ ≠ x₂ → ∀ y ∈ f x₁, ∀ z ∈ f x₂, y ≠ z) →
      ListNodup (listFlatMap f l)
  | [], _, _, _ => ListNodup.nil
  | x :: xs, ListNodup.cons hnx hnd, hall_nd, hdisj => by
    refine nodup_append (hall_nd x (List.Mem.head xs))
      (nodup_listFlatMap hnd (fun a ha => hall_nd a (List.mem_cons_of_mem x ha))
        (fun a ha b hb hab => hdisj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)) ?_
    intro y hy z hz
    rcases mem_listFlatMap.mp hz with ⟨x₂, hx₂, hz₂⟩
    exact hdisj x (List.Mem.head xs) x₂ (List.mem_cons_of_mem x hx₂) (hnx x₂ hx₂) y hy z hz₂

/-! ## 2. Arithmetic, Factorials, Products, and Euclid's Lemma -/

def natFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFactorial n

def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

theorem length_listFlatMap {α : Type u} {β : Type v} (f : α → List β) :
    ∀ (l : List α), (listFlatMap f l).length = listSum (l.map (fun x => (f x).length))
  | [] => rfl
  | x :: xs => by
    simp only [listFlatMap, List.length_append, List.map, listSum]
    rw [length_listFlatMap f xs]

/-- Standard textbook definition of a prime natural number. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def noDivisorInRange (p : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | d, fuel + 1 =>
    if p ≤ d then true
    else (p % d != 0) && noDivisorInRange p (d + 1) fuel

theorem noDivisorInRange_sound {p : Nat} :
    ∀ {d fuel k : Nat}, noDivisorInRange p d fuel = true →
      d ≤ k → k < d + fuel → k < p → ¬ (k ∣ p)
  | d, 0, k, _, hdk, hkf, _ => by omega
  | d, fuel + 1, k, hok, hdk, hkf, hkp => by
    unfold noDivisorInRange at hok
    split at hok
    · omega
    · rcases Bool.and_eq_true_iff.mp hok with ⟨hmod, hrest⟩
      by_cases hkd : k = d
      · subst hkd
        intro hdvd
        rcases hdvd with ⟨q, hq⟩
        have hm0 : (k * q) % k = 0 := Nat.mul_mod_right k q
        rw [← hq] at hm0
        simp [hm0] at hmod
      · exact noDivisorInRange_sound hrest (by omega) (by omega) hkp

theorem isPrime_of_check (p : Nat) (hp2 : 2 ≤ p)
    (hchk : noDivisorInRange p 2 p = true) : IsPrime p := by
  refine ⟨hp2, ?_⟩
  intro d hdvd
  rcases hdvd with ⟨q, hq⟩
  by_cases hd0 : d = 0
  · subst hd0; simp at hq; omega
  · by_cases hd1 : d = 1
    · exact Or.inl hd1
    · by_cases hdp : p ≤ d
      · by_cases hq0 : q = 0
        · subst hq0; simp at hq; omega
        · have hge : d * 1 ≤ d * q := Nat.mul_le_mul_left d (by omega)
          rw [← hq] at hge
          exact Or.inr (by omega)
      · exfalso
        exact noDivisorInRange_sound hchk (by omega) (by omega) (by omega) ⟨q, hq⟩

theorem isPrime_53 : IsPrime 53 :=
  isPrime_of_check 53 (by decide) (by decide)

/-- Gauss's descent proof of Euclid's lemma in Core Lean. -/
theorem euclid_descent {p b : Nat} (hp : IsPrime p) :
    ∀ (r : Nat), 0 < r → r < p → p ∣ r * b → p ∣ b
  | r, hr0, hrp, hdvd => by
    by_cases hr1 : r = 1
    · subst hr1; simpa using hdvd
    · have hmod_lt : p % r < r := Nat.mod_lt p hr0
      by_cases hmod0 : p % r = 0
      · exfalso
        rcases hp.2 r (Nat.dvd_of_mod_eq_zero hmod0) with rfl | rfl
        · exact hr1 rfl
        · exact Nat.lt_irrefl r hrp
      · have hdiv : r * (p / r) + p % r = p := Nat.div_add_mod p r
        rcases hdvd with ⟨k, hk⟩
        have h1 : (r * (p / r) + p % r) * b = p * b := congrArg (· * b) hdiv
        have h2 : (r * (p / r) + p % r) * b = r * (p / r) * b + (p % r) * b :=
          Nat.right_distrib (r * (p / r)) (p % r) b
        have h3 : r * (p / r) * b = p * (k * (p / r)) := by
          calc
            r * (p / r) * b = (p / r) * (r * b) := by
              rw [Nat.mul_comm r (p / r), Nat.mul_assoc]
            _ = (p / r) * (p * k) := by rw [hk]
            _ = p * (k * (p / r)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (p / r) p, Nat.mul_assoc, Nat.mul_comm (p / r) k]
        have hmod_dvd : p ∣ (p % r) * b := by
          refine ⟨b - k * (p / r), ?_⟩
          have hsub := Nat.mul_sub_left_distrib p b (k * (p / r))
          omega
        exact euclid_descent hp (p % r) (by omega) (by omega) hmod_dvd
termination_by r => r

theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases ha : a % p = 0
  · exact Or.inl (Nat.dvd_of_mod_eq_zero ha)
  · right
    have hp_pos : 0 < p := by have := hp.1; omega
    have hlt : a % p < p := Nat.mod_lt a hp_pos
    have hdiv : p * (a / p) + a % p = a := Nat.div_add_mod a p
    rcases h with ⟨k, hk⟩
    have hrem : p ∣ (a % p) * b := by
      have h1 : (p * (a / p) + a % p) * b = a * b := congrArg (· * b) hdiv
      have h2 : (p * (a / p) + a % p) * b = p * ((a / p) * b) + (a % p) * b := by
        rw [Nat.right_distrib, Nat.mul_assoc]
      refine ⟨k - (a / p) * b, ?_⟩
      have hsub := Nat.mul_sub_left_distrib p k ((a / p) * b)
      omega
    exact euclid_descent hp (a % p) (by omega) hlt hrem

theorem IsPrime.le_of_dvd_pos {p x : Nat} (_hp : IsPrime p) (hx : 0 < x) (hdvd : p ∣ x) :
    p ≤ x := by
  rcases hdvd with ⟨k, rfl⟩
  by_cases hk0 : k = 0
  · subst hk0; simp at hx
  · have h1 : p * 1 ≤ p * k := Nat.mul_le_mul_left p (by omega)
    omega

theorem IsPrime.dvd_listProd {p : Nat} (hp : IsPrime p) :
    ∀ {l : List Nat}, p ∣ listProd l → ∃ x ∈ l, p ∣ x
  | [], hdvd => by
    exfalso
    have hle := hp.le_of_dvd_pos (by decide : 0 < 1) hdvd
    have hp2 := hp.1
    omega
  | x :: xs, hdvd => by
    rcases hp.dvd_mul hdvd with hx | hxs
    · exact ⟨x, List.Mem.head xs, hx⟩
    · rcases hp.dvd_listProd hxs with ⟨y, hy, hpy⟩
      exact ⟨y, List.mem_cons_of_mem x hy, hpy⟩

theorem IsPrime.not_dvd_listProd_bounded {p : Nat} (hp : IsPrime p)
    {l : List Nat} (hbnd : ∀ x ∈ l, 0 < x ∧ x < p) :
    ¬ (p ∣ listProd l) := by
  intro hdvd
  rcases hp.dvd_listProd hdvd with ⟨x, hx, hpx⟩
  rcases hbnd x hx with ⟨hx0, hxp⟩
  have hle := hp.le_of_dvd_pos hx0 hpx
  omega

theorem IsPrime.not_dvd_factorial {p : Nat} (hp : IsPrime p) :
    ∀ {m : Nat}, m < p → ¬ (p ∣ natFactorial m)
  | 0, _, hdvd => by
    have hle := hp.le_of_dvd_pos (by decide : 0 < 1) hdvd
    have hp2 := hp.1
    omega
  | m + 1, hlt, hdvd => by
    rcases hp.dvd_mul hdvd with hm1 | hrest
    · have hle := hp.le_of_dvd_pos (by omega : 0 < m + 1) hm1
      omega
    · exact hp.not_dvd_factorial (by omega) hrest

/-! ## 3. Posets, Lattices, and Linear Extensions -/

class Poset (P : Type u) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

scoped infix:50 " ≼ " => Poset.le

class Lattice (L : Type u) extends Poset L where
  inf : L → L → L
  sup : L → L → L
  inf_le_left : ∀ a b : L, (inf a b) ≼ a
  inf_le_right : ∀ a b : L, (inf a b) ≼ b
  le_inf : ∀ {a b c : L}, c ≼ a → c ≼ b → c ≼ (inf a b)
  le_sup_left : ∀ a b : L, a ≼ (sup a b)
  le_sup_right : ∀ a b : L, b ≼ (sup a b)
  sup_le : ∀ {a b c : L}, a ≼ c → b ≼ c → (sup a b) ≼ c

scoped infixl:70 " ⊓ " => Lattice.inf
scoped infixl:65 " ⊔ " => Lattice.sup

def finRange : (n : Nat) → List (Fin n)
  | 0 => []
  | m + 1 => ⟨0, Nat.zero_lt_succ m⟩ :: (finRange m).map Fin.succ

theorem mem_finRange {n : Nat} : ∀ (x : Fin n), x ∈ finRange n := by
  induction n with
  | zero => intro x; exact Fin.elim0 x
  | succ m ih =>
    intro ⟨val, hlt⟩
    cases val with
    | zero => exact List.Mem.head _
    | succ k =>
      have hk : k < m := Nat.lt_of_succ_lt_succ hlt
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨k, hk⟩, ih ⟨k, hk⟩, rfl⟩)

theorem nodup_finRange : ∀ (n : Nat), ListNodup (finRange n)
  | 0 => ListNodup.nil
  | m + 1 => by
    refine ListNodup.cons ?_ (nodup_map (fun {a b} h => Fin.succ_inj.mp h) (nodup_finRange m))
    intro y hy heq
    rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
    have hv := congrArg Fin.val heq
    simp at hv

def listGet {α : Type u} : (l : List α) → Fin l.length → α
  | x :: _, ⟨0, _⟩ => x
  | _ :: xs, ⟨i + 1, hi⟩ => listGet xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem listGet_mem {α : Type u} :
    ∀ (l : List α) (i : Fin l.length), listGet l i ∈ l
  | _ :: xs, ⟨0, _⟩ => List.Mem.head xs
  | x :: xs, ⟨i + 1, hi⟩ => List.mem_cons_of_mem x (listGet_mem xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

theorem mem_iff_exists_listGet {α : Type u} {y : α} :
    ∀ {l : List α}, y ∈ l ↔ ∃ i : Fin l.length, listGet l i = y
  | [] => ⟨(fun h => nomatch h), (fun ⟨i, _⟩ => Fin.elim0 i)⟩
  | x :: xs => by
    constructor
    · intro h
      cases h with
      | head => exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
      | tail _ hm =>
        rcases mem_iff_exists_listGet.mp hm with ⟨⟨i, hi⟩, hget⟩
        exact ⟨⟨i + 1, Nat.succ_lt_succ hi⟩, hget⟩
    · rintro ⟨⟨iv, hi⟩, hget⟩
      cases iv with
      | zero =>
        simp only [listGet] at hget
        subst hget
        exact List.Mem.head xs
      | succ i =>
        exact List.mem_cons_of_mem x
          (mem_iff_exists_listGet.mpr ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hget⟩)

theorem nodup_listGet_inj {α : Type u} :
    ∀ {L : List α}, ListNodup L → ∀ {i j : Fin L.length}, listGet L i = listGet L j → i = j
  | _ :: _, ListNodup.cons _ _, ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | _ :: xs, ListNodup.cons hnx _, ⟨0, _⟩, ⟨j + 1, hj⟩, heq =>
    False.elim (hnx (listGet xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩) (listGet_mem xs _) heq)
  | _ :: xs, ListNodup.cons hnx _, ⟨i + 1, hi⟩, ⟨0, _⟩, heq =>
    False.elim (hnx (listGet xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (listGet_mem xs _) heq.symm)
  | _ :: _, ListNodup.cons _ hnd, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, heq => by
    have hij := nodup_listGet_inj hnd (i := ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      (j := ⟨j, Nat.lt_of_succ_lt_succ hj⟩) heq
    exact Fin.ext (congrArg (· + 1) (congrArg Fin.val hij))

/-- A linear extension of a poset `P` represented as a duplicate-free exhaustive
list `L : List P` respecting the partial order (`L[i] ≼ L[j] → i ≤ j`). -/
def IsLinearExtension (P : Type u) [Poset P] (L : List P) : Prop :=
  ListNodup L ∧
  (∀ x : P, x ∈ L) ∧
  (∀ (i j : Fin L.length), (listGet L i) ≼ (listGet L j) → i.val ≤ j.val)

/-- Exact linear extension count `e(P) = e`. -/
def HasLinearExtensionCount (P : Type u) [Poset P] (e : Nat) : Prop :=
  HasCardinality { L : List P // IsLinearExtension P L } e

theorem hasLinearExtensionCount_unique {P : Type u} [Poset P] {e₁ e₂ : Nat}
    (h₁ : HasLinearExtensionCount P e₁) (h₂ : HasLinearExtensionCount P e₂) : e₁ = e₂ :=
  hasCardinality_unique h₁ h₂

/-- Equivalent order-preserving bijection formulation `f : P ≃ Fin N` of a linear extension. -/
structure LinearExtensionBij (P : Type u) [Poset P] (N : Nat) where
  toFun : P → Fin N
  inj : ∀ {x y : P}, toFun x = toFun y → x = y
  surj : ∀ k : Fin N, ∃ x : P, toFun x = k
  mono : ∀ {x y : P}, x ≼ y → (toFun x).val ≤ (toFun y).val

section BijectionEquivalence
open Classical

noncomputable def indexOfMem {α : Type u} : ∀ (L : List α) (x : α), x ∈ L → Fin L.length
  | y :: ys, x, h =>
    if hxy : x = y then ⟨0, Nat.zero_lt_succ ys.length⟩
    else
      have hxys : x ∈ ys := by
        cases h with
        | head => exact False.elim (hxy rfl)
        | tail _ hm => exact hm
      Fin.succ (indexOfMem ys x hxys)

theorem listGet_indexOfMem {α : Type u} :
    ∀ (L : List α) (x : α) (hx : x ∈ L), listGet L (indexOfMem L x hx) = x
  | _ :: ys, x, _ => by
    unfold indexOfMem
    split
    · next hxy => exact hxy.symm
    · exact listGet_indexOfMem ys x _

theorem finRange_length : ∀ (n : Nat), (finRange n).length = n
  | 0 => rfl
  | m + 1 => by simp [finRange, finRange_length m]

theorem listGet_finRange :
    ∀ (n : Nat) (i : Fin (finRange n).length), (listGet (finRange n) i).val = i.val
  | _ + 1, ⟨0, _⟩ => rfl
  | m + 1, ⟨k + 1, hk⟩ => by
    simp only [finRange, listGet]
    have hmap : ∀ {α β : Type} (f : α → β) (l : List α) (j : Fin l.length),
        listGet (l.map f) ⟨j.val, by simp [j.isLt]⟩ = f (listGet l j) := by
      intro α β f l j
      induction l with
      | nil => exact Fin.elim0 j
      | cons _ as ihl =>
        rcases j with ⟨jv, hj⟩
        cases jv with
        | zero => rfl
        | succ jv' => exact ihl ⟨jv', Nat.lt_of_succ_lt_succ hj⟩
    have hk' : k < (finRange m).length := by
      have hl : (List.map Fin.succ (finRange m)).length = (finRange m).length := List.length_map ..
      simp only [finRange, List.length_cons, hl] at hk
      exact Nat.lt_of_succ_lt_succ hk
    rw [hmap Fin.succ (finRange m) ⟨k, hk'⟩]
    simp [listGet_finRange m ⟨k, hk'⟩]

/-- Forward direction: every list linear extension induces an order-preserving bijection. -/
noncomputable def linearExtensionToBij {P : Type u} [Poset P] {N : Nat}
    (hcard : HasCardinality P N)
    (L : { l : List P // IsLinearExtension P l }) : LinearExtensionBij P N := by
  rcases L with ⟨l, hnd, hall, hmono⟩
  have hlen : l.length = N := hasCardinality_unique ⟨l, hnd, hall, rfl⟩ hcard
  refine
    { toFun := fun x => (indexOfMem l x (hall x)).cast hlen
      inj := ?_
      surj := ?_
      mono := ?_ }
  · intro x y heq
    have hidx : indexOfMem l x (hall x) = indexOfMem l y (hall y) :=
      Fin.ext (by simpa using congrArg Fin.val heq)
    have hx := listGet_indexOfMem l x (hall x)
    have hy := listGet_indexOfMem l y (hall y)
    rw [hidx] at hx
    exact hx.symm.trans hy
  · intro k
    let k' : Fin l.length := k.cast hlen.symm
    refine ⟨listGet l k', ?_⟩
    have hg := listGet_indexOfMem l (listGet l k') (hall (listGet l k'))
    have hidx := nodup_listGet_inj hnd hg
    exact Fin.ext (by simpa using congrArg Fin.val hidx)
  · intro x y hxy
    have hx := listGet_indexOfMem l x (hall x)
    have hy := listGet_indexOfMem l y (hall y)
    have hle : (listGet l (indexOfMem l x (hall x))) ≼ (listGet l (indexOfMem l y (hall y))) := by
      rw [hx, hy]; exact hxy
    exact hmono _ _ hle

/-- Inverse direction: every order-preserving bijection `f : P → Fin N` induces a
list linear extension `[f⁻¹(0), ..., f⁻¹(N-1)]`. -/
noncomputable def bijToLinearExtension {P : Type u} [Poset P] {N : Nat}
    (b : LinearExtensionBij P N) : { l : List P // IsLinearExtension P l } := by
  let inv : Fin N → P := fun k => choose (b.surj k)
  have hinv : ∀ k : Fin N, b.toFun (inv k) = k := fun k => choose_spec (b.surj k)
  let l := (finRange N).map inv
  refine ⟨l, ?_, ?_, ?_⟩
  · refine nodup_map (fun {k₁ k₂} heq => ?_) (nodup_finRange N)
    have h1 := congrArg b.toFun heq
    rw [hinv k₁, hinv k₂] at h1
    exact h1
  · intro x
    refine List.mem_map.mpr ⟨b.toFun x, mem_finRange (b.toFun x), ?_⟩
    exact b.inj (hinv (b.toFun x))
  · intro i j hle
    have hmap : ∀ (r : List (Fin N)) (idx : Fin r.length),
        listGet (r.map inv) ⟨idx.val, by simp [idx.isLt]⟩ = inv (listGet r idx) := by
      intro r idx
      induction r with
      | nil => exact Fin.elim0 idx
      | cons _ as ih =>
        rcases idx with ⟨iv, hi⟩
        cases iv with
        | zero => rfl
        | succ iv' => exact ih ⟨iv', Nat.lt_of_succ_lt_succ hi⟩
    have hlen_fr : l.length = (finRange N).length := List.length_map ..
    let i' : Fin (finRange N).length := ⟨i.val, hlen_fr ▸ i.isLt⟩
    let j' : Fin (finRange N).length := ⟨j.val, hlen_fr ▸ j.isLt⟩
    have hgi : listGet l i = inv (listGet (finRange N) i') := hmap (finRange N) i'
    have hgj : listGet l j = inv (listGet (finRange N) j') := hmap (finRange N) j'
    rw [hgi, hgj] at hle
    have hm := b.mono hle
    rw [hinv, hinv, listGet_finRange N i', listGet_finRange N j'] at hm
    exact hm

end BijectionEquivalence

/-! ## 4. Certified Layer-by-Layer Order-Ideal Dynamic Programming Engine -/

def IsLinearExtOf (P : Type u) [Poset P] (I : P → Prop) (L : List P) : Prop :=
  ListNodup L ∧
  (∀ x : P, x ∈ L ↔ I x) ∧
  (∀ (i j : Fin L.length), (listGet L i) ≼ (listGet L j) → i.val ≤ j.val)

theorem isLinearExtOf_univ_iff (P : Type u) [Poset P] (L : List P) :
    IsLinearExtOf P (fun _ => True) L ↔ IsLinearExtension P L := by
  unfold IsLinearExtOf IsLinearExtension
  simp

def IsLowerSet (P : Type u) [Poset P] (I : P → Prop) : Prop :=
  ∀ {x y : P}, I y → x ≼ y → I x

theorem listGet_append_left {α : Type u} :
    ∀ (l₁ l₂ : List α) (i : Fin l₁.length),
      listGet (l₁ ++ l₂) ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by simp)⟩ = listGet l₁ i
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: xs, l₂, ⟨i + 1, hi⟩ =>
    listGet_append_left xs l₂ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem listGet_append_singleton_last {α : Type u} :
    ∀ (l : List α) (z : α),
      listGet (l ++ [z]) ⟨l.length, by simp⟩ = z
  | [], _ => rfl
  | _ :: xs, z => listGet_append_singleton_last xs z

theorem list_split_last {α : Type u} :
    ∀ (l : List α), l ≠ [] → ∃ (init : List α) (z : α), l = init ++ [z]
  | [], h => False.elim (h rfl)
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: ys, _ => by
    rcases list_split_last (y :: ys) (by simp) with ⟨init, z, heq⟩
    exact ⟨x :: init, z, by simp [heq]⟩

theorem append_singleton_inj {α : Type u} :
    ∀ {l₁ l₂ : List α} {z₁ z₂ : α}, l₁ ++ [z₁] = l₂ ++ [z₂] → l₁ = l₂ ∧ z₁ = z₂
  | [], [], _, _, h => ⟨rfl, List.cons.inj h |>.1⟩
  | [], _ :: _, _, _, h => by
    have hlen := congrArg List.length h
    simp at hlen
  | _ :: _, [], _, _, h => by
    have hlen := congrArg List.length h
    simp at hlen
  | _ :: _, _ :: _, _, _, h => by
    rcases List.cons.inj h with ⟨rfl, htail⟩
    rcases append_singleton_inj htail with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem isLinearExtOf_append_maximal {P : Type u} [Poset P]
    {I : P → Prop} {z : P}
    (hzI : I z) (hzmax : ∀ y : P, I y → z ≼ y → y = z) (init : List P) :
    IsLinearExtOf P (fun x => I x ∧ x ≠ z) init → IsLinearExtOf P I (init ++ [z]) := by
  rintro ⟨hnd, hmem, hmono⟩
  have hz_not_init : z ∉ init := fun hz => (hmem z).mp hz |>.2 rfl
  refine ⟨?_, ?_, ?_⟩
  · exact nodup_append hnd (ListNodup.cons (fun _ h => nomatch h) ListNodup.nil)
      (fun x hx y hy heq => by
        cases hy with
        | head => subst heq; exact hz_not_init hx
        | tail _ hm => cases hm)
  · intro x
    rw [List.mem_append]
    constructor
    · rintro (hx | hx)
      · exact ((hmem x).mp hx).1
      · cases hx with
        | head => exact hzI
        | tail _ hm => cases hm
    · intro hxI
      by_cases hxz : x = z
      · subst hxz; exact Or.inr (List.Mem.head [])
      · exact Or.inl ((hmem x).mpr ⟨hxI, hxz⟩)
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hle
    have hlen : (init ++ [z]).length = init.length + 1 := by simp
    by_cases hj_last : j = init.length
    · change i ≤ j; omega
    · have hj_lt : j < init.length := by omega
      have hgj : listGet (init ++ [z]) ⟨j, hj⟩ = listGet init ⟨j, hj_lt⟩ :=
        listGet_append_left init [z] ⟨j, hj_lt⟩
      by_cases hi_last : i = init.length
      · exfalso
        subst hi_last
        have hgi : listGet (init ++ [z]) ⟨init.length, hi⟩ = z :=
          listGet_append_singleton_last init z
        rw [hgi, hgj] at hle
        have hj_mem : listGet init ⟨j, hj_lt⟩ ∈ init := listGet_mem init ⟨j, hj_lt⟩
        rcases (hmem _).mp hj_mem with ⟨hjI, hj_nez⟩
        exact hj_nez (hzmax _ hjI hle)
      · have hi_lt : i < init.length := by omega
        have hgi : listGet (init ++ [z]) ⟨i, hi⟩ = listGet init ⟨i, hi_lt⟩ :=
          listGet_append_left init [z] ⟨i, hi_lt⟩
        rw [hgi, hgj] at hle
        exact hmono ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hle

theorem isLinearExtOf_split_last {P : Type u} [Poset P]
    {I : P → Prop} {init : List P} {z : P}
    (hL : IsLinearExtOf P I (init ++ [z])) :
    I z ∧ (∀ y : P, I y → z ≼ y → y = z) ∧ IsLinearExtOf P (fun x => I x ∧ x ≠ z) init := by
  rcases hL with ⟨hnd, hmem, hmono⟩
  have hlen : (init ++ [z]).length = init.length + 1 := by simp
  have hz_mem : z ∈ init ++ [z] := by simp
  have hzI : I z := (hmem z).mp hz_mem
  have hz_not_init : z ∉ init := by
    intro hzin
    rcases mem_iff_exists_listGet.mp hzin with ⟨⟨i, hi⟩, hgi⟩
    have h1 : listGet (init ++ [z]) ⟨i, by omega⟩ = z := by
      rw [listGet_append_left init [z] ⟨i, hi⟩]; exact hgi
    have h2 : listGet (init ++ [z]) ⟨init.length, by omega⟩ = z :=
      listGet_append_singleton_last init z
    have hinj := nodup_listGet_inj hnd (h1.trans h2.symm)
    have hval := congrArg Fin.val hinj
    dsimp only at hval
    omega
  have hnd_init : ListNodup init := by
    have hrec : ∀ (l : List P), ListNodup (l ++ [z]) → ListNodup l := by
      intro l hl
      induction l with
      | nil => exact ListNodup.nil
      | cons a as ih =>
        cases hl with
        | cons hna htail =>
          exact ListNodup.cons (fun b hb => hna b (List.mem_append.mpr (Or.inl hb))) (ih htail)
    exact hrec init hnd
  refine ⟨hzI, ?_, hnd_init, ?_, ?_⟩
  · intro y hyI hzy
    have hy_mem : y ∈ init ++ [z] := (hmem y).mpr hyI
    rcases mem_iff_exists_listGet.mp hy_mem with ⟨⟨j, hj⟩, hgj⟩
    have hgz : listGet (init ++ [z]) ⟨init.length, by omega⟩ = z :=
      listGet_append_singleton_last init z
    have hle : (listGet (init ++ [z]) ⟨init.length, by omega⟩) ≼ (listGet (init ++ [z]) ⟨j, hj⟩) := by
      rw [hgz, hgj]; exact hzy
    have hij := hmono ⟨init.length, by omega⟩ ⟨j, hj⟩ hle
    change init.length ≤ j at hij
    have hjeq : j = init.length := by omega
    subst hjeq
    rw [← hgj, hgz]
  · intro x
    constructor
    · intro hx
      exact ⟨(hmem x).mp (List.mem_append.mpr (Or.inl hx)), fun hxz => by subst hxz; exact hz_not_init hx⟩
    · rintro ⟨hxI, hxz⟩
      rcases List.mem_append.mp ((hmem x).mpr hxI) with hx | hx
      · exact hx
      · cases hx with
        | head => exact False.elim (hxz rfl)
        | tail _ hm => cases hm
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hle
    have hgi := listGet_append_left init [z] ⟨i, hi⟩
    have hgj := listGet_append_left init [z] ⟨j, hj⟩
    have hle' : (listGet (init ++ [z]) ⟨i, by omega⟩) ≼ (listGet (init ++ [z]) ⟨j, by omega⟩) := by
      rw [hgi, hgj]; exact hle
    exact hmono ⟨i, by omega⟩ ⟨j, by omega⟩ hle'

def beqBoolList : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && beqBoolList as bs
  | _, _ => false

theorem beqBoolList_iff : ∀ {l₁ l₂ : List Bool}, beqBoolList l₁ l₂ = true ↔ l₁ = l₂
  | [], [] => ⟨(fun _ => rfl), (fun _ => rfl)⟩
  | [], _ :: _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, _ :: _ => by
    simp only [beqBoolList, Bool.and_eq_true_iff, beq_iff_eq]
    exact ⟨(fun ⟨h1, h2⟩ => by rw [h1, beqBoolList_iff.mp h2]),
      (fun h => ⟨List.cons.inj h |>.1, beqBoolList_iff.mpr (List.cons.inj h |>.2)⟩)⟩

def memMask {P : Type u} [DecidableEq P] : List P → List Bool → P → Bool
  | x :: xs, true :: bs, y => decide (y = x) || memMask xs bs y
  | _ :: xs, false :: bs, y => memMask xs bs y
  | _, _, _ => false

def boolGet : List Bool → Nat → Bool
  | b :: _, 0 => b
  | _ :: bs, k + 1 => boolGet bs k
  | [], _ => false

def rowGet : List (List Bool) → Nat → List Bool
  | r :: _, 0 => r
  | _ :: rs, i + 1 => rowGet rs i
  | [], _ => []

def buildAdjMatrix {P : Type u} (elems : List P) (leBool : P → P → Bool) : List (List Bool) :=
  elems.map (fun x => elems.map (fun y => leBool x y))

def adjLookup (adj : List (List Bool)) (i j : Nat) : Bool :=
  boolGet (rowGet adj i) j

theorem boolGet_map {α : Type u} (f : α → Bool) :
    ∀ (l : List α) (j : Fin l.length), boolGet (l.map f) j.val = f (listGet l j)
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: xs, ⟨j + 1, hj⟩ => boolGet_map f xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩

theorem rowGet_map {α : Type u} (f : α → List Bool) :
    ∀ (l : List α) (i : Fin l.length), rowGet (l.map f) i.val = f (listGet l i)
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: xs, ⟨i + 1, hi⟩ => rowGet_map f xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem adjLookup_buildAdjMatrix {P : Type u} (elems : List P) (leBool : P → P → Bool)
    (i j : Fin elems.length) :
    adjLookup (buildAdjMatrix elems leBool) i.val j.val = leBool (listGet elems i) (listGet elems j) := by
  unfold adjLookup buildAdjMatrix
  rw [rowGet_map _ elems i, boolGet_map _ elems j]

def clearAt : List Bool → Nat → List Bool
  | _ :: bs, 0 => false :: bs
  | b :: bs, k + 1 => b :: clearAt bs k
  | [], _ => []

def setAtTrue : List Bool → Nat → List Bool
  | _ :: bs, 0 => true :: bs
  | b :: bs, k + 1 => b :: setAtTrue bs k
  | [], _ => []

theorem clearAt_length : ∀ (b : List Bool) (k : Nat), (clearAt b k).length = b.length
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, k + 1 => congrArg (· + 1) (clearAt_length bs k)

theorem memMask_replicate_false {P : Type u} [DecidableEq P] :
    ∀ (elems : List P) (y : P), memMask elems (List.replicate elems.length false) y = false
  | [], _ => rfl
  | _ :: xs, y => memMask_replicate_false xs y

theorem memMask_replicate_true {P : Type u} [DecidableEq P] :
    ∀ {elems : List P} {y : P}, y ∈ elems → memMask elems (List.replicate elems.length true) y = true
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    simp only [List.length_cons, List.replicate, memMask]
    cases h with
    | head => simp
    | tail _ hm => rw [memMask_replicate_true hm]; simp

theorem memMask_iff_exists_index {P : Type u} [DecidableEq P] :
    ∀ (elems : List P) (b : List Bool), ListNodup elems → b.length = elems.length → ∀ (y : P),
      memMask elems b y = true ↔
        ∃ i : Fin elems.length, boolGet b i.val = true ∧ listGet elems i = y
  | [], [], _, _, _ => ⟨(fun h => nomatch h), (fun ⟨i, _⟩ => Fin.elim0 i)⟩
  | _ :: xs, flag :: bs, ListNodup.cons _ hnd, hlen, y => by
    have hlen' : bs.length = xs.length := Nat.succ.inj hlen
    cases flag with
    | false =>
      simp only [memMask]
      rw [memMask_iff_exists_index xs bs hnd hlen' y]
      constructor
      · rintro ⟨⟨i, hi⟩, hb, hg⟩
        exact ⟨⟨i + 1, Nat.succ_lt_succ hi⟩, hb, hg⟩
      · rintro ⟨⟨iv, hi⟩, hb, hg⟩
        cases iv with
        | zero => simp [boolGet] at hb
        | succ i => exact ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hb, hg⟩
    | true =>
      simp only [memMask, Bool.or_eq_true, decide_eq_true_eq]
      rw [memMask_iff_exists_index xs bs hnd hlen' y]
      constructor
      · rintro (rfl | ⟨⟨i, hi⟩, hb, hg⟩)
        · exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, rfl⟩
        · exact ⟨⟨i + 1, Nat.succ_lt_succ hi⟩, hb, hg⟩
      · rintro ⟨⟨iv, hi⟩, hb, hg⟩
        cases iv with
        | zero =>
          simp only [listGet] at hg
          exact Or.inl hg.symm
        | succ i =>
          exact Or.inr ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hb, hg⟩

theorem boolGet_clearAt :
    ∀ (b : List Bool) (k j : Nat),
      boolGet (clearAt b k) j = (if j = k then false else boolGet b j)
  | [], _, _ => by split <;> rfl
  | _ :: _, 0, 0 => rfl
  | _ :: _, 0, _ + 1 => rfl
  | _ :: _, _ + 1, 0 => rfl
  | _ :: bs, k + 1, j + 1 => by
    by_cases hjk : j = k
    · subst hjk
      simp [clearAt, boolGet, boolGet_clearAt bs j j]
    · have hjk' : j + 1 ≠ k + 1 := by omega
      simp [clearAt, boolGet, boolGet_clearAt bs k j, hjk, hjk']

theorem memMask_clearAt {P : Type u} [DecidableEq P]
    {elems : List P} {b : List Bool} (hnd : ListNodup elems) (hlen : b.length = elems.length)
    (k : Fin elems.length) (y : P) :
    (memMask elems (clearAt b k.val) y = true) ↔
      (memMask elems b y = true ∧ y ≠ listGet elems k) := by
  have hclen : (clearAt b k.val).length = elems.length := (clearAt_length b k.val).trans hlen
  rw [memMask_iff_exists_index elems (clearAt b k.val) hnd hclen y,
      memMask_iff_exists_index elems b hnd hlen y]
  constructor
  · rintro ⟨i, hbi, hgi⟩
    rw [boolGet_clearAt] at hbi
    split at hbi
    · cases hbi
    · next hne =>
      refine ⟨⟨i, hbi, hgi⟩, ?_⟩
      intro hy
      rw [← hgi] at hy
      have hik := nodup_listGet_inj hnd hy
      exact hne (congrArg Fin.val hik)
  · rintro ⟨⟨i, hbi, hgi⟩, hyne⟩
    refine ⟨i, ?_, hgi⟩
    rw [boolGet_clearAt]
    split
    · next heq =>
      have hik : i = k := Fin.ext heq
      subst hik
      exact False.elim (hyne hgi.symm)
    · exact hbi

def lookupBoolList (key : List Bool) : List (List Bool × Nat) → Option Nat
  | [] => none
  | (b, v) :: rest => if beqBoolList key b then some v else lookupBoolList key rest

theorem lookupBoolList_mem {key : List Bool} {v : Nat} :
    ∀ {tbl : List (List Bool × Nat)}, lookupBoolList key tbl = some v → (key, v) ∈ tbl
  | [], h => nomatch h
  | (b, w) :: rest, h => by
    unfold lookupBoolList at h
    split at h
    · next heq =>
      have hkb : key = b := beqBoolList_iff.mp heq
      subst hkb
      have hvw : w = v := Option.some.inj h
      subst hvw
      exact List.Mem.head rest
    · exact List.mem_cons_of_mem _ (lookupBoolList_mem h)

/-- Fast index-only lower-set check using the precomputed adjacency matrix `adj`. -/
def checkLowerSetAdj (m : Nat) (adj : List (List Bool)) (b : List Bool) : Bool :=
  (finRange m).all fun j =>
    if boolGet b j.val then
      (finRange m).all fun i =>
        if adjLookup adj i.val j.val then boolGet b i.val else true
    else true

theorem checkLowerSetAdj_sound {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} (hnd : ListNodup elems) (hall : ∀ x : P, x ∈ elems)
    {leBool : P → P → Bool} (hle : ∀ x y : P, leBool x y = true ↔ x ≼ y)
    {b : List Bool} (hlen : b.length = elems.length)
    (hchk : checkLowerSetAdj elems.length (buildAdjMatrix elems leBool) b = true) :
    IsLowerSet P (fun x => memMask elems b x = true) := by
  intro x y hy hxy
  rcases (memMask_iff_exists_index elems b hnd hlen y).mp hy with ⟨j, hbj, hgj⟩
  rcases mem_iff_exists_listGet.mp (hall x) with ⟨i, hgi⟩
  have hj_all := List.all_eq_true.mp hchk j (mem_finRange j)
  rw [if_pos hbj] at hj_all
  have hi_all := List.all_eq_true.mp hj_all i (mem_finRange i)
  have hadj : adjLookup (buildAdjMatrix elems leBool) i.val j.val = true := by
    rw [adjLookup_buildAdjMatrix, hgi, hgj]
    exact (hle x y).mpr hxy
  rw [if_pos hadj] at hi_all
  exact (memMask_iff_exists_index elems b hnd hlen x).mpr ⟨i, hi_all, hgi⟩

def isMaximalIndexAdj (m : Nat) (adj : List (List Bool)) (b : List Bool) (k : Fin m) : Bool :=
  boolGet b k.val &&
  (finRange m).all fun j =>
    if boolGet b j.val && decide (j ≠ k) then
      !adjLookup adj k.val j.val
    else true

def maximalIndicesAdj (m : Nat) (adj : List (List Bool)) (b : List Bool) : List (Fin m) :=
  (finRange m).filter (isMaximalIndexAdj m adj b)

inductive BoolTrie : Type where
  | empty : BoolTrie
  | leaf : Nat → BoolTrie
  | node : BoolTrie → BoolTrie → BoolTrie

def lookupTrie : List Bool → BoolTrie → Option Nat
  | [], BoolTrie.leaf v => some v
  | false :: bs, BoolTrie.node l _ => lookupTrie bs l
  | true :: bs, BoolTrie.node _ r => lookupTrie bs r
  | _, _ => none

def trieSet : List Bool → Nat → BoolTrie → BoolTrie
  | [], v, _ => BoolTrie.leaf v
  | false :: bs, v, BoolTrie.node l r => BoolTrie.node (trieSet bs v l) r
  | true :: bs, v, BoolTrie.node l r => BoolTrie.node l (trieSet bs v r)
  | false :: bs, v, _ => BoolTrie.node (trieSet bs v BoolTrie.empty) BoolTrie.empty
  | true :: bs, v, _ => BoolTrie.node BoolTrie.empty (trieSet bs v BoolTrie.empty)

def buildLookupTrie : List (List Bool × Nat) → BoolTrie
  | [] => BoolTrie.empty
  | (b, v) :: rest => trieSet b v (buildLookupTrie rest)

theorem lookupTrie_empty : ∀ (k : List Bool), lookupTrie k BoolTrie.empty = none
  | [] => rfl
  | false :: _ => rfl
  | true :: _ => rfl

theorem lookupTrie_trieSet {v : Nat} :
    ∀ (key k' : List Bool) (w : Nat) (t : BoolTrie),
      lookupTrie key (trieSet k' w t) = some v →
      (key = k' ∧ v = w) ∨ lookupTrie key t = some v := by
  intro key
  induction key with
  | nil =>
    intro k' w t hv
    cases k' with
    | nil => exact Or.inl ⟨rfl, (Option.some.inj hv).symm⟩
    | cons b _ => cases b <;> cases t <;> cases hv
  | cons b ks ih =>
    intro k' w t hv
    cases k' with
    | nil => cases b <;> cases hv
    | cons b' ks' =>
      cases b <;> cases b' <;> cases t
      · simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w BoolTrie.empty hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (false :: ·) hk, hvw⟩
        · rw [lookupTrie_empty] at hr; cases hr
      · simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w BoolTrie.empty hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (false :: ·) hk, hvw⟩
        · rw [lookupTrie_empty] at hr; cases hr
      · next l _ =>
        simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w l hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (false :: ·) hk, hvw⟩
        · exact Or.inr hr
      · simp only [trieSet, lookupTrie] at hv; cases hv
      · simp only [trieSet, lookupTrie] at hv; cases hv
      · exact Or.inr hv
      · simp only [trieSet, lookupTrie] at hv; cases hv
      · simp only [trieSet, lookupTrie] at hv; cases hv
      · exact Or.inr hv
      · simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w BoolTrie.empty hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (true :: ·) hk, hvw⟩
        · rw [lookupTrie_empty] at hr; cases hr
      · simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w BoolTrie.empty hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (true :: ·) hk, hvw⟩
        · rw [lookupTrie_empty] at hr; cases hr
      · next _ r =>
        simp only [trieSet, lookupTrie] at hv
        rcases ih ks' w r hv with ⟨hk, hvw⟩ | hr
        · exact Or.inl ⟨congrArg (true :: ·) hk, hvw⟩
        · exact Or.inr hr

theorem lookupTrie_buildLookupTrie_mem {key : List Bool} {v : Nat} :
    ∀ {tbl : List (List Bool × Nat)},
      lookupTrie key (buildLookupTrie tbl) = some v → (key, v) ∈ tbl
  | [], h => by rw [buildLookupTrie, lookupTrie_empty] at h; cases h
  | (b, w) :: rest, h => by
    rcases lookupTrie_trieSet key b w (buildLookupTrie rest) h with ⟨rfl, rfl⟩ | hr
    · exact List.Mem.head rest
    · exact List.mem_cons_of_mem _ (lookupTrie_buildLookupTrie_mem hr)

def sumChildLookups {m : Nat} (prevTrie : BoolTrie)
    (b : List Bool) : List (Fin m) → Option Nat
  | [] => some 0
  | k :: ks =>
    match lookupTrie (clearAt b k.val) prevTrie, sumChildLookups prevTrie b ks with
    | some v, some s => some (v + s)
    | _, _ => none

def checkLayerEntryAdj (m : Nat) (adj : List (List Bool))
    (prevTrie : BoolTrie) (entry : List Bool × Nat) : Bool :=
  let (b, val) := entry
  (b.length == m) &&
  (b.any id) &&
  checkLowerSetAdj m adj b &&
  match sumChildLookups prevTrie b (maximalIndicesAdj m adj b) with
  | some s => s == val
  | none => false

def checkAllLayersAdj (m : Nat) (adj : List (List Bool)) :
    List (List Bool × Nat) → List (List (List Bool × Nat)) → Bool
  | _, [] => true
  | prevLayer, nextLayer :: rest =>
    let prevTrie := buildLookupTrie prevLayer
    nextLayer.all (checkLayerEntryAdj m adj prevTrie) &&
    checkAllLayersAdj m adj nextLayer rest

def trieInsertAdd : List Bool → Nat → BoolTrie → BoolTrie
  | [], v, BoolTrie.leaf w => BoolTrie.leaf (w + v)
  | [], v, _ => BoolTrie.leaf v
  | false :: bs, v, BoolTrie.node l r => BoolTrie.node (trieInsertAdd bs v l) r
  | true :: bs, v, BoolTrie.node l r => BoolTrie.node l (trieInsertAdd bs v r)
  | false :: bs, v, _ => BoolTrie.node (trieInsertAdd bs v BoolTrie.empty) BoolTrie.empty
  | true :: bs, v, _ => BoolTrie.node BoolTrie.empty (trieInsertAdd bs v BoolTrie.empty)

def trieToListAux (revPrefix : List Bool) : BoolTrie → List (List Bool × Nat) → List (List Bool × Nat)
  | BoolTrie.empty, acc => acc
  | BoolTrie.leaf v, acc => (revPrefix.reverse, v) :: acc
  | BoolTrie.node l r, acc =>
    trieToListAux (false :: revPrefix) l (trieToListAux (true :: revPrefix) r acc)

def canAddElementAdj (m : Nat) (adj : List (List Bool)) (b : List Bool) (k : Fin m) : Bool :=
  (!boolGet b k.val) &&
  (finRange m).all fun j =>
    if decide (j ≠ k) && adjLookup adj j.val k.val then
      boolGet b j.val
    else true

def stepLayerTrieAux (m : Nat) (adj : List (List Bool)) (idxs : List (Fin m)) :
    List (List Bool × Nat) → BoolTrie → BoolTrie
  | [], trie => trie
  | (b, v) :: rest, trie =>
    let trie' := idxs.foldl (fun t k =>
      if canAddElementAdj m adj b k then
        trieInsertAdd (setAtTrue b k.val) v t
      else t
    ) trie
    stepLayerTrieAux m adj idxs rest trie'

def stepLayerAdj (m : Nat) (adj : List (List Bool))
    (curLayer : List (List Bool × Nat)) : List (List Bool × Nat) :=
  let trie := stepLayerTrieAux m adj (finRange m) curLayer BoolTrie.empty
  trieToListAux [] trie []

def buildLayersAdj (m : Nat) (adj : List (List Bool)) :
    Nat → List (List Bool × Nat) → List (List (List Bool × Nat))
  | 0, _ => []
  | fuel + 1, cur =>
    let nxt := stepLayerAdj m adj cur
    nxt :: buildLayersAdj m adj fuel nxt

def verifyPosetLinExtCount {P : Type u} (elems : List P)
    (leBool : P → P → Bool) (expected : Nat) : Bool :=
  let m := elems.length
  let adj := buildAdjMatrix elems leBool
  let layer0 := [(List.replicate m false, 1)]
  let layers := buildLayersAdj m adj m layer0
  checkAllLayersAdj m adj layer0 layers &&
  let finalLayer := (layer0 :: layers).getLast (by simp)
  lookupTrie (List.replicate m true) (buildLookupTrie finalLayer) == some expected

section LayerDPSoundness
open Classical

def ValidDPEntry {P : Type u} [Poset P] [DecidableEq P]
    (elems : List P) (entry : List Bool × Nat) : Prop :=
  entry.1.length = elems.length ∧
  IsLowerSet P (fun x => memMask elems entry.1 x = true) ∧
  HasCardinality { L : List P // IsLinearExtOf P (fun x => memMask elems entry.1 x = true) L } entry.2

theorem validDPEntry_empty {P : Type u} [Poset P] [DecidableEq P] (elems : List P) :
    ValidDPEntry elems (List.replicate elems.length false, 1) := by
  refine ⟨List.length_replicate .., ?_, ?_⟩
  · intro x y hy _
    dsimp only at hy
    rw [memMask_replicate_false] at hy
    cases hy
  · have hnil : IsLinearExtOf P (fun x => memMask elems (List.replicate elems.length false) x = true) [] := by
      refine ⟨ListNodup.nil, ?_, fun i => Fin.elim0 i⟩
      intro x
      dsimp only
      rw [memMask_replicate_false]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    refine ⟨[⟨[], hnil⟩], ListNodup.cons (fun _ h => nomatch h) ListNodup.nil, ?_, rfl⟩
    rintro ⟨L, _, hmem, _⟩
    cases L with
    | nil => exact List.Mem.head []
    | cons x xs =>
      exfalso
      have hx := (hmem x).mp (List.Mem.head xs)
      dsimp only at hx
      rw [memMask_replicate_false] at hx
      cases hx

theorem sumChildLookups_children {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} {prevLayer : List (List Bool × Nat)}
    (hprev : ∀ e ∈ prevLayer, ValidDPEntry elems e)
    {b : List Bool} :
    ∀ {ks : List (Fin elems.length)} {s : Nat},
      ListNodup ks →
      sumChildLookups (buildLookupTrie prevLayer) b ks = some s →
      ∃ cs : Fin elems.length → Nat,
        (∀ k ∈ ks, ValidDPEntry elems (clearAt b k.val, cs k)) ∧
        listSum (ks.map cs) = s
  | [], s, _, hs => by
    simp only [sumChildLookups] at hs
    have hs0 : 0 = s := Option.some.inj hs
    subst hs0
    exact ⟨(fun _ => 0), ⟨(fun _ hk => nomatch hk), rfl⟩⟩
  | k :: ks, s, ListNodup.cons hnk hnd, hs => by
    unfold sumChildLookups at hs
    cases hlk : lookupTrie (clearAt b k.val) (buildLookupTrie prevLayer) with
    | none => rw [hlk] at hs; cases hs
    | some vk =>
      rw [hlk] at hs
      cases hrest : sumChildLookups (buildLookupTrie prevLayer) b ks with
      | none => rw [hrest] at hs; cases hs
      | some srest =>
        rw [hrest] at hs
        have hsum : vk + srest = s := Option.some.inj hs
        rcases sumChildLookups_children hprev hnd hrest with ⟨cs', hcs_valid, hcs_sum⟩
        refine ⟨fun i => if i = k then vk else cs' i, ?_, ?_⟩
        · intro j hj
          cases hj with
          | head =>
            simp only [↓reduceIte]
            exact hprev _ (lookupTrie_buildLookupTrie_mem hlk)
          | tail _ hm =>
            have hjne : j ≠ k := fun h => hnk j hm h.symm
            simp only [hjne, ↓reduceIte]
            exact hcs_valid j hm
        · have hmap : ks.map (fun i => if i = k then vk else cs' i) = ks.map cs' := by
            have hrec : ∀ (ms : List (Fin elems.length)), (∀ y ∈ ms, k ≠ y) →
                ms.map (fun i => if i = k then vk else cs' i) = ms.map cs' := by
              intro ms hnot
              induction ms with
              | nil => rfl
              | cons m ms' ih =>
                have hmk : m ≠ k := fun h => hnot m (List.Mem.head ms') h.symm
                simp only [List.map, hmk, ↓reduceIte]
                exact congrArg (cs' m :: ·) (ih (fun y hy => hnot y (List.mem_cons_of_mem m hy)))
            exact hrec ks hnk
          simp only [List.map, ↓reduceIte, listSum, hmap, hcs_sum, hsum]

theorem any_true_exists_index :
    ∀ {b : List Bool}, b.any id = true → ∃ k : Nat, k < b.length ∧ boolGet b k = true
  | [], h => nomatch h
  | true :: bs, _ => ⟨0, Nat.zero_lt_succ bs.length, rfl⟩
  | false :: bs, h => by
    simp only [List.any, id_eq, Bool.false_or] at h
    rcases any_true_exists_index h with ⟨k, hk, hbg⟩
    exact ⟨k + 1, Nat.succ_lt_succ hk, hbg⟩

theorem isMaximalIndexAdj_iff {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} (hnd : ListNodup elems)
    {leBool : P → P → Bool} (hle : ∀ x y : P, leBool x y = true ↔ x ≼ y)
    {b : List Bool} (hlen : b.length = elems.length) (k : Fin elems.length) :
    isMaximalIndexAdj elems.length (buildAdjMatrix elems leBool) b k = true ↔
      (memMask elems b (listGet elems k) = true ∧
       ∀ y : P, memMask elems b y = true → (listGet elems k) ≼ y → y = listGet elems k) := by
  unfold isMaximalIndexAdj
  rw [Bool.and_eq_true_iff]
  constructor
  · rintro ⟨hbk, hall_j⟩
    refine ⟨(memMask_iff_exists_index elems b hnd hlen _).mpr ⟨k, hbk, rfl⟩, ?_⟩
    intro y hyI hky
    rcases (memMask_iff_exists_index elems b hnd hlen y).mp hyI with ⟨j, hbj, hgj⟩
    by_cases hjk : j = k
    · subst hjk; exact hgj.symm
    · exfalso
      have hj_chk := List.all_eq_true.mp hall_j j (mem_finRange j)
      have hcond : (boolGet b j.val && decide (j ≠ k)) = true := by simp [hbj, hjk]
      rw [if_pos hcond, adjLookup_buildAdjMatrix] at hj_chk
      rw [← hgj] at hky
      have hleb : leBool (listGet elems k) (listGet elems j) = true := (hle _ _).mpr hky
      rw [hleb] at hj_chk
      cases hj_chk
  · rintro ⟨hk_mem, hmax⟩
    have hbk : boolGet b k.val = true := by
      rcases (memMask_iff_exists_index elems b hnd hlen _).mp hk_mem with ⟨i, hbi, hgi⟩
      have hik := nodup_listGet_inj hnd hgi
      subst hik
      exact hbi
    refine ⟨hbk, List.all_eq_true.mpr fun j _ => ?_⟩
    split
    · next hcond =>
      rcases Bool.and_eq_true_iff.mp hcond with ⟨hbj, hjk_dec⟩
      have hjk : j ≠ k := of_decide_eq_true hjk_dec
      rw [adjLookup_buildAdjMatrix]
      cases hleb : leBool (listGet elems k) (listGet elems j) with
      | false => rfl
      | true =>
        exfalso
        have hj_mem : memMask elems b (listGet elems j) = true :=
          (memMask_iff_exists_index elems b hnd hlen _).mpr ⟨j, hbj, rfl⟩
        have heq := hmax (listGet elems j) hj_mem ((hle _ _).mp hleb)
        exact hjk (nodup_listGet_inj hnd heq)
    · rfl

theorem checkLayerEntryAdj_sound {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} (hnd : ListNodup elems) (hall : ∀ x : P, x ∈ elems)
    {leBool : P → P → Bool} (hle : ∀ x y : P, leBool x y = true ↔ x ≼ y)
    {prevLayer : List (List Bool × Nat)}
    (hprev : ∀ e ∈ prevLayer, ValidDPEntry elems e)
    {entry : List Bool × Nat}
    (hchk : checkLayerEntryAdj elems.length (buildAdjMatrix elems leBool) (buildLookupTrie prevLayer) entry = true) :
    ValidDPEntry elems entry := by
  rcases entry with ⟨b, val⟩
  unfold checkLayerEntryAdj at hchk
  rcases Bool.and_eq_true_iff.mp hchk with ⟨h123, hsum_opt⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hlow_b⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hlen_b, hany_b⟩
  have hlen : b.length = elems.length := beq_iff_eq.mp hlen_b
  have hlow : IsLowerSet P (fun x => memMask elems b x = true) :=
    checkLowerSetAdj_sound hnd hall hle hlen hlow_b
  refine ⟨hlen, hlow, ?_⟩
  dsimp only
  let maxIdxs := maximalIndicesAdj elems.length (buildAdjMatrix elems leBool) b
  have hnd_max : ListNodup maxIdxs := nodup_filter _ (nodup_finRange elems.length)
  cases hsum_eq : sumChildLookups (buildLookupTrie prevLayer) b maxIdxs with
  | none => rw [hsum_eq] at hsum_opt; cases hsum_opt
  | some s =>
    rw [hsum_eq] at hsum_opt
    have hsval : s = val := beq_iff_eq.mp hsum_opt
    subst hsval
    rcases sumChildLookups_children hprev hnd_max hsum_eq with ⟨cs, hcs_valid, hcs_sum⟩
    let liftFor (k : Fin elems.length) :
        List { L : List P // IsLinearExtOf P (fun x => memMask elems b x = true) L } :=
      if hk : k ∈ maxIdxs then
        let childCard : HasCardinality
            { L : List P // IsLinearExtOf P (fun x => memMask elems (clearAt b k.val) x = true) L }
            (cs k) := (hcs_valid k hk).2.2
        let childList : List { L : List P // IsLinearExtOf P (fun x => memMask elems (clearAt b k.val) x = true) L } :=
          choose childCard
        have hk_max : isMaximalIndexAdj elems.length (buildAdjMatrix elems leBool) b k = true :=
          pred_of_filter hk
        have hk_pair := (isMaximalIndexAdj_iff hnd hle hlen k).mp hk_max
        childList.map fun (initSub : { L : List P // IsLinearExtOf P (fun x => memMask elems (clearAt b k.val) x = true) L }) =>
          have hinit_prop : IsLinearExtOf P (fun x => memMask elems b x = true ∧ x ≠ listGet elems k) initSub.val := by
            rcases initSub.property with ⟨h1, h2, h3⟩
            refine ⟨h1, fun x => ?_, h3⟩
            exact (h2 x).trans (memMask_clearAt hnd hlen k x)
          ⟨initSub.val ++ [listGet elems k],
           isLinearExtOf_append_maximal (I := fun x => memMask elems b x = true)
             hk_pair.1 hk_pair.2 initSub.val hinit_prop⟩
      else []
    let allExts := listFlatMap liftFor maxIdxs
    refine ⟨allExts, ?_, ?_, ?_⟩
    · refine nodup_listFlatMap hnd_max ?_ ?_
      · intro k hk
        simp only [liftFor, hk, ↓reduceIte]
        have hspec := choose_spec (hcs_valid k hk).2.2
        refine nodup_map (fun {u₁ u₂} heq => ?_) hspec.1
        have hval := congrArg Subtype.val heq
        exact Subtype.ext (append_singleton_inj hval).1
      · intro k₁ hk₁ k₂ hk₂ hkne y hy z hz heq
        simp only [liftFor, hk₁, hk₂, ↓reduceIte] at hy hz
        rcases List.mem_map.mp hy with ⟨u₁, _, rfl⟩
        rcases List.mem_map.mp hz with ⟨u₂, _, rfl⟩
        have hval := congrArg Subtype.val heq
        have hzeq := (append_singleton_inj hval).2
        exact hkne (nodup_listGet_inj hnd hzeq)
    · rintro ⟨L, hL⟩
      have hL_ne : L ≠ [] := by
        intro hemp
        subst hemp
        rcases any_true_exists_index hany_b with ⟨k, hk, hbk⟩
        have hk_el : k < elems.length := hlen ▸ hk
        have hmem_k : memMask elems b (listGet elems ⟨k, hk_el⟩) = true :=
          (memMask_iff_exists_index elems b hnd hlen _).mpr ⟨⟨k, hk_el⟩, hbk, rfl⟩
        exact nomatch (hL.2.1 _).mpr hmem_k
      rcases list_split_last L hL_ne with ⟨init, z, rfl⟩
      rcases isLinearExtOf_split_last hL with ⟨hzI, hzmax, hinit⟩
      rcases (memMask_iff_exists_index elems b hnd hlen z).mp hzI with ⟨k, _, hgk⟩
      subst hgk
      have hk_max_bool : isMaximalIndexAdj elems.length (buildAdjMatrix elems leBool) b k = true :=
        (isMaximalIndexAdj_iff hnd hle hlen k).mpr ⟨hzI, hzmax⟩
      have hk_in : k ∈ maxIdxs := List.mem_filter.mpr ⟨mem_finRange k, hk_max_bool⟩
      refine mem_listFlatMap.mpr ⟨k, hk_in, ?_⟩
      simp only [liftFor, hk_in, ↓reduceIte]
      have hspec := choose_spec (hcs_valid k hk_in).2.2
      have hinit_clear : IsLinearExtOf P (fun x => memMask elems (clearAt b k.val) x = true) init := by
        rcases hinit with ⟨h1, h2, h3⟩
        refine ⟨h1, fun x => ?_, h3⟩
        exact (h2 x).trans (memMask_clearAt hnd hlen k x).symm
      let initSub : { l : List P // IsLinearExtOf P (fun x => memMask elems (clearAt b k.val) x = true) l } :=
        ⟨init, hinit_clear⟩
      refine List.mem_map.mpr ⟨initSub, hspec.2.1 initSub, ?_⟩
      exact Subtype.ext rfl
    · rw [length_listFlatMap]
      have hmap_len : maxIdxs.map (fun k => (liftFor k).length) = maxIdxs.map cs := by
        have hrec : ∀ (ms : List (Fin elems.length)), (∀ k ∈ ms, k ∈ maxIdxs) →
            ms.map (fun k => (liftFor k).length) = ms.map cs := by
          intro ms hsub
          induction ms with
          | nil => rfl
          | cons k ks ih =>
            have hk : k ∈ maxIdxs := hsub k (List.Mem.head ks)
            have hspec := choose_spec (hcs_valid k hk).2.2
            have hlk : (liftFor k).length = cs k := by
              dsimp only [liftFor]
              rw [dif_pos hk, List.length_map]
              exact hspec.2.2
            simp only [List.map, hlk]
            exact congrArg (cs k :: ·) (ih (fun j hj => hsub j (List.mem_cons_of_mem k hj)))
        exact hrec maxIdxs (fun k hk => hk)
      rw [hmap_len, hcs_sum]

theorem checkAllLayersAdj_sound {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} (hnd : ListNodup elems) (hall : ∀ x : P, x ∈ elems)
    {leBool : P → P → Bool} (hle : ∀ x y : P, leBool x y = true ↔ x ≼ y) :
    ∀ (prev : List (List Bool × Nat)) (layers : List (List (List Bool × Nat))),
      (∀ e ∈ prev, ValidDPEntry elems e) →
      checkAllLayersAdj elems.length (buildAdjMatrix elems leBool) prev layers = true →
      ∀ e ∈ (prev :: layers).getLast (by simp), ValidDPEntry elems e
  | prev, [], hprev, _ => hprev
  | prev, nxt :: rest, hprev, hchk => by
    simp only [checkAllLayersAdj, Bool.and_eq_true_iff] at hchk
    have hnxt : ∀ e ∈ nxt, ValidDPEntry elems e := fun e he =>
      checkLayerEntryAdj_sound hnd hall hle hprev (List.all_eq_true.mp hchk.1 e he)
    exact checkAllLayersAdj_sound hnd hall hle nxt rest hnxt hchk.2

/-- Master soundness theorem for `verifyPosetLinExtCount`: a single `Bool` kernel check
certifies the exact number of linear extensions of any finite poset `P`. -/
theorem verifyPosetLinExtCount_sound {P : Type u} [Poset P] [DecidableEq P]
    {elems : List P} (hnd : ListNodup elems) (hall : ∀ x : P, x ∈ elems)
    {leBool : P → P → Bool} (hle : ∀ x y : P, leBool x y = true ↔ x ≼ y)
    {expected : Nat}
    (hok : verifyPosetLinExtCount elems leBool expected = true) :
    HasLinearExtensionCount P expected := by
  unfold verifyPosetLinExtCount at hok
  rcases Bool.and_eq_true_iff.mp hok with ⟨hlayers, hfinal_b⟩
  have hfinal := beq_iff_eq.mp hfinal_b
  have h0 : ∀ e ∈ [(List.replicate elems.length false, 1)], ValidDPEntry elems e := by
    intro e he
    cases he with
    | head => exact validDPEntry_empty elems
    | tail _ hm => cases hm
  have hlast := checkAllLayersAdj_sound hnd hall hle _ _ h0 hlayers _
    (lookupTrie_buildLookupTrie_mem hfinal)
  rcases hlast.2.2 with ⟨subList, hnd_sub, hall_sub, hlen_sub⟩
  dsimp only at subList hnd_sub hall_sub hlen_sub
  have hfull_iff : ∀ L : List P,
      IsLinearExtOf P (fun x => memMask elems (List.replicate elems.length true) x = true) L ↔
      IsLinearExtension P L := by
    intro L
    have htrue : (fun x => memMask elems (List.replicate elems.length true) x = true) = (fun _ => True) := by
      funext x
      simp [memMask_replicate_true (hall x)]
    rw [htrue, isLinearExtOf_univ_iff]
  let mapFn : { l : List P // IsLinearExtOf P (fun x => memMask elems (List.replicate elems.length true) x = true) l } →
      { l : List P // IsLinearExtension P l } :=
    fun u => ⟨u.val, (hfull_iff u.val).mp u.property⟩
  let mapped := subList.map mapFn
  refine ⟨mapped, ?_, ?_, ?_⟩
  · exact nodup_map (f := mapFn)
      (fun {u₁ u₂} h => Subtype.ext (by simpa [mapFn] using congrArg Subtype.val h)) hnd_sub
  · rintro ⟨L, hL⟩
    let u : { l : List P // IsLinearExtOf P (fun x => memMask elems (List.replicate elems.length true) x = true) l } :=
      ⟨L, (hfull_iff L).mpr hL⟩
    exact List.mem_map.mpr ⟨u, hall_sub u, rfl⟩
  · simp [mapped, hlen_sub]

end LayerDPSoundness

/-! ## 5. Set Partitions, Noncrossing Partitions, and Refinement Lattices -/

def isStrictInc {n : Nat} : List (Fin n) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.val < b.val) && isStrictInc (b :: rest)

theorem isStrictInc_map_succ {n : Nat} :
    ∀ (l : List (Fin n)), isStrictInc l = true → isStrictInc (l.map Fin.succ) = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [List.map, isStrictInc] at h ⊢
    rcases Bool.and_eq_true_iff.mp h with ⟨hab, hrest⟩
    have hab' : a.val < b.val := of_decide_eq_true hab
    exact Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true (Nat.succ_lt_succ hab'), isStrictInc_map_succ (b :: rest) hrest⟩

theorem isStrictInc_finRange : ∀ (n : Nat), isStrictInc (finRange n) = true
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by
    have ih := isStrictInc_map_succ (finRange (m + 1)) (isStrictInc_finRange (m + 1))
    simp only [finRange, List.map] at ih ⊢
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (Nat.zero_lt_succ 0), ih⟩

theorem lt_of_mem_tail_strictInc {n : Nat} :
    ∀ {a : Fin n} {xs : List (Fin n)}, isStrictInc (a :: xs) = true →
      ∀ z ∈ xs, a.val < z.val
  | _, [], _, _, hz => nomatch hz
  | _, b :: rest, h, z, hz => by
    simp only [isStrictInc] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hab, hrest⟩
    have hab' := of_decide_eq_true hab
    cases hz with
    | head => exact hab'
    | tail _ hm =>
      have hbz := lt_of_mem_tail_strictInc hrest z hm
      omega

theorem isStrictInc_filter {n : Nat} (p : Fin n → Bool) :
    ∀ {l : List (Fin n)}, isStrictInc l = true → isStrictInc (l.filter p) = true
  | [], _ => rfl
  | [_], _ => by simp only [List.filter]; split <;> rfl
  | a :: b :: rest, h => by
    have htail : isStrictInc (b :: rest) = true := (Bool.and_eq_true_iff.mp h).2
    have ihtail := isStrictInc_filter p htail
    cases hpa : p a with
    | false =>
      have hstep : List.filter p (a :: b :: rest) = List.filter p (b :: rest) := by
        simp [List.filter, hpa]
      rw [hstep]
      exact ihtail
    | true =>
      have hstep : List.filter p (a :: b :: rest) = a :: List.filter p (b :: rest) := by
        simp [List.filter, hpa]
      rw [hstep]
      cases hfl : List.filter p (b :: rest) with
      | nil => rfl
      | cons c cs =>
        rw [hfl] at ihtail
        simp only [isStrictInc]
        have hc_mem : c ∈ List.filter p (b :: rest) := by rw [hfl]; exact List.Mem.head cs
        have hac : a.val < c.val := lt_of_mem_tail_strictInc h c (mem_of_filter hc_mem)
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hac, ihtail⟩

theorem strictInc_eq_of_mem_iff {n : Nat} :
    ∀ {l₁ l₂ : List (Fin n)}, isStrictInc l₁ = true → isStrictInc l₂ = true →
      (∀ x : Fin n, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hmem =>
    False.elim (nomatch (hmem y).mpr (List.Mem.head ys))
  | x :: xs, [], _, _, hmem =>
    False.elim (nomatch (hmem x).mp (List.Mem.head xs))
  | x :: xs, y :: ys, h₁, h₂, hmem => by
    have hx_in_2 : x ∈ y :: ys := (hmem x).mp (List.Mem.head xs)
    have hy_in_1 : y ∈ x :: xs := (hmem y).mpr (List.Mem.head ys)
    have hxy : x = y := by
      cases hx_in_2 with
      | head => rfl
      | tail _ hxs =>
        cases hy_in_1 with
        | head => rfl
        | tail _ hys =>
          have hlt1 := lt_of_mem_tail_strictInc h₂ x hxs
          have hlt2 := lt_of_mem_tail_strictInc h₁ y hys
          omega
    subst hxy
    have htail1 : isStrictInc xs = true := by
      cases xs with
      | nil => rfl
      | cons _ _ => exact (Bool.and_eq_true_iff.mp h₁).2
    have htail2 : isStrictInc ys = true := by
      cases ys with
      | nil => rfl
      | cons _ _ => exact (Bool.and_eq_true_iff.mp h₂).2
    refine congrArg (x :: ·) (strictInc_eq_of_mem_iff htail1 htail2 ?_)
    intro z
    constructor
    · intro hz
      have hz2 : z ∈ x :: ys := (hmem z).mp (List.mem_cons_of_mem x hz)
      cases hz2 with
      | head => exact False.elim (Nat.lt_irrefl x.val (lt_of_mem_tail_strictInc h₁ x hz))
      | tail _ hm => exact hm
    · intro hz
      have hz1 : z ∈ x :: xs := (hmem z).mpr (List.mem_cons_of_mem x hz)
      cases hz1 with
      | head => exact False.elim (Nat.lt_irrefl x.val (lt_of_mem_tail_strictInc h₂ x hz))
      | tail _ hm => exact hm

def allBlocksNonemptyStrictInc {n : Nat} : List (List (Fin n)) → Bool
  | [] => true
  | B :: bs => (!B.isEmpty) && isStrictInc B && allBlocksNonemptyStrictInc bs

def headsStrictInc {n : Nat} : List (List (Fin n)) → Bool
  | [] => true
  | [_] => true
  | (a :: _) :: (b :: bs_b) :: rest =>
    decide (a.val < b.val) && headsStrictInc ((b :: bs_b) :: rest)
  | _ => false

def countBlocksContaining {n : Nat} (x : Fin n) : List (List (Fin n)) → Nat
  | [] => 0
  | B :: bs => (if decide (x ∈ B) then 1 else 0) + countBlocksContaining x bs

def coversAllOnce (n : Nat) (blocks : List (List (Fin n))) : Bool :=
  (finRange n).all (fun x => countBlocksContaining x blocks == 1)

def isValidPartition (n : Nat) (blocks : List (List (Fin n))) : Bool :=
  allBlocksNonemptyStrictInc blocks && headsStrictInc blocks && coversAllOnce n blocks

/-- Canonical set partition of `Fin n`: nonempty pairwise-disjoint sorted blocks covering `Fin n`. -/
structure SetPartition (n : Nat) where
  blocks : List (List (Fin n))
  valid : isValidPartition n blocks = true
  deriving DecidableEq

def sameBlockBool {n : Nat} (blocks : List (List (Fin n))) (x y : Fin n) : Bool :=
  blocks.any (fun B => decide (x ∈ B) && decide (y ∈ B))

def SameBlock {n : Nat} (π : SetPartition n) (x y : Fin n) : Prop :=
  sameBlockBool π.blocks x y = true

/-- Exact noncrossing condition (Kreweras 1972): no `a < b < c < d` in `Fin n`
have `a, c` in one block and `b, d` in a distinct block. -/
def IsNoncrossing {n : Nat} (π : SetPartition n) : Prop :=
  ∀ a b c d : Fin n,
    a.val < b.val → b.val < c.val → c.val < d.val →
    SameBlock π a c → SameBlock π b d → SameBlock π a b

def isNoncrossingBool {n : Nat} (π : SetPartition n) : Bool :=
  (finRange n).all fun a =>
    (finRange n).all fun b =>
      (finRange n).all fun c =>
        (finRange n).all fun d =>
          if decide (a.val < b.val ∧ b.val < c.val ∧ c.val < d.val) &&
             sameBlockBool π.blocks a c && sameBlockBool π.blocks b d then
            sameBlockBool π.blocks a b
          else true

theorem isNoncrossingBool_iff {n : Nat} (π : SetPartition n) :
    isNoncrossingBool π = true ↔ IsNoncrossing π := by
  unfold isNoncrossingBool IsNoncrossing SameBlock
  constructor
  · intro h a b c d hab hbc hcd hac hbd
    have ha := List.all_eq_true.mp h a (mem_finRange a)
    have hb := List.all_eq_true.mp ha b (mem_finRange b)
    have hc := List.all_eq_true.mp hb c (mem_finRange c)
    have hd := List.all_eq_true.mp hc d (mem_finRange d)
    have hcond : (decide (a.val < b.val ∧ b.val < c.val ∧ c.val < d.val) &&
        sameBlockBool π.blocks a c && sameBlockBool π.blocks b d) = true := by
      simp [hab, hbc, hcd, hac, hbd]
    rw [if_pos hcond] at hd
    exact hd
  · intro h
    refine List.all_eq_true.mpr fun a _ => List.all_eq_true.mpr fun b _ =>
      List.all_eq_true.mpr fun c _ => List.all_eq_true.mpr fun d _ => ?_
    split
    · next hcond =>
      rcases Bool.and_eq_true_iff.mp hcond with ⟨h12, hbd⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨hlt, hac⟩
      rcases of_decide_eq_true hlt with ⟨hab, hbc, hcd⟩
      exact h a b c d hab hbc hcd hac hbd
    · rfl

/-- The type of noncrossing partitions of `Fin n`. -/
def NCPartition (n : Nat) : Type :=
  { π : SetPartition n // IsNoncrossing π }

instance instDecidableEqNCPartition (n : Nat) : DecidableEq (NCPartition n) :=
  fun a b =>
    if h : a.val = b.val then isTrue (Subtype.ext h)
    else isFalse (fun heq => h (congrArg Subtype.val heq))

/-! ### Equivalence Relations and Canonical Uniqueness of `SetPartition n` -/

structure IsBoolEquivRel {n : Nat} (R : Fin n → Fin n → Bool) : Prop where
  refl : ∀ x : Fin n, R x x = true
  symm : ∀ {x y : Fin n}, R x y = true → R y x = true
  trans : ∀ {x y z : Fin n}, R x y = true → R y z = true → R x z = true

def equivClass {n : Nat} (R : Fin n → Fin n → Bool) (x : Fin n) : List (Fin n) :=
  (finRange n).filter (fun y => R x y)

def isClassMin {n : Nat} (R : Fin n → Fin n → Bool) (x : Fin n) : Bool :=
  match equivClass R x with
  | y :: _ => decide (x = y)
  | [] => false

def classReps {n : Nat} (R : Fin n → Fin n → Bool) : List (Fin n) :=
  (finRange n).filter (isClassMin R)

def blocksOfRel {n : Nat} (R : Fin n → Fin n → Bool) : List (List (Fin n)) :=
  (classReps R).map (equivClass R)

theorem equivClass_eq_of_rel {n : Nat} {R : Fin n → Fin n → Bool}
    (hR : IsBoolEquivRel R) {x y : Fin n} (hxy : R x y = true) :
    equivClass R x = equivClass R y := by
  unfold equivClass
  have hfun : (fun z => R x z) = (fun z => R y z) := by
    funext z
    cases h1 : R x z <;> cases h2 : R y z
    · rfl
    · exfalso; have hxz := hR.trans hxy h2; rw [h1] at hxz; cases hxz
    · exfalso; have hyz := hR.trans (hR.symm hxy) h1; rw [h2] at hyz; cases hyz
    · rfl
  rw [hfun]

theorem mem_equivClass_iff {n : Nat} (R : Fin n → Fin n → Bool) (x y : Fin n) :
    y ∈ equivClass R x ↔ R x y = true := by
  unfold equivClass
  exact ⟨pred_of_filter, fun h => List.mem_filter.mpr ⟨mem_finRange y, h⟩⟩

theorem equivClass_nonempty {n : Nat} {R : Fin n → Fin n → Bool}
    (hR : IsBoolEquivRel R) (x : Fin n) : equivClass R x ≠ [] := by
  intro hemp
  have hx : x ∈ equivClass R x := (mem_equivClass_iff R x x).mpr (hR.refl x)
  rw [hemp] at hx
  cases hx

theorem equivClass_head_of_isClassMin {n : Nat} {R : Fin n → Fin n → Bool}
    {r : Fin n} (hr : isClassMin R r = true) :
    ∃ tail : List (Fin n), equivClass R r = r :: tail := by
  unfold isClassMin at hr
  cases hcls : equivClass R r with
  | nil => rw [hcls] at hr; cases hr
  | cons y ys =>
    rw [hcls] at hr
    have hry : r = y := of_decide_eq_true hr
    subst hry
    exact ⟨ys, rfl⟩

theorem allBlocksNonemptyStrictInc_blocksOfRel {n : Nat} {R : Fin n → Fin n → Bool}
    (hR : IsBoolEquivRel R) :
    allBlocksNonemptyStrictInc (blocksOfRel R) = true := by
  unfold blocksOfRel
  have hrec : ∀ (rs : List (Fin n)), allBlocksNonemptyStrictInc (rs.map (equivClass R)) = true := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.map, allBlocksNonemptyStrictInc]
      have hne : (!List.isEmpty (equivClass R r)) = true := by
        cases hcls : equivClass R r with
        | nil => exact False.elim (equivClass_nonempty hR r hcls)
        | cons _ _ => rfl
      have hsi : isStrictInc (equivClass R r) = true :=
        isStrictInc_filter _ (isStrictInc_finRange n)
      simp [hne, hsi, ih]
  exact hrec (classReps R)

theorem headsStrictInc_map_reps {n : Nat} {R : Fin n → Fin n → Bool} :
    ∀ {rs : List (Fin n)}, isStrictInc rs = true →
      (∀ r ∈ rs, isClassMin R r = true) →
      headsStrictInc (rs.map (equivClass R)) = true
  | [], _, _ => rfl
  | [r], _, hall => by
    rcases equivClass_head_of_isClassMin (hall r (List.Mem.head [])) with ⟨_, hcls⟩
    simp [List.map, hcls, headsStrictInc]
  | a :: b :: rest, hsi, hall => by
    simp only [isStrictInc] at hsi
    rcases Bool.and_eq_true_iff.mp hsi with ⟨hab, hrest⟩
    rcases equivClass_head_of_isClassMin (hall a (List.Mem.head _)) with ⟨_, ha⟩
    rcases equivClass_head_of_isClassMin (hall b (List.mem_cons_of_mem a (List.Mem.head _))) with ⟨_, hb⟩
    have ih := headsStrictInc_map_reps hrest (fun r hr => hall r (List.mem_cons_of_mem a hr))
    simp only [List.map, ha, hb, headsStrictInc] at ih ⊢
    exact Bool.and_eq_true_iff.mpr ⟨hab, ih⟩

theorem countBlocksContaining_eq_one_of_unique {n : Nat} {x : Fin n} :
    ∀ {bs : List (List (Fin n))}, ListNodup bs →
      (∃ B₀ ∈ bs, x ∈ B₀ ∧ ∀ B ∈ bs, x ∈ B → B = B₀) →
      countBlocksContaining x bs = 1
  | [], _, ⟨_, hmem, _⟩ => nomatch hmem
  | B :: rest, ListNodup.cons hnotmem hnd, ⟨B₀, hB₀, hxB₀, huniq⟩ => by
    have hzero : ∀ {cs : List (List (Fin n))}, (∀ C ∈ cs, x ∉ C) → countBlocksContaining x cs = 0 := by
      intro cs hno
      induction cs with
      | nil => rfl
      | cons C cs' ih =>
        have hxC : x ∉ C := hno C (List.Mem.head cs')
        simp [countBlocksContaining, hxC, ih (fun D hD => hno D (List.mem_cons_of_mem C hD))]
    cases hB₀ with
    | head =>
      have hno : ∀ C ∈ rest, x ∉ C := fun C hC hxC =>
        hnotmem C hC (huniq C (List.mem_cons_of_mem B hC) hxC).symm
      simp [countBlocksContaining, hxB₀, hzero hno]
    | tail _ hm =>
      have hxB : x ∉ B := by
        intro hxB
        have heq := huniq B (List.Mem.head rest) hxB
        subst heq
        exact hnotmem B hm rfl
      have ih := countBlocksContaining_eq_one_of_unique hnd
        ⟨B₀, hm, hxB₀, fun C hC hxC => huniq C (List.mem_cons_of_mem B hC) hxC⟩
      simp [countBlocksContaining, hxB, ih]

theorem isValidPartition_blocksOfRel {n : Nat} {R : Fin n → Fin n → Bool}
    (hR : IsBoolEquivRel R) :
    isValidPartition n (blocksOfRel R) = true := by
  unfold isValidPartition
  have h1 := allBlocksNonemptyStrictInc_blocksOfRel hR
  have h2 : headsStrictInc (blocksOfRel R) = true :=
    headsStrictInc_map_reps (isStrictInc_filter _ (isStrictInc_finRange n))
      (fun _ hr => pred_of_filter hr)
  have hnd_blocks : ListNodup (blocksOfRel R) := by
    refine nodup_map_on (nodup_filter _ (nodup_finRange n)) ?_
    intro a ha b hb hab
    rcases equivClass_head_of_isClassMin (pred_of_filter ha) with ⟨_, hca⟩
    rcases equivClass_head_of_isClassMin (pred_of_filter hb) with ⟨_, hcb⟩
    rw [hca, hcb] at hab
    exact List.cons.inj hab |>.1
  have h3 : coversAllOnce n (blocksOfRel R) = true := by
    unfold coversAllOnce
    refine List.all_eq_true.mpr fun x _ => ?_
    cases hcls : equivClass R x with
    | nil => exact False.elim (equivClass_nonempty hR x hcls)
    | cons r tail =>
      have hxr : R x r = true := (mem_equivClass_iff R x r).mp (by rw [hcls]; exact List.Mem.head tail)
      have heq_cls : equivClass R r = equivClass R x := equivClass_eq_of_rel hR (hR.symm hxr)
      have hr_min : isClassMin R r = true := by unfold isClassMin; rw [heq_cls, hcls]; simp
      have hr_rep : r ∈ classReps R := List.mem_filter.mpr ⟨mem_finRange r, hr_min⟩
      have hB₀_mem : equivClass R r ∈ blocksOfRel R := List.mem_map.mpr ⟨r, hr_rep, rfl⟩
      have hx_in : x ∈ equivClass R r := (mem_equivClass_iff R r x).mpr (hR.symm hxr)
      have hcnt := countBlocksContaining_eq_one_of_unique hnd_blocks ⟨equivClass R r, hB₀_mem, hx_in, ?_⟩
      · exact beq_iff_eq.mpr hcnt
      · intro B hB hxB
        rcases List.mem_map.mp hB with ⟨r', _, rfl⟩
        have hr'x : R r' x = true := (mem_equivClass_iff R r' x).mp hxB
        exact equivClass_eq_of_rel hR (hR.trans hr'x hxr)
  simp [h1, h2, h3]

def ofEquivRel {n : Nat} (R : Fin n → Fin n → Bool) (hR : IsBoolEquivRel R) : SetPartition n :=
  ⟨blocksOfRel R, isValidPartition_blocksOfRel hR⟩

theorem sameBlockBool_blocksOfRel {n : Nat} {R : Fin n → Fin n → Bool}
    (hR : IsBoolEquivRel R) (x y : Fin n) :
    sameBlockBool (blocksOfRel R) x y = R x y := by
  cases hxy : R x y with
  | false =>
    cases hsb : sameBlockBool (blocksOfRel R) x y with
    | false => rfl
    | true =>
      exfalso
      rcases List.any_eq_true.mp hsb with ⟨B, hB, hxyB⟩
      rcases List.mem_map.mp hB with ⟨r, _, rfl⟩
      rcases Bool.and_eq_true_iff.mp hxyB with ⟨hxB, hyB⟩
      have hrx := (mem_equivClass_iff R r x).mp (of_decide_eq_true hxB)
      have hry := (mem_equivClass_iff R r y).mp (of_decide_eq_true hyB)
      have hxy' := hR.trans (hR.symm hrx) hry
      rw [hxy] at hxy'; cases hxy'
  | true =>
    refine List.any_eq_true.mpr ?_
    cases hcls : equivClass R x with
    | nil => exact False.elim (equivClass_nonempty hR x hcls)
    | cons r tail =>
      have hxr : R x r = true := (mem_equivClass_iff R x r).mp (by rw [hcls]; exact List.Mem.head tail)
      have heq_cls : equivClass R r = equivClass R x := equivClass_eq_of_rel hR (hR.symm hxr)
      have hr_min : isClassMin R r = true := by unfold isClassMin; rw [heq_cls, hcls]; simp
      have hr_rep : r ∈ classReps R := List.mem_filter.mpr ⟨mem_finRange r, hr_min⟩
      refine ⟨equivClass R r, List.mem_map.mpr ⟨r, hr_rep, rfl⟩, ?_⟩
      have hx_in : x ∈ equivClass R r := (mem_equivClass_iff R r x).mpr (hR.symm hxr)
      have hy_in : y ∈ equivClass R r := (mem_equivClass_iff R r y).mpr (hR.trans (hR.symm hxr) hxy)
      simp [hx_in, hy_in]

theorem unique_block_of_count_eq_one {n : Nat} {x : Fin n} :
    ∀ {bs : List (List (Fin n))}, countBlocksContaining x bs = 1 →
      ∃ B₀ ∈ bs, x ∈ B₀ ∧ ∀ B ∈ bs, x ∈ B → B = B₀
  | [], h => nomatch h
  | B :: rest, h => by
    have hzero_none : ∀ {cs : List (List (Fin n))}, countBlocksContaining x cs = 0 →
        ∀ C ∈ cs, x ∉ C := by
      intro cs hc C hC hxC
      induction cs with
      | nil => cases hC
      | cons D ds ih =>
        simp only [countBlocksContaining] at hc
        cases hC with
        | head => simp [hxC] at hc
        | tail _ hm =>
          split at hc
          · omega
          · exact ih (by omega) hm
    simp only [countBlocksContaining] at h
    by_cases hxB : x ∈ B
    · simp [hxB] at h
      refine ⟨B, List.Mem.head rest, hxB, ?_⟩
      intro C hC hxC
      cases hC with
      | head => rfl
      | tail _ hm => exact False.elim (hzero_none h C hm hxC)
    · simp [hxB] at h
      rcases unique_block_of_count_eq_one h with ⟨B₀, hm₀, hxB₀, huniq⟩
      refine ⟨B₀, List.mem_cons_of_mem B hm₀, hxB₀, ?_⟩
      intro C hC hxC
      cases hC with
      | head => exact False.elim (hxB hxC)
      | tail _ hm => exact huniq C hm hxC

theorem SetPartition.unique_block {n : Nat} (π : SetPartition n) (x : Fin n) :
    ∃ B₀ ∈ π.blocks, x ∈ B₀ ∧ ∀ B ∈ π.blocks, x ∈ B → B = B₀ := by
  have hv := π.valid
  unfold isValidPartition at hv
  rcases Bool.and_eq_true_iff.mp hv with ⟨_, hcov⟩
  have hx := List.all_eq_true.mp hcov x (mem_finRange x)
  exact unique_block_of_count_eq_one (beq_iff_eq.mp hx)

theorem SetPartition.block_nonempty_strictInc {n : Nat} (π : SetPartition n)
    {B : List (Fin n)} (hB : B ∈ π.blocks) :
    B ≠ [] ∧ isStrictInc B = true := by
  have hv := π.valid
  unfold isValidPartition at hv
  rcases Bool.and_eq_true_iff.mp hv with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hall, _⟩
  have hrec : ∀ {bs : List (List (Fin n))}, allBlocksNonemptyStrictInc bs = true →
      ∀ C ∈ bs, C ≠ [] ∧ isStrictInc C = true := by
    intro bs hbs C hC
    induction bs with
    | nil => cases hC
    | cons D ds ih =>
      unfold allBlocksNonemptyStrictInc at hbs
      rcases Bool.and_eq_true_iff.mp hbs with ⟨hD12, hds⟩
      rcases Bool.and_eq_true_iff.mp hD12 with ⟨hDne, hDsi⟩
      cases hC with
      | head =>
        refine ⟨?_, hDsi⟩
        intro hemp
        rw [hemp] at hDne
        cases hDne
      | tail _ hm => exact ih hds hm
  exact hrec hall B hB

theorem SetPartition.sameBlock_isEquivRel {n : Nat} (π : SetPartition n) :
    IsBoolEquivRel (sameBlockBool π.blocks) where
  refl x := by
    rcases π.unique_block x with ⟨B₀, hB₀, hx, _⟩
    exact List.any_eq_true.mpr ⟨B₀, hB₀, by simp [hx]⟩
  symm hxy := by
    rcases List.any_eq_true.mp hxy with ⟨B, hB, hboth⟩
    rcases Bool.and_eq_true_iff.mp hboth with ⟨hx, hy⟩
    exact List.any_eq_true.mpr ⟨B, hB, Bool.and_eq_true_iff.mpr ⟨hy, hx⟩⟩
  trans hxy hyz := by
    rcases List.any_eq_true.mp hxy with ⟨B₁, hB₁, hb1⟩
    rcases List.any_eq_true.mp hyz with ⟨B₂, hB₂, hb2⟩
    rcases Bool.and_eq_true_iff.mp hb1 with ⟨hx₁, hy₁⟩
    rcases Bool.and_eq_true_iff.mp hb2 with ⟨hy₂, hz₂⟩
    rcases π.unique_block _ with ⟨B₀, _, _, huniq⟩
    have heq1 := huniq B₁ hB₁ (of_decide_eq_true hy₁)
    have heq2 := huniq B₂ hB₂ (of_decide_eq_true hy₂)
    have h12 : B₁ = B₂ := heq1.trans heq2.symm
    subst h12
    exact List.any_eq_true.mpr ⟨B₁, hB₁, Bool.and_eq_true_iff.mpr ⟨hx₁, hz₂⟩⟩

def blockHeads {n : Nat} : List (List (Fin n)) → List (Fin n)
  | [] => []
  | (r :: _) :: bs => r :: blockHeads bs
  | [] :: bs => blockHeads bs

theorem isStrictInc_blockHeads {n : Nat} :
    ∀ {bs : List (List (Fin n))},
      allBlocksNonemptyStrictInc bs = true → headsStrictInc bs = true →
      isStrictInc (blockHeads bs) = true
  | [], _, _ => rfl
  | [B], hall, _ => by
    cases B with
    | nil => simp [allBlocksNonemptyStrictInc] at hall
    | cons _ _ => rfl
  | B₁ :: B₂ :: rest, hall, hheads => by
    cases B₁ with
    | nil => simp [allBlocksNonemptyStrictInc] at hall
    | cons a ta =>
      cases B₂ with
      | nil =>
        unfold allBlocksNonemptyStrictInc at hall
        rcases Bool.and_eq_true_iff.mp hall with ⟨_, hrest1⟩
        simp [allBlocksNonemptyStrictInc] at hrest1
      | cons b tb =>
        unfold allBlocksNonemptyStrictInc at hall
        rcases Bool.and_eq_true_iff.mp hall with ⟨_, hrest1⟩
        simp only [headsStrictInc, Bool.and_eq_true_iff] at hheads
        have ih := isStrictInc_blockHeads hrest1 hheads.2
        simp only [blockHeads, isStrictInc] at ih ⊢
        exact Bool.and_eq_true_iff.mpr ⟨hheads.1, ih⟩

theorem SetPartition.blocks_eq_blocksOfRel {n : Nat} (π : SetPartition n) :
    π.blocks = blocksOfRel (sameBlockBool π.blocks) := by
  let R := sameBlockBool π.blocks
  have hR := π.sameBlock_isEquivRel
  have hcls_of_block : ∀ B ∈ π.blocks, ∀ r : Fin n, ∀ tail : List (Fin n),
      B = r :: tail → equivClass R r = B := by
    intro B hB r tail hB_eq
    have hsiB := (π.block_nonempty_strictInc hB).2
    refine strictInc_eq_of_mem_iff (isStrictInc_filter _ (isStrictInc_finRange n)) hsiB ?_
    intro y
    rw [mem_equivClass_iff]
    constructor
    · intro hry
      rcases List.any_eq_true.mp hry with ⟨B', hB', hboth⟩
      rcases Bool.and_eq_true_iff.mp hboth with ⟨hrB', hyB'⟩
      rcases π.unique_block r with ⟨_, _, _, huniq⟩
      have hrB : r ∈ B := by rw [hB_eq]; exact List.Mem.head tail
      have heq : B' = B := (huniq B' hB' (of_decide_eq_true hrB')).trans (huniq B hB hrB).symm
      subst heq
      exact of_decide_eq_true hyB'
    · intro hyB
      have hrB : r ∈ B := by rw [hB_eq]; exact List.Mem.head tail
      exact List.any_eq_true.mpr ⟨B, hB, by simp [hrB, hyB]⟩
  have hv := π.valid
  unfold isValidPartition at hv
  rcases Bool.and_eq_true_iff.mp hv with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hall_ne, hheads⟩
  have hmap_heads : (blockHeads π.blocks).map (equivClass R) = π.blocks := by
    have hrec : ∀ {bs : List (List (Fin n))},
        (∀ B ∈ bs, B ∈ π.blocks) → allBlocksNonemptyStrictInc bs = true →
        (blockHeads bs).map (equivClass R) = bs := by
      intro bs hsub hne
      induction bs with
      | nil => rfl
      | cons B rest ih =>
        cases hBeq : B with
        | nil => simp [hBeq, allBlocksNonemptyStrictInc] at hne
        | cons r tail =>
          rw [hBeq] at hne
          unfold allBlocksNonemptyStrictInc at hne
          rcases Bool.and_eq_true_iff.mp hne with ⟨_, hne_rest⟩
          have hBmem : r :: tail ∈ π.blocks := hBeq ▸ hsub B (List.Mem.head rest)
          have hcls := hcls_of_block (r :: tail) hBmem r tail rfl
          simp only [blockHeads, List.map, hcls]
          exact congrArg ((r :: tail) :: ·) (ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC)) hne_rest)
    exact hrec (fun _ h => h) hall_ne
  have hreps_eq : classReps R = blockHeads π.blocks := by
    refine strictInc_eq_of_mem_iff
      (isStrictInc_filter _ (isStrictInc_finRange n))
      (isStrictInc_blockHeads hall_ne hheads) ?_
    intro r
    constructor
    · intro hr_rep
      have hr_min : isClassMin R r = true := pred_of_filter hr_rep
      rcases π.unique_block r with ⟨B, hB, hrB, _⟩
      cases hBeq : B with
      | nil => exact False.elim ((π.block_nonempty_strictInc hB).1 hBeq)
      | cons r' tail =>
        have hcls_r' : equivClass R r' = r' :: tail :=
          hcls_of_block (r' :: tail) (hBeq ▸ hB) r' tail rfl
        have hr'B : r' ∈ B := by rw [hBeq]; exact List.Mem.head tail
        have hrr' : R r r' = true :=
          List.any_eq_true.mpr ⟨B, hB, by simp [hrB, hr'B]⟩
        have hcls_r : equivClass R r = r' :: tail :=
          (equivClass_eq_of_rel hR hrr').trans hcls_r'
        unfold isClassMin at hr_min
        rw [hcls_r] at hr_min
        have heq_rr' : r = r' := of_decide_eq_true hr_min
        subst heq_rr'
        have hmem_heads : ∀ {bs : List (List (Fin n))},
            allBlocksNonemptyStrictInc bs = true → (r :: tail) ∈ bs → r ∈ blockHeads bs := by
          intro bs hne hm
          induction bs with
          | nil => cases hm
          | cons C cs ih =>
            cases C with
            | nil => simp [allBlocksNonemptyStrictInc] at hne
            | cons c tc =>
              unfold allBlocksNonemptyStrictInc at hne
              rcases Bool.and_eq_true_iff.mp hne with ⟨_, hne_cs⟩
              cases hm with
              | head => exact List.Mem.head _
              | tail _ htail => exact List.mem_cons_of_mem c (ih hne_cs htail)
        exact hmem_heads hall_ne (hBeq ▸ hB)
    · intro hr_head
      have hex_B : ∃ tail : List (Fin n), (r :: tail) ∈ π.blocks := by
        have hrec : ∀ {bs : List (List (Fin n))},
            (∀ B ∈ bs, B ∈ π.blocks) → allBlocksNonemptyStrictInc bs = true →
            r ∈ blockHeads bs → ∃ tail, (r :: tail) ∈ π.blocks := by
          intro bs hsub hne hm
          induction bs with
          | nil => cases hm
          | cons C cs ih =>
            cases C with
            | nil => simp [allBlocksNonemptyStrictInc] at hne
            | cons c tc =>
              unfold allBlocksNonemptyStrictInc at hne
              rcases Bool.and_eq_true_iff.mp hne with ⟨_, hne_cs⟩
              cases hm with
              | head => exact ⟨tc, hsub (r :: tc) (List.Mem.head cs)⟩
              | tail _ htail => exact ih (fun D hD => hsub D (List.mem_cons_of_mem _ hD)) hne_cs htail
        exact hrec (fun _ h => h) hall_ne hr_head
      rcases hex_B with ⟨tail, hB⟩
      have hcls := hcls_of_block (r :: tail) hB r tail rfl
      refine List.mem_filter.mpr ⟨mem_finRange r, ?_⟩
      unfold isClassMin
      rw [hcls]
      simp
  unfold blocksOfRel
  rw [hreps_eq, hmap_heads]

/-- Canonical extensionality: two set partitions are equal iff they induce the same
equivalence relation on `Fin n`. -/
theorem SetPartition.ext_sameBlock {n : Nat} {π₁ π₂ : SetPartition n}
    (h : ∀ x y : Fin n, sameBlockBool π₁.blocks x y = sameBlockBool π₂.blocks x y) :
    π₁ = π₂ := by
  have hfun : sameBlockBool π₁.blocks = sameBlockBool π₂.blocks := by
    funext x y; exact h x y
  have hb : π₁.blocks = π₂.blocks := by
    rw [π₁.blocks_eq_blocksOfRel, π₂.blocks_eq_blocksOfRel, hfun]
  cases π₁; cases π₂
  simp at hb
  subst hb
  rfl

/-! ### Complete Duplicate-Free Enumeration of `SetPartition n` and `NCPartition n` -/

def relSingleton {n : Nat} (π : SetPartition n) (u v : Fin (n + 1)) : Bool :=
  if hu : u.val < n then
    if hv : v.val < n then
      sameBlockBool π.blocks ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else false
  else decide (u = v)

theorem relSingleton_isEquivRel {n : Nat} (π : SetPartition n) :
    IsBoolEquivRel (relSingleton π) where
  refl u := by
    unfold relSingleton
    split
    · next hu => simp [hu, π.sameBlock_isEquivRel.refl ⟨u.val, hu⟩]
    · simp
  symm {u v} huv := by
    unfold relSingleton at huv ⊢
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [hu, hv, ↓reduceDIte] at huv ⊢
      exact π.sameBlock_isEquivRel.symm huv
    · simp [hu, hv] at huv
    · simp only [hu, ↓reduceDIte, decide_eq_true_eq] at huv
      subst huv; exact False.elim (hu hv)
    · simp only [hu, hv, ↓reduceDIte, decide_eq_true_eq] at huv ⊢
      exact huv.symm
  trans {u v w} huv hvw := by
    unfold relSingleton at huv hvw ⊢
    by_cases hu : u.val < n <;> by_cases hv : v.val < n <;> by_cases hw : w.val < n
    · simp only [hu, hv, hw, ↓reduceDIte] at huv hvw ⊢
      exact π.sameBlock_isEquivRel.trans huv hvw
    · simp [hv, hw] at hvw
    · simp [hu, hv] at huv
    · simp [hu, hv] at huv
    · simp only [hu, ↓reduceDIte, decide_eq_true_eq] at huv
      subst huv; exact False.elim (hu hv)
    · simp only [hu, ↓reduceDIte, decide_eq_true_eq] at huv
      subst huv; exact False.elim (hu hv)
    · simp only [hv, ↓reduceDIte, decide_eq_true_eq] at hvw
      subst hvw; exact False.elim (hv hw)
    · simp only [hu, hv, hw, ↓reduceDIte, decide_eq_true_eq] at huv hvw ⊢
      exact huv.trans hvw

def projToRep {n : Nat} (r : Fin n) (u : Fin (n + 1)) : Fin n :=
  if hu : u.val < n then ⟨u.val, hu⟩ else r

def relJoinRep {n : Nat} (π : SetPartition n) (r : Fin n) (u v : Fin (n + 1)) : Bool :=
  sameBlockBool π.blocks (projToRep r u) (projToRep r v)

theorem relJoinRep_isEquivRel {n : Nat} (π : SetPartition n) (r : Fin n) :
    IsBoolEquivRel (relJoinRep π r) where
  refl u := π.sameBlock_isEquivRel.refl (projToRep r u)
  symm huv := π.sameBlock_isEquivRel.symm huv
  trans huv hvw := π.sameBlock_isEquivRel.trans huv hvw

def extendSingleton {n : Nat} (π : SetPartition n) : SetPartition (n + 1) :=
  ofEquivRel (relSingleton π) (relSingleton_isEquivRel π)

def extendJoinRep {n : Nat} (π : SetPartition n) (r : Fin n) : SetPartition (n + 1) :=
  ofEquivRel (relJoinRep π r) (relJoinRep_isEquivRel π r)

def extendOnePartition {n : Nat} (π : SetPartition n) : List (SetPartition (n + 1)) :=
  extendSingleton π :: (classReps (sameBlockBool π.blocks)).map (extendJoinRep π)

def enumSetPartitions : (n : Nat) → List (SetPartition n)
  | 0 => [⟨[], rfl⟩]
  | n + 1 => listFlatMap extendOnePartition (enumSetPartitions n)

theorem sameBlock_extendSingleton {n : Nat} (π : SetPartition n) (u v : Fin (n + 1)) :
    sameBlockBool (extendSingleton π).blocks u v = relSingleton π u v :=
  sameBlockBool_blocksOfRel (relSingleton_isEquivRel π) u v

theorem sameBlock_extendJoinRep {n : Nat} (π : SetPartition n) (r : Fin n) (u v : Fin (n + 1)) :
    sameBlockBool (extendJoinRep π r).blocks u v = relJoinRep π r u v :=
  sameBlockBool_blocksOfRel (relJoinRep_isEquivRel π r) u v

theorem sameBlock_extendSingleton_castSucc {n : Nat} (π : SetPartition n) (i j : Fin n) :
    sameBlockBool (extendSingleton π).blocks i.castSucc j.castSucc =
      sameBlockBool π.blocks i j := by
  rw [sameBlock_extendSingleton]
  simp [relSingleton, i.isLt, j.isLt]

theorem sameBlock_extendJoinRep_castSucc {n : Nat} (π : SetPartition n) (r i j : Fin n) :
    sameBlockBool (extendJoinRep π r).blocks i.castSucc j.castSucc =
      sameBlockBool π.blocks i j := by
  rw [sameBlock_extendJoinRep]
  simp [relJoinRep, projToRep, i.isLt, j.isLt]

theorem mem_extendOnePartition_proj {n : Nat} {π : SetPartition n}
    {σ : SetPartition (n + 1)} (hσ : σ ∈ extendOnePartition π) (i j : Fin n) :
    sameBlockBool σ.blocks i.castSucc j.castSucc = sameBlockBool π.blocks i j := by
  unfold extendOnePartition at hσ
  cases hσ with
  | head => exact sameBlock_extendSingleton_castSucc π i j
  | tail _ hm =>
    rcases List.mem_map.mp hm with ⟨r, _, rfl⟩
    exact sameBlock_extendJoinRep_castSucc π r i j

theorem nodup_extendOnePartition {n : Nat} (π : SetPartition n) :
    ListNodup (extendOnePartition π) := by
  unfold extendOnePartition
  have hnd_reps : ListNodup (classReps (sameBlockBool π.blocks)) :=
    nodup_filter _ (nodup_finRange n)
  refine ListNodup.cons ?_ (nodup_map_on hnd_reps ?_)
  · intro σ hσ heq
    rcases List.mem_map.mp hσ with ⟨r, _, rfl⟩
    have h1 : sameBlockBool (extendSingleton π).blocks r.castSucc (Fin.last n) =
        sameBlockBool (extendJoinRep π r).blocks r.castSucc (Fin.last n) :=
      congrArg (fun p => sameBlockBool p.blocks r.castSucc (Fin.last n)) heq
    rw [sameBlock_extendSingleton, sameBlock_extendJoinRep] at h1
    have hleft : relSingleton π r.castSucc (Fin.last n) = false := by
      simp [relSingleton, r.isLt]
    have hright : relJoinRep π r r.castSucc (Fin.last n) = true := by
      unfold relJoinRep projToRep
      simp [r.isLt, π.sameBlock_isEquivRel.refl r]
    rw [hleft, hright] at h1
    cases h1
  · intro r₁ hr₁ r₂ hr₂ heq
    have h1 : sameBlockBool (extendJoinRep π r₁).blocks r₁.castSucc (Fin.last n) =
        sameBlockBool (extendJoinRep π r₂).blocks r₁.castSucc (Fin.last n) :=
      congrArg (fun p => sameBlockBool p.blocks r₁.castSucc (Fin.last n)) heq
    rw [sameBlock_extendJoinRep, sameBlock_extendJoinRep] at h1
    have hleft : relJoinRep π r₁ r₁.castSucc (Fin.last n) = true := by
      unfold relJoinRep projToRep
      simp [r₁.isLt, π.sameBlock_isEquivRel.refl r₁]
    have hright : relJoinRep π r₂ r₁.castSucc (Fin.last n) = sameBlockBool π.blocks r₁ r₂ := by
      unfold relJoinRep projToRep
      simp [r₁.isLt]
    rw [hleft, hright] at h1
    have hcls := equivClass_eq_of_rel π.sameBlock_isEquivRel h1.symm
    rcases equivClass_head_of_isClassMin (pred_of_filter hr₁) with ⟨_, hc₁⟩
    rcases equivClass_head_of_isClassMin (pred_of_filter hr₂) with ⟨_, hc₂⟩
    rw [hc₁, hc₂] at hcls
    exact List.cons.inj hcls |>.1

theorem nodup_enumSetPartitions : ∀ (n : Nat), ListNodup (enumSetPartitions n)
  | 0 => ListNodup.cons (fun _ h => nomatch h) ListNodup.nil
  | n + 1 => by
    refine nodup_listFlatMap (nodup_enumSetPartitions n)
      (fun π _ => nodup_extendOnePartition π) ?_
    intro π₁ _ π₂ _ hne σ₁ hσ₁ σ₂ hσ₂ heq
    subst heq
    refine hne (SetPartition.ext_sameBlock fun i j => ?_)
    rw [← mem_extendOnePartition_proj hσ₁ i j, mem_extendOnePartition_proj hσ₂ i j]

theorem fin_eq_last_of_not_lt {n : Nat} (u : Fin (n + 1)) (hu : ¬ u.val < n) :
    u = Fin.last n := by
  have hlt := u.isLt
  exact Fin.ext (by simp only [Fin.last]; omega)

theorem mem_enumSetPartitions : ∀ {n : Nat} (π : SetPartition n), π ∈ enumSetPartitions n
  | 0, π => by
    have heq : π = ⟨[], rfl⟩ := SetPartition.ext_sameBlock (fun x => Fin.elim0 x)
    rw [heq]
    exact List.Mem.head []
  | n + 1, σ => by
    have hS := σ.sameBlock_isEquivRel
    let R : Fin n → Fin n → Bool := fun i j => sameBlockBool σ.blocks i.castSucc j.castSucc
    have hR : IsBoolEquivRel R :=
      { refl := fun i => hS.refl i.castSucc
        symm := fun h => hS.symm h
        trans := fun h1 h2 => hS.trans h1 h2 }
    let π : SetPartition n := ofEquivRel R hR
    have hπ_rel : ∀ i j : Fin n, sameBlockBool π.blocks i j =
        sameBlockBool σ.blocks i.castSucc j.castSucc :=
      fun i j => sameBlockBool_blocksOfRel hR i j
    refine mem_listFlatMap.mpr ⟨π, mem_enumSetPartitions π, ?_⟩
    unfold extendOnePartition
    by_cases hex : (finRange n).any (fun i => sameBlockBool σ.blocks i.castSucc (Fin.last n)) = true
    · rcases List.any_eq_true.mp hex with ⟨i₀, _, hi₀⟩
      cases hcls : equivClass (sameBlockBool π.blocks) i₀ with
      | nil => exact False.elim (equivClass_nonempty π.sameBlock_isEquivRel i₀ hcls)
      | cons r tail =>
        have hi₀r : sameBlockBool π.blocks i₀ r = true :=
          (mem_equivClass_iff _ i₀ r).mp (by rw [hcls]; exact List.Mem.head tail)
        have heq_cls : equivClass (sameBlockBool π.blocks) r = equivClass (sameBlockBool π.blocks) i₀ :=
          equivClass_eq_of_rel π.sameBlock_isEquivRel (π.sameBlock_isEquivRel.symm hi₀r)
        have hr_min : isClassMin (sameBlockBool π.blocks) r = true := by
          unfold isClassMin; rw [heq_cls, hcls]; simp
        have hr_rep : r ∈ classReps (sameBlockBool π.blocks) :=
          List.mem_filter.mpr ⟨mem_finRange r, hr_min⟩
        have hr_last : sameBlockBool σ.blocks r.castSucc (Fin.last n) = true := by
          rw [hπ_rel] at hi₀r
          exact hS.trans (hS.symm hi₀r) hi₀
        refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r, hr_rep, ?_⟩)
        refine SetPartition.ext_sameBlock fun u v => ?_
        rw [sameBlock_extendJoinRep]
        unfold relJoinRep projToRep
        by_cases hu : u.val < n <;> by_cases hv : v.val < n
        · simp only [hu, hv, ↓reduceDIte]
          have h1 := hπ_rel ⟨u.val, hu⟩ ⟨v.val, hv⟩
          have hu_eq : (⟨u.val, hu⟩ : Fin n).castSucc = u := Fin.ext rfl
          have hv_eq : (⟨v.val, hv⟩ : Fin n).castSucc = v := Fin.ext rfl
          rw [hu_eq, hv_eq] at h1
          exact h1
        · simp only [hu, hv, ↓reduceDIte]
          have h1 := hπ_rel ⟨u.val, hu⟩ r
          have hu_eq : (⟨u.val, hu⟩ : Fin n).castSucc = u := Fin.ext rfl
          have hv_eq := fin_eq_last_of_not_lt v hv
          rw [hu_eq] at h1; subst hv_eq
          rw [h1]
          cases hSu : sameBlockBool σ.blocks u (Fin.last n) with
          | true => exact hS.trans hSu (hS.symm hr_last)
          | false =>
            cases hSur : sameBlockBool σ.blocks u r.castSucc with
            | false => rfl
            | true =>
              exfalso
              have h2 := hS.trans hSur hr_last
              rw [hSu] at h2; cases h2
        · simp only [hu, hv, ↓reduceDIte]
          have h1 := hπ_rel r ⟨v.val, hv⟩
          have hu_eq := fin_eq_last_of_not_lt u hu
          have hv_eq : (⟨v.val, hv⟩ : Fin n).castSucc = v := Fin.ext rfl
          rw [hv_eq] at h1; subst hu_eq
          rw [h1]
          cases hSv : sameBlockBool σ.blocks (Fin.last n) v with
          | true => exact hS.trans hr_last hSv
          | false =>
            cases hSrv : sameBlockBool σ.blocks r.castSucc v with
            | false => rfl
            | true =>
              exfalso
              have h2 := hS.trans (hS.symm hr_last) hSrv
              rw [hSv] at h2; cases h2
        · simp only [hu, hv, ↓reduceDIte, π.sameBlock_isEquivRel.refl r]
          have hu_eq := fin_eq_last_of_not_lt u hu
          have hv_eq := fin_eq_last_of_not_lt v hv
          subst hu_eq; subst hv_eq
          exact (hS.refl (Fin.last n)).symm
    · have hno : ∀ i : Fin n, sameBlockBool σ.blocks i.castSucc (Fin.last n) = false := by
        intro i
        cases hSi : sameBlockBool σ.blocks i.castSucc (Fin.last n) with
        | false => rfl
        | true =>
          exfalso
          exact hex (List.any_eq_true.mpr ⟨i, mem_finRange i, hSi⟩)
      have heq : extendSingleton π = σ := by
        refine SetPartition.ext_sameBlock fun u v => ?_
        rw [sameBlock_extendSingleton]
        unfold relSingleton
        by_cases hu : u.val < n <;> by_cases hv : v.val < n
        · simp only [hu, hv, ↓reduceDIte]
          have h1 := hπ_rel ⟨u.val, hu⟩ ⟨v.val, hv⟩
          have hu_eq : (⟨u.val, hu⟩ : Fin n).castSucc = u := Fin.ext rfl
          have hv_eq : (⟨v.val, hv⟩ : Fin n).castSucc = v := Fin.ext rfl
          rw [hu_eq, hv_eq] at h1
          exact h1
        · simp only [hu, hv, ↓reduceDIte]
          have hu_eq : (⟨u.val, hu⟩ : Fin n).castSucc = u := Fin.ext rfl
          have hv_eq := fin_eq_last_of_not_lt v hv
          subst hv_eq
          have hn := hno ⟨u.val, hu⟩
          rw [hu_eq] at hn
          exact hn.symm
        · simp only [hu, ↓reduceDIte]
          have hu_eq := fin_eq_last_of_not_lt u hu
          have hv_eq : (⟨v.val, hv⟩ : Fin n).castSucc = v := Fin.ext rfl
          subst hu_eq
          have hn := hno ⟨v.val, hv⟩
          rw [hv_eq] at hn
          have hne_uv : Fin.last n ≠ v := fun h => by
            have hval := congrArg Fin.val h
            simp only [Fin.last] at hval; omega
          simp only [hne_uv, decide_false]
          cases hSv : sameBlockBool σ.blocks (Fin.last n) v with
          | false => rfl
          | true =>
            exfalso
            have hsym := hS.symm hSv
            rw [hn] at hsym; cases hsym
        · simp only [hu, ↓reduceDIte]
          have hu_eq := fin_eq_last_of_not_lt u hu
          have hv_eq := fin_eq_last_of_not_lt v hv
          subst hu_eq; subst hv_eq
          simp [hS.refl (Fin.last n)]
      rw [← heq]
      exact List.Mem.head _

theorem setPartition_hasCardinality (n : Nat) :
    HasCardinality (SetPartition n) (enumSetPartitions n).length :=
  ⟨enumSetPartitions n, nodup_enumSetPartitions n, mem_enumSetPartitions, rfl⟩

def enumNCPartitions (n : Nat) : List (NCPartition n) :=
  let raw := (enumSetPartitions n).filter isNoncrossingBool
  subtypeList raw (fun π hπ => (isNoncrossingBool_iff π).mp (pred_of_filter hπ))

theorem nodup_enumNCPartitions (n : Nat) : ListNodup (enumNCPartitions n) :=
  subtypeList_nodup _ (nodup_filter _ (nodup_enumSetPartitions n)) _

theorem mem_enumNCPartitions {n : Nat} (π : NCPartition n) : π ∈ enumNCPartitions n := by
  refine subtypeList_mem _ _ π ?_
  exact List.mem_filter.mpr ⟨mem_enumSetPartitions π.val, (isNoncrossingBool_iff π.val).mpr π.property⟩

theorem ncPartition_hasCardinality (n : Nat) :
    HasCardinality (NCPartition n) (enumNCPartitions n).length :=
  ⟨enumNCPartitions n, nodup_enumNCPartitions n, mem_enumNCPartitions, rfl⟩

/-! ### Refinement Order and Universal Lattice Instances on `SetPartition n` and `NCPartition n` -/

/-- Textbook block-refinement order: every block of `π₁` is a subset of some block of `π₂`. -/
def Refines {n : Nat} (π₁ π₂ : SetPartition n) : Prop :=
  ∀ B₁ ∈ π₁.blocks, ∃ B₂ ∈ π₂.blocks, ∀ x ∈ B₁, x ∈ B₂

def refinesBool {n : Nat} (π₁ π₂ : SetPartition n) : Bool :=
  (finRange n).all fun x =>
    (finRange n).all fun y =>
      if sameBlockBool π₁.blocks x y then sameBlockBool π₂.blocks x y else true

theorem refinesBool_iff_sameBlock {n : Nat} (π₁ π₂ : SetPartition n) :
    refinesBool π₁ π₂ = true ↔
      (∀ x y : Fin n, sameBlockBool π₁.blocks x y = true → sameBlockBool π₂.blocks x y = true) := by
  unfold refinesBool
  constructor
  · intro h x y hxy
    have hx := List.all_eq_true.mp h x (mem_finRange x)
    have hy := List.all_eq_true.mp hx y (mem_finRange y)
    rw [if_pos hxy] at hy
    exact hy
  · intro h
    refine List.all_eq_true.mpr fun x _ => List.all_eq_true.mpr fun y _ => ?_
    split
    · next hxy => exact h x y hxy
    · rfl

theorem refines_iff_sameBlock {n : Nat} (π₁ π₂ : SetPartition n) :
    Refines π₁ π₂ ↔
      (∀ x y : Fin n, sameBlockBool π₁.blocks x y = true → sameBlockBool π₂.blocks x y = true) := by
  constructor
  · intro href x y hxy
    rcases List.any_eq_true.mp hxy with ⟨B₁, hB₁, hboth⟩
    rcases Bool.and_eq_true_iff.mp hboth with ⟨hx, hy⟩
    rcases href B₁ hB₁ with ⟨B₂, hB₂, hsub⟩
    exact List.any_eq_true.mpr ⟨B₂, hB₂,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hsub x (of_decide_eq_true hx)),
        decide_eq_true (hsub y (of_decide_eq_true hy))⟩⟩
  · intro h B₁ hB₁
    cases hBeq : B₁ with
    | nil => exact False.elim ((π₁.block_nonempty_strictInc hB₁).1 hBeq)
    | cons r tail =>
      rcases π₂.unique_block r with ⟨B₂, hB₂, hrB₂, huniq₂⟩
      refine ⟨B₂, hB₂, ?_⟩
      intro x hx_rt
      have hrB₁ : r ∈ B₁ := by rw [hBeq]; exact List.Mem.head tail
      have hxB₁ : x ∈ B₁ := by rw [hBeq]; exact hx_rt
      have hrx₁ : sameBlockBool π₁.blocks r x = true :=
        List.any_eq_true.mpr ⟨B₁, hB₁, by simp [hrB₁, hxB₁]⟩
      have hrx₂ := h r x hrx₁
      rcases List.any_eq_true.mp hrx₂ with ⟨B₂', hB₂', hboth⟩
      rcases Bool.and_eq_true_iff.mp hboth with ⟨hr', hx'⟩
      have heq := huniq₂ B₂' hB₂' (of_decide_eq_true hr')
      subst heq
      exact of_decide_eq_true hx'

theorem refinesBool_iff {n : Nat} (π₁ π₂ : SetPartition n) :
    refinesBool π₁ π₂ = true ↔ Refines π₁ π₂ :=
  (refinesBool_iff_sameBlock π₁ π₂).trans (refines_iff_sameBlock π₁ π₂).symm

theorem infRel_isEquivRel {n : Nat} (π₁ π₂ : SetPartition n) :
    IsBoolEquivRel (fun x y => sameBlockBool π₁.blocks x y && sameBlockBool π₂.blocks x y) where
  refl x := Bool.and_eq_true_iff.mpr ⟨π₁.sameBlock_isEquivRel.refl x, π₂.sameBlock_isEquivRel.refl x⟩
  symm h := by
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    exact Bool.and_eq_true_iff.mpr ⟨π₁.sameBlock_isEquivRel.symm h1, π₂.sameBlock_isEquivRel.symm h2⟩
  trans ha hb := by
    rcases Bool.and_eq_true_iff.mp ha with ⟨ha1, ha2⟩
    rcases Bool.and_eq_true_iff.mp hb with ⟨hb1, hb2⟩
    exact Bool.and_eq_true_iff.mpr ⟨π₁.sameBlock_isEquivRel.trans ha1 hb1, π₂.sameBlock_isEquivRel.trans ha2 hb2⟩

def setPartitionInf {n : Nat} (π₁ π₂ : SetPartition n) : SetPartition n :=
  ofEquivRel _ (infRel_isEquivRel π₁ π₂)

theorem sameBlock_setPartitionInf {n : Nat} (π₁ π₂ : SetPartition n) (x y : Fin n) :
    sameBlockBool (setPartitionInf π₁ π₂).blocks x y =
      (sameBlockBool π₁.blocks x y && sameBlockBool π₂.blocks x y) :=
  sameBlockBool_blocksOfRel (infRel_isEquivRel π₁ π₂) x y

theorem topRel_isEquivRel (n : Nat) : IsBoolEquivRel (fun (_ _ : Fin n) => true) where
  refl _ := rfl
  symm _ := rfl
  trans _ _ := rfl

def setPartitionTop (n : Nat) : SetPartition n :=
  ofEquivRel _ (topRel_isEquivRel n)

theorem refines_setPartitionTop {n : Nat} (π : SetPartition n) :
    Refines π (setPartitionTop n) := by
  rw [refines_iff_sameBlock]
  intro x y _
  exact sameBlockBool_blocksOfRel (topRel_isEquivRel n) x y

theorem setPartitionTop_isNoncrossing (n : Nat) : IsNoncrossing (setPartitionTop n) := by
  intro a b _ _ _ _ _ _ _
  exact sameBlockBool_blocksOfRel (topRel_isEquivRel n) a b

theorem setPartitionInf_isNoncrossing {n : Nat} {π₁ π₂ : SetPartition n}
    (h₁ : IsNoncrossing π₁) (h₂ : IsNoncrossing π₂) :
    IsNoncrossing (setPartitionInf π₁ π₂) := by
  intro a b c d hab hbc hcd hac hbd
  unfold SameBlock at hac hbd ⊢
  rw [sameBlock_setPartitionInf] at hac hbd ⊢
  rcases Bool.and_eq_true_iff.mp hac with ⟨hac₁, hac₂⟩
  rcases Bool.and_eq_true_iff.mp hbd with ⟨hbd₁, hbd₂⟩
  exact Bool.and_eq_true_iff.mpr ⟨h₁ a b c d hab hbc hcd hac₁ hbd₁, h₂ a b c d hab hbc hcd hac₂ hbd₂⟩

def foldrInf {α : Type} (infFn : α → α → α) (topElem : α) : List α → α
  | [] => topElem
  | x :: xs => infFn x (foldrInf infFn topElem xs)

theorem foldrInf_ge {α : Type} {leFn : α → α → Prop}
    {infFn : α → α → α}
    (hle_inf : ∀ {a b c : α}, leFn c a → leFn c b → leFn c (infFn a b))
    {z topElem : α} (htop : leFn z topElem) :
    ∀ {cands : List α}, (∀ u ∈ cands, leFn z u) → leFn z (foldrInf infFn topElem cands)
  | [], _ => htop
  | x :: xs, hall =>
    hle_inf (hall x (List.Mem.head xs))
      (foldrInf_ge hle_inf htop (fun u hu => hall u (List.mem_cons_of_mem x hu)))

theorem foldrInf_le_mem {α : Type} {leFn : α → α → Prop}
    (htrans : ∀ {a b c : α}, leFn a b → leFn b c → leFn a c)
    {infFn : α → α → α}
    (hinf_l : ∀ a b : α, leFn (infFn a b) a)
    (hinf_r : ∀ a b : α, leFn (infFn a b) b)
    {topElem w : α} :
    ∀ {cands : List α}, w ∈ cands → leFn (foldrInf infFn topElem cands) w
  | [], h => nomatch h
  | y :: xs, h => by
    cases h with
    | head => exact hinf_l w (foldrInf infFn topElem xs)
    | tail _ hm =>
      exact htrans (hinf_r y (foldrInf infFn topElem xs))
        (foldrInf_le_mem (leFn := leFn) htrans hinf_l hinf_r hm)

theorem refines_refl {n : Nat} (π : SetPartition n) : Refines π π :=
  (refines_iff_sameBlock π π).mpr fun _ _ h => h

theorem refines_trans {n : Nat} {π₁ π₂ π₃ : SetPartition n}
    (h12 : Refines π₁ π₂) (h23 : Refines π₂ π₃) : Refines π₁ π₃ :=
  (refines_iff_sameBlock π₁ π₃).mpr fun x y h =>
    (refines_iff_sameBlock π₂ π₃).mp h23 x y ((refines_iff_sameBlock π₁ π₂).mp h12 x y h)

theorem refines_antisymm {n : Nat} {π₁ π₂ : SetPartition n}
    (h12 : Refines π₁ π₂) (h21 : Refines π₂ π₁) : π₁ = π₂ := by
  refine SetPartition.ext_sameBlock fun x y => ?_
  have f12 := (refines_iff_sameBlock π₁ π₂).mp h12 x y
  have f21 := (refines_iff_sameBlock π₂ π₁).mp h21 x y
  cases h1 : sameBlockBool π₁.blocks x y <;> cases h2 : sameBlockBool π₂.blocks x y
  · rfl
  · exfalso; have := f21 h2; rw [h1] at this; cases this
  · exfalso; have := f12 h1; rw [h2] at this; cases this
  · rfl

theorem setPartitionInf_le_left {n : Nat} (π₁ π₂ : SetPartition n) :
    Refines (setPartitionInf π₁ π₂) π₁ := by
  rw [refines_iff_sameBlock]
  intro x y h
  rw [sameBlock_setPartitionInf] at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem setPartitionInf_le_right {n : Nat} (π₁ π₂ : SetPartition n) :
    Refines (setPartitionInf π₁ π₂) π₂ := by
  rw [refines_iff_sameBlock]
  intro x y h
  rw [sameBlock_setPartitionInf] at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem le_setPartitionInf {n : Nat} {π₁ π₂ τ : SetPartition n}
    (h₁ : Refines τ π₁) (h₂ : Refines τ π₂) :
    Refines τ (setPartitionInf π₁ π₂) := by
  rw [refines_iff_sameBlock]
  intro x y h
  rw [sameBlock_setPartitionInf]
  exact Bool.and_eq_true_iff.mpr
    ⟨(refines_iff_sameBlock τ π₁).mp h₁ x y h, (refines_iff_sameBlock τ π₂).mp h₂ x y h⟩

def setPartitionSup {n : Nat} (π₁ π₂ : SetPartition n) : SetPartition n :=
  let ubs := (enumSetPartitions n).filter (fun τ => refinesBool π₁ τ && refinesBool π₂ τ)
  foldrInf setPartitionInf (setPartitionTop n) ubs

/-- Full set partition lattice `Π_n` under refinement for every `n : Nat`. -/
instance setPartitionLattice (n : Nat) : Lattice (SetPartition n) where
  le := Refines
  le_refl := refines_refl
  le_trans := refines_trans
  le_antisymm := refines_antisymm
  inf := setPartitionInf
  sup := setPartitionSup
  inf_le_left := setPartitionInf_le_left
  inf_le_right := setPartitionInf_le_right
  le_inf := le_setPartitionInf
  le_sup_left π₁ π₂ := by
    refine foldrInf_ge (leFn := Refines) le_setPartitionInf (refines_setPartitionTop π₁) ?_
    intro τ hτ
    have hp : (refinesBool π₁ τ && refinesBool π₂ τ) = true := (List.mem_filter.mp hτ).2
    exact (refinesBool_iff π₁ τ).mp (Bool.and_eq_true_iff.mp hp).1
  le_sup_right π₁ π₂ := by
    refine foldrInf_ge (leFn := Refines) le_setPartitionInf (refines_setPartitionTop π₂) ?_
    intro τ hτ
    have hp : (refinesBool π₁ τ && refinesBool π₂ τ) = true := (List.mem_filter.mp hτ).2
    exact (refinesBool_iff π₂ τ).mp (Bool.and_eq_true_iff.mp hp).2
  sup_le {π₁ π₂ τ} h₁ h₂ := by
    refine foldrInf_le_mem (leFn := Refines) refines_trans
      (fun a b => setPartitionInf_le_left a b)
      (fun a b => setPartitionInf_le_right a b) ?_
    exact List.mem_filter.mpr ⟨mem_enumSetPartitions τ,
      Bool.and_eq_true_iff.mpr ⟨(refinesBool_iff π₁ τ).mpr h₁, (refinesBool_iff π₂ τ).mpr h₂⟩⟩

def ncInf {n : Nat} (π₁ π₂ : NCPartition n) : NCPartition n :=
  ⟨setPartitionInf π₁.val π₂.val, setPartitionInf_isNoncrossing π₁.property π₂.property⟩

def ncTop (n : Nat) : NCPartition n :=
  ⟨setPartitionTop n, setPartitionTop_isNoncrossing n⟩

def ncSup {n : Nat} (π₁ π₂ : NCPartition n) : NCPartition n :=
  let ubs := (enumNCPartitions n).filter (fun τ => refinesBool π₁.val τ.val && refinesBool π₂.val τ.val)
  foldrInf ncInf (ncTop n) ubs

/-- The noncrossing partition lattice `NC_n` under refinement for every `n : Nat`. -/
instance ncPartitionLattice (n : Nat) : Lattice (NCPartition n) where
  le a b := Refines a.val b.val
  le_refl a := refines_refl a.val
  le_trans h1 h2 := refines_trans h1 h2
  le_antisymm h1 h2 := Subtype.ext (refines_antisymm h1 h2)
  inf := ncInf
  sup := ncSup
  inf_le_left a b := setPartitionInf_le_left a.val b.val
  inf_le_right a b := setPartitionInf_le_right a.val b.val
  le_inf h1 h2 := le_setPartitionInf h1 h2
  le_sup_left a b := by
    refine foldrInf_ge (leFn := fun x y : NCPartition n => Refines x.val y.val)
      (fun h1 h2 => le_setPartitionInf h1 h2) (refines_setPartitionTop a.val) ?_
    intro τ hτ
    have hp : (refinesBool a.val τ.val && refinesBool b.val τ.val) = true := (List.mem_filter.mp hτ).2
    exact (refinesBool_iff a.val τ.val).mp (Bool.and_eq_true_iff.mp hp).1
  le_sup_right a b := by
    refine foldrInf_ge (leFn := fun x y : NCPartition n => Refines x.val y.val)
      (fun h1 h2 => le_setPartitionInf h1 h2) (refines_setPartitionTop b.val) ?_
    intro τ hτ
    have hp : (refinesBool a.val τ.val && refinesBool b.val τ.val) = true := (List.mem_filter.mp hτ).2
    exact (refinesBool_iff b.val τ.val).mp (Bool.and_eq_true_iff.mp hp).2
  sup_le {a b c} h1 h2 := by
    refine foldrInf_le_mem (leFn := fun x y : NCPartition n => Refines x.val y.val)
      (fun u v => refines_trans u v)
      (fun x y => setPartitionInf_le_left x.val y.val)
      (fun x y => setPartitionInf_le_right x.val y.val) ?_
    exact List.mem_filter.mpr ⟨mem_enumNCPartitions c,
      Bool.and_eq_true_iff.mpr ⟨(refinesBool_iff a.val c.val).mpr h1, (refinesBool_iff b.val c.val).mpr h2⟩⟩

/-! ## 6. Block-Size Products, Exact Counts, and Non-Vacuity Witnesses -/

/-- Product of block sizes `∏_{B ∈ π} |B|` of a set partition `π`. -/
def partitionBlockSizeProd {n : Nat} (π : SetPartition n) : Nat :=
  listProd (π.blocks.map List.length)

/-- Product of all block sizes across `NC_n`: `D_n = ∏_{π ∈ NC_n} ∏_{B ∈ π} |B|`. -/
def ncBlockSizeProduct (n : Nat) : Nat :=
  listProd ((enumNCPartitions n).map (fun π => partitionBlockSizeProd π.val))

/-- Product of all block sizes across the full partition lattice `Π_n`. -/
def piBlockSizeProduct (n : Nat) : Nat :=
  listProd ((enumSetPartitions n).map partitionBlockSizeProd)

theorem nc1_card : HasCardinality (NCPartition 1) 1 :=
  ⟨enumNCPartitions 1, nodup_enumNCPartitions 1, mem_enumNCPartitions, by decide⟩

theorem nc2_card : HasCardinality (NCPartition 2) 2 :=
  ⟨enumNCPartitions 2, nodup_enumNCPartitions 2, mem_enumNCPartitions, by decide⟩

theorem nc3_card : HasCardinality (NCPartition 3) 5 :=
  ⟨enumNCPartitions 3, nodup_enumNCPartitions 3, mem_enumNCPartitions, by decide⟩

theorem nc4_card : HasCardinality (NCPartition 4) 14 :=
  ⟨enumNCPartitions 4, nodup_enumNCPartitions 4, mem_enumNCPartitions, by decide⟩

theorem nc5_card : HasCardinality (NCPartition 5) 42 :=
  ⟨enumNCPartitions 5, nodup_enumNCPartitions 5, mem_enumNCPartitions, by decide⟩

theorem pi4_card : HasCardinality (SetPartition 4) 15 :=
  ⟨enumSetPartitions 4, nodup_enumSetPartitions 4, mem_enumSetPartitions, by decide⟩

theorem nc1_blockSizeProd_eq : ncBlockSizeProduct 1 = 1 := by decide
theorem nc2_blockSizeProd_eq : ncBlockSizeProduct 2 = 2 := by decide
theorem nc3_blockSizeProd_eq : ncBlockSizeProduct 3 = 24 := by decide
theorem nc4_blockSizeProd_eq : ncBlockSizeProduct 4 = 331776 := by decide
theorem pi4_blockSizeProd_eq : piBlockSizeProduct 4 = 1327104 := by decide

def ncRefinesBool {n : Nat} (a b : NCPartition n) : Bool :=
  refinesBool a.val b.val

theorem ncRefinesBool_iff {n : Nat} (a b : NCPartition n) :
    ncRefinesBool a b = true ↔ a ≼ b :=
  refinesBool_iff a.val b.val

theorem nc1_linExt : HasLinearExtensionCount (NCPartition 1) 1 :=
  verifyPosetLinExtCount_sound (nodup_enumNCPartitions 1) mem_enumNCPartitions
    ncRefinesBool_iff (by decide)

theorem nc2_linExt : HasLinearExtensionCount (NCPartition 2) 1 :=
  verifyPosetLinExtCount_sound (nodup_enumNCPartitions 2) mem_enumNCPartitions
    ncRefinesBool_iff (by decide)

theorem nc3_linExt : HasLinearExtensionCount (NCPartition 3) 6 :=
  verifyPosetLinExtCount_sound (nodup_enumNCPartitions 3) mem_enumNCPartitions
    ncRefinesBool_iff (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Key enumeration theorem: the 14-element noncrossing partition lattice `NC_4`
has **exact** linear extension count `e(NC_4) = 1,399,200 = 2^5 * 3 * 5^2 * 11 * 53`. -/
theorem nc4_linExt : HasLinearExtensionCount (NCPartition 4) 1399200 :=
  verifyPosetLinExtCount_sound (nodup_enumNCPartitions 4) mem_enumNCPartitions
    ncRefinesBool_iff (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Exact linear extension count of the 15-element full partition lattice `Π_4`:
`e(Π_4) = 10,368,000 = 2^10 * 3^4 * 5^3`. -/
theorem pi4_linExt : HasLinearExtensionCount (SetPartition 4) 10368000 :=
  verifyPosetLinExtCount_sound (nodup_enumSetPartitions 4) mem_enumSetPartitions
    refinesBool_iff (by decide)

/-! ### Hook-Length Product Formulations and Positive Non-Vacuity Witnesses -/

/-- A finite poset `P` admits a standard poset hook-length product formula if
there exist positive integer hook lengths `h : P → Nat` such that
`|P|! = e(P) * ∏_{x ∈ P} h(x)`. -/
def HasIntegerHookFormula (P : Type u) [Poset P] : Prop :=
  ∃ (elems : List P) (e : Nat) (h : P → Nat),
    ListNodup elems ∧ (∀ x : P, x ∈ elems) ∧
    HasLinearExtensionCount P e ∧
    (∀ x : P, 0 < h x) ∧
    natFactorial elems.length = e * listProd (elems.map h)

/-- Literal block-size hook-length product formula on `NC_n`:
`|NC_n|! = e(NC_n) * ∏_{π ∈ NC_n} ∏_{B ∈ π} |B|`. -/
def SatisfiesNCBlockSizeHookFormula (n : Nat) : Prop :=
  ∃ (N e : Nat),
    HasCardinality (NCPartition n) N ∧
    HasLinearExtensionCount (NCPartition n) e ∧
    natFactorial N = e * ncBlockSizeProduct n

/-- Literal block-size hook-length product formula on the full partition lattice `Π_n`. -/
def SatisfiesPiBlockSizeHookFormula (n : Nat) : Prop :=
  ∃ (N e : Nat),
    HasCardinality (SetPartition n) N ∧
    HasLinearExtensionCount (SetPartition n) e ∧
    natFactorial N = e * piBlockSizeProduct n

/-- Positive non-vacuity witness at `n = 1`: `|NC_1| = 1`, `e(NC_1) = 1`, `D_1 = 1`,
and `1! = 1 * 1`. -/
theorem nc1_positive_witness :
    SatisfiesNCBlockSizeHookFormula 1 ∧ HasIntegerHookFormula (NCPartition 1) := by
  refine ⟨⟨1, 1, nc1_card, nc1_linExt, by decide⟩, ?_⟩
  have hpos : (enumNCPartitions 1).all (fun π => decide (0 < partitionBlockSizeProd π.val)) = true :=
    by decide
  refine ⟨enumNCPartitions 1, 1, fun π => partitionBlockSizeProd π.val,
    nodup_enumNCPartitions 1, mem_enumNCPartitions, nc1_linExt, ?_, by decide⟩
  intro π
  exact of_decide_eq_true (List.all_eq_true.mp hpos π (mem_enumNCPartitions π))

/-- Positive non-vacuity witness at `n = 2`: `|NC_2| = 2`, `e(NC_2) = 1`, `D_2 = 2`,
and `2! = 1 * 2`. Thus the exact conjectured block-size hook-length identity holds
non-vacuously for both `n = 1` and `n = 2`. -/
theorem nc2_positive_witness :
    SatisfiesNCBlockSizeHookFormula 2 ∧ HasIntegerHookFormula (NCPartition 2) := by
  refine ⟨⟨2, 1, nc2_card, nc2_linExt, by decide⟩, ?_⟩
  have hpos : (enumNCPartitions 2).all (fun π => decide (0 < partitionBlockSizeProd π.val)) = true :=
    by decide
  refine ⟨enumNCPartitions 2, 1, fun π => partitionBlockSizeProd π.val,
    nodup_enumNCPartitions 2, mem_enumNCPartitions, nc2_linExt, ?_, by decide⟩
  intro π
  exact of_decide_eq_true (List.all_eq_true.mp hpos π (mem_enumNCPartitions π))

/-! ## 7. Complete Disproof of Conjecture 00000004768 -/

/-- Counterexample at `n = 3` to the block-size denominator formula:
`|NC_3| = 5`, `e(NC_3) = 6`, `D_3 = 24`, so `5! = 120 ≠ 144 = 6 * 24`. -/
theorem disproof_blockSize_hook_n3 : ¬ SatisfiesNCBlockSizeHookFormula 3 := by
  rintro ⟨N, e, hN, he, heq⟩
  have hN5 : N = 5 := hasCardinality_unique hN nc3_card
  have he6 : e = 6 := hasLinearExtensionCount_unique he nc3_linExt
  subst hN5; subst he6
  rw [nc3_blockSizeProd_eq] at heq
  have hbad : natFactorial 5 ≠ 6 * 24 := by decide
  exact hbad heq

/-- Counterexample at `n = 4` to the block-size denominator formula:
`|NC_4| = 14`, `e(NC_4) = 1,399,200`, `D_4 = 331,776`, and `14! ≠ e(NC_4) * D_4`. -/
theorem disproof_blockSize_hook_n4 : ¬ SatisfiesNCBlockSizeHookFormula 4 := by
  rintro ⟨N, e, hN, he, heq⟩
  have hN14 : N = 14 := hasCardinality_unique hN nc4_card
  have he4 : e = 1399200 := hasLinearExtensionCount_unique he nc4_linExt
  subst hN14; subst he4
  rw [nc4_blockSizeProd_eq] at heq
  have hdvd53 : 53 ∣ 1399200 * 331776 := ⟨26400 * 331776, by decide⟩
  rw [← heq] at hdvd53
  exact isPrime_53.not_dvd_factorial (by decide : 14 < 53) hdvd53

/-- Prime-factor obstruction for `NC_4`: since `53` is prime and `53 ∣ 1,399,200`,
`e(NC_4)` cannot divide `m!` for ANY `m < 53` (including `|NC_4| = 14`,
`|NC_4| - 2 = 12`, `2*4 = 8`, `4^2 = 16`, `|NC_5| = 42`). -/
theorem nc4_linExt_not_dvd_factorial_lt53 {m e D : Nat}
    (hm : m < 53) (he : HasLinearExtensionCount (NCPartition 4) e) :
    natFactorial m ≠ e * D := by
  intro heq
  have he_val : e = 1399200 := hasLinearExtensionCount_unique he nc4_linExt
  subst he_val
  have hdvd53 : 53 ∣ 1399200 * D := ⟨26400 * D, by omega⟩
  rw [← heq] at hdvd53
  exact isPrime_53.not_dvd_factorial hm hdvd53

/-- Universal hook-length impossibility for `NC_4`: `NC_4` admits **no** integer-valued
poset hook-length product formula `|NC_4|! = e(NC_4) * ∏_{π ∈ NC_4} h(π)` for ANY
assignment `h : NCPartition 4 → Nat` whatsoever. -/
theorem nc4_no_integer_hook_formula : ¬ HasIntegerHookFormula (NCPartition 4) := by
  rintro ⟨elems, e, _, hnd, hall, he, _, heq⟩
  have hlen : elems.length = 14 := hasCardinality_unique ⟨elems, hnd, hall, rfl⟩ nc4_card
  rw [hlen] at heq
  exact nc4_linExt_not_dvd_factorial_lt53 (by decide : 14 < 53) he heq

/-- Bounded-numerator impossibility over ANY positive denominator `D` (in particular
the block-size product `D_4 = ncBlockSizeProduct 4` or block-factorial product):
no finite product of positive integers `< 53` can equal `e(NC_4) * D`. -/
theorem nc4_no_bounded_product_over_denominator
    {e D : Nat} (he : HasLinearExtensionCount (NCPartition 4) e)
    (factors : List Nat) (hbnd : ∀ a ∈ factors, 0 < a ∧ a < 53) :
    listProd factors ≠ e * D := by
  intro heq
  have he_val : e = 1399200 := hasLinearExtensionCount_unique he nc4_linExt
  subst he_val
  have hdvd53 : 53 ∣ 1399200 * D := ⟨26400 * D, by omega⟩
  rw [← heq] at hdvd53
  exact isPrime_53.not_dvd_listProd_bounded hbnd hdvd53

/-- Specific instantiation for the conjectured block-size denominator `D_4 = ncBlockSizeProduct 4`:
no product of positive integers bounded by `|NC_4| = 14` (or any bound `< 53`) can serve
as the numerator of `e(NC_4) = (∏ a_i) / D_4`. -/
theorem nc4_no_bounded_product_over_blockSizes
    {e : Nat} (he : HasLinearExtensionCount (NCPartition 4) e)
    (factors : List Nat) (hbnd : ∀ a ∈ factors, 0 < a ∧ a ≤ 14) :
    listProd factors ≠ e * ncBlockSizeProduct 4 := by
  refine nc4_no_bounded_product_over_denominator he factors (fun a ha => ?_)
  rcases hbnd a ha with ⟨h0, h14⟩
  exact ⟨h0, by omega⟩

/-- Full three-clause formalization of Conjecture 00000004768 under the standard
poset hook-length product (`|NC_n|! = e(NC_n) * D_n` with `D_n` the product of
block sizes, together with any polynomial-time computability predicate). -/
def Conjecture4768_Standard (PolyTimeComputable : (Nat → Nat) → Prop) : Prop :=
  (∀ n : Nat, 1 ≤ n → SatisfiesNCBlockSizeHookFormula n) ∧
  (∃ f : Nat → Nat, (∀ n : Nat, 1 ≤ n → HasLinearExtensionCount (NCPartition n) (f n)) ∧
    PolyTimeComputable f)

theorem disproof_conjecture4768_standard
    (PolyTimeComputable : (Nat → Nat) → Prop) :
    ¬ Conjecture4768_Standard PolyTimeComputable := by
  rintro ⟨hhook, _⟩
  exact disproof_blockSize_hook_n3 (hhook 3 (by decide))

/-- Generalized multi-clause formalization of Conjecture 00000004768 allowing:
(a) ANY integer hook-length formula `|NC_n|! = e(NC_n) * ∏ h(π)`, OR
(b) ANY rational hook-type product `(∏ a_i) / D_n` over `D_n = ncBlockSizeProduct n`
    whose numerator factors are bounded by `2 * |NC_n|` (`= 28 < 53` at `n = 4`). -/
def Conjecture4768_Generalized (PolyTimeComputable : (Nat → Nat) → Prop) : Prop :=
  (∀ n : Nat, 1 ≤ n →
    HasIntegerHookFormula (NCPartition n) ∨
    (∃ (N e : Nat) (factors : List Nat),
      HasCardinality (NCPartition n) N ∧
      HasLinearExtensionCount (NCPartition n) e ∧
      (∀ a ∈ factors, 0 < a ∧ a ≤ 2 * N) ∧
      listProd factors = e * ncBlockSizeProduct n)) ∧
  (∃ f : Nat → Nat, (∀ n : Nat, 1 ≤ n → HasLinearExtensionCount (NCPartition n) (f n)) ∧
    PolyTimeComputable f)

theorem disproof_conjecture4768_generalized
    (PolyTimeComputable : (Nat → Nat) → Prop) :
    ¬ Conjecture4768_Generalized PolyTimeComputable := by
  rintro ⟨hgen, _⟩
  rcases hgen 4 (by decide) with hhook | ⟨N, e, factors, hN, he, hbnd, heq⟩
  · exact nc4_no_integer_hook_formula hhook
  · have hN14 : N = 14 := hasCardinality_unique hN nc4_card
    subst hN14
    refine nc4_no_bounded_product_over_denominator he factors (fun a ha => ?_) heq
    rcases hbnd a ha with ⟨h0, h28⟩
    exact ⟨h0, by omega⟩

/-- Bonus disproof for the full partition lattice `Π_n` (`SetPartition n`): even if
"the poset lattice of partitions under refinement" were read as the unrestricted
partition lattice `Π_n`, the block-size product formula fails (`15! ≠ 10,368,000 * 1,327,104`),
and `e(Π_4)` does not divide `(|Π_4| - 2)! = 13!` (`5^3 ∣ e(Π_4)` while `v_5(13!) = 2`). -/
theorem disproof_conjecture4768_fullPartitionLattice :
    ¬ (∀ n : Nat, 1 ≤ n → SatisfiesPiBlockSizeHookFormula n) ∧
    (∀ e D : Nat, HasLinearExtensionCount (SetPartition 4) e → natFactorial 13 ≠ e * D) := by
  refine ⟨?_, ?_⟩
  · intro hall
    rcases hall 4 (by decide) with ⟨N, e, hN, he, heq⟩
    have hN15 : N = 15 := hasCardinality_unique hN pi4_card
    have he4 : e = 10368000 := hasLinearExtensionCount_unique he pi4_linExt
    subst hN15; subst he4
    rw [pi4_blockSizeProd_eq] at heq
    have hbad : natFactorial 15 ≠ 10368000 * 1327104 := by decide
    exact hbad heq
  · intro e D he heq
    have he4 : e = 10368000 := hasLinearExtensionCount_unique he pi4_linExt
    subst he4
    have hdvd125 : 125 ∣ 10368000 * D := ⟨82944 * D, by omega⟩
    rw [← heq] at hdvd125
    rcases hdvd125 with ⟨q, hq⟩
    have hmod : natFactorial 13 % 125 = 50 := by decide
    have hmod2 : (125 * q) % 125 = 0 := Nat.mul_mod_right 125 q
    rw [← hq, hmod] at hmod2
    cases hmod2

end Conjecture4768

/-! ## 8. Axiom Audit (`#print axioms`) -/

#print axioms Conjecture4768.ncPartitionLattice
#print axioms Conjecture4768.setPartitionLattice
#print axioms Conjecture4768.isPrime_53
#print axioms Conjecture4768.IsPrime.dvd_mul
#print axioms Conjecture4768.nc1_positive_witness
#print axioms Conjecture4768.nc2_positive_witness
#print axioms Conjecture4768.nc3_linExt
#print axioms Conjecture4768.nc4_card
#print axioms Conjecture4768.nc4_linExt
#print axioms Conjecture4768.nc5_card
#print axioms Conjecture4768.pi4_linExt
#print axioms Conjecture4768.disproof_blockSize_hook_n3
#print axioms Conjecture4768.disproof_blockSize_hook_n4
#print axioms Conjecture4768.nc4_linExt_not_dvd_factorial_lt53
#print axioms Conjecture4768.nc4_no_integer_hook_formula
#print axioms Conjecture4768.nc4_no_bounded_product_over_blockSizes
#print axioms Conjecture4768.disproof_conjecture4768_standard
#print axioms Conjecture4768.disproof_conjecture4768_generalized
#print axioms Conjecture4768.disproof_conjecture4768_fullPartitionLattice
