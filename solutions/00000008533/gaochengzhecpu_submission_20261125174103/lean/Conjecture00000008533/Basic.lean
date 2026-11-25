/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization for Conjecture 00000008533:
Foundational definitions of exact rationals, finite lists/sums, finite geometric lattices,
and the incidence-algebra Möbius function (with both left and right inversion laws).
-/

namespace Conjecture00000008533

/-! ## 1. Self-Contained List, NoDup, and Summation Infrastructure -/

/-- Duplicate-free list predicate. -/
inductive NoDup {α : Type} : List α → Prop where
  | nil : NoDup []
  | cons {x : α} {xs : List α} : x ∉ xs → NoDup xs → NoDup (x :: xs)

def decideNoDup {α : Type} [DecidableEq α] : (xs : List α) → Decidable (NoDup xs)
  | [] => isTrue NoDup.nil
  | x :: xs =>
    match inferInstanceAs (Decidable (x ∈ xs)), decideNoDup xs with
    | isFalse hnin, isTrue hnd => isTrue (NoDup.cons hnin hnd)
    | isTrue hin, _ => isFalse (fun h => by cases h with | cons hn _ => exact hn hin)
    | _, isFalse hnd => isFalse (fun h => by cases h with | cons _ hd => exact hnd hd)

instance instDecidableNoDup {α : Type} [DecidableEq α] (xs : List α) : Decidable (NoDup xs) :=
  decideNoDup xs

theorem mem_filter_iff_prop {α : Type} (p : α → Bool) (xs : List α) (x : α) :
    x ∈ xs.filter p ↔ x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => simp [List.filter]
  | cons a as ih =>
    simp only [List.filter]
    cases hp : p a
    · simp only [List.mem_cons]
      constructor
      · intro h
        rcases ih.mp h with ⟨hm, hpx⟩
        exact ⟨Or.inr hm, hpx⟩
      · rintro ⟨rfl | hm', hpx⟩
        · rw [hp] at hpx; contradiction
        · exact ih.mpr ⟨hm', hpx⟩
    · simp only [List.mem_cons]
      constructor
      · rintro (rfl | hm)
        · exact ⟨Or.inl rfl, hp⟩
        · rcases ih.mp hm with ⟨hm', hpx⟩
          exact ⟨Or.inr hm', hpx⟩
      · rintro ⟨rfl | hm', hpx⟩
        · exact Or.inl rfl
        · exact Or.inr (ih.mpr ⟨hm', hpx⟩)

theorem nodup_filter {α : Type} (p : α → Bool) {xs : List α} (h : NoDup xs) :
    NoDup (xs.filter p) := by
  induction h with
  | nil => exact NoDup.nil
  | cons hnin _ ih =>
    simp only [List.filter]
    cases p _
    · exact ih
    · refine NoDup.cons ?_ ih
      intro hm
      exact hnin ((mem_filter_iff_prop p _ _).mp hm).1

/-- Sum of natural-number weights over a list. -/
def sumNat {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumNat rest f

/-- Sum of integer weights over a list. -/
def sumInt {α : Type} (xs : List α) (f : α → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumInt rest f

theorem sumNat_congr {α : Type} {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x = g x) : sumNat xs f = sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumNat]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem sumInt_congr {α : Type} {xs : List α} {f g : α → Int}
    (h : ∀ x ∈ xs, f x = g x) : sumInt xs f = sumInt xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumInt]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem sumNat_eq_zero {α : Type} {xs : List α} {f : α → Nat}
    (h : ∀ x ∈ xs, f x = 0) : sumNat xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumNat, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem sumInt_eq_zero {α : Type} {xs : List α} {f : α → Int}
    (h : ∀ x ∈ xs, f x = 0) : sumInt xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumInt, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rfl

theorem sumInt_add {α : Type} (xs : List α) (f g : α → Int) :
    sumInt xs (fun x => f x + g x) = sumInt xs f + sumInt xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumInt, ih]
    omega

theorem sumNat_add {α : Type} (xs : List α) (f g : α → Nat) :
    sumNat xs (fun x => f x + g x) = sumNat xs f + sumNat xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumNat, ih]
    omega

theorem sumInt_mul_left {α : Type} (xs : List α) (c : Int) (f : α → Int) :
    sumInt xs (fun x => c * f x) = c * sumInt xs f := by
  induction xs with
  | nil => simp [sumInt]
  | cons a as ih =>
    simp only [sumInt, ih, Int.mul_add]

theorem sumInt_mul_right {α : Type} (xs : List α) (f : α → Int) (c : Int) :
    sumInt xs (fun x => f x * c) = sumInt xs f * c := by
  induction xs with
  | nil => simp [sumInt]
  | cons a as ih =>
    simp only [sumInt, ih, Int.add_mul]

theorem sumNat_filter_split {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) :
    sumNat (xs.filter p) f + sumNat (xs.filter (fun x => !p x)) f = sumNat xs f := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter, sumNat]
    cases p a <;> simp only [Bool.not_false, Bool.not_true, sumNat] <;> omega

theorem sumInt_filter_split {α : Type} (xs : List α) (p : α → Bool) (f : α → Int) :
    sumInt (xs.filter p) f + sumInt (xs.filter (fun x => !p x)) f = sumInt xs f := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter, sumInt]
    cases p a <;> simp only [Bool.not_false, Bool.not_true, sumInt] <;> omega

theorem sumInt_filter_eq_sumInt_ite {α : Type} (xs : List α) (p : α → Bool) (f : α → Int) :
    sumInt (xs.filter p) f = sumInt xs (fun x => if p x = true then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter, sumInt]
    cases hp : p a <;> simp [sumInt, ih]

theorem sumInt_single_hit {α : Type} [DecidableEq α] {xs : List α} (hnd : NoDup xs)
    {a : α} (ha : a ∈ xs) (f : α → Int) :
    sumInt xs (fun x => if x = a then f x else 0) = f a := by
  induction hnd with
  | nil => cases ha
  | @cons b bs hnin _ ih =>
    simp only [sumInt]
    by_cases hba : b = a
    · subst hba
      simp only [ite_true]
      have hz : sumInt bs (fun x => if x = b then f x else 0) = 0 := by
        apply sumInt_eq_zero
        intro x hx
        have hne : x ≠ b := fun h => hnin (h ▸ hx)
        simp [hne]
      omega
    · simp only [hba, ite_false]
      rcases List.mem_cons.mp ha with rfl | hbs
      · exact absurd rfl hba
      · rw [ih hbs]; omega

theorem sumNat_single_hit {α : Type} [DecidableEq α] {xs : List α} (hnd : NoDup xs)
    {a : α} (ha : a ∈ xs) (f : α → Nat) :
    sumNat xs (fun x => if x = a then f x else 0) = f a := by
  induction hnd with
  | nil => cases ha
  | @cons b bs hnin _ ih =>
    simp only [sumNat]
    by_cases hba : b = a
    · subst hba
      simp only [ite_true]
      have hz : sumNat bs (fun x => if x = b then f x else 0) = 0 := by
        apply sumNat_eq_zero
        intro x hx
        have hne : x ≠ b := fun h => hnin (h ▸ hx)
        simp [hne]
      omega
    · simp only [hba, ite_false]
      rcases List.mem_cons.mp ha with rfl | hbs
      · exact absurd rfl hba
      · rw [ih hbs]; omega

theorem sumInt_double_swap {α β : Type} (xs : List α) (ys : List β) (g : α → β → Int) :
    sumInt xs (fun x => sumInt ys (fun y => g x y)) =
    sumInt ys (fun y => sumInt xs (fun x => g x y)) := by
  induction xs with
  | nil =>
    simp only [sumInt]
    exact (sumInt_eq_zero (fun _ _ => rfl)).symm
  | cons a as ih =>
    simp only [sumInt, ih]
    rw [← sumInt_add]

theorem sumNat_double_swap {α β : Type} (xs : List α) (ys : List β) (g : α → β → Nat) :
    sumNat xs (fun x => sumNat ys (fun y => g x y)) =
    sumNat ys (fun y => sumNat xs (fun x => g x y)) := by
  induction xs with
  | nil =>
    simp only [sumNat]
    exact (sumNat_eq_zero (fun _ _ => rfl)).symm
  | cons a as ih =>
    simp only [sumNat, ih]
    rw [← sumNat_add]

theorem mem_sumNat_le {α : Type} {a : α} {B : List α} (ha : a ∈ B) (f : α → Nat) :
    f a ≤ sumNat B f := by
  induction B with
  | nil => cases ha
  | cons b bs ih =>
    simp only [sumNat]
    rcases List.mem_cons.mp ha with rfl | hbs
    · omega
    · have h := ih hbs; omega

theorem sumNat_subset_le {α : Type} [DecidableEq α] {A B : List α}
    (hnd : NoDup A) (hsub : ∀ x ∈ A, x ∈ B) (f : α → Nat) :
    sumNat A f ≤ sumNat B f := by
  induction hnd generalizing B with
  | nil => exact Nat.zero_le _
  | @cons a as hnin _ ih =>
    have haB : a ∈ B := hsub a List.mem_cons_self
    have split := sumNat_filter_split B (fun x => decide (x = a)) f
    have ha_filt : a ∈ B.filter (fun x => decide (x = a)) := by
      rw [mem_filter_iff_prop]
      exact ⟨haB, decide_eq_true rfl⟩
    have hge_a : f a ≤ sumNat (B.filter (fun x => decide (x = a))) f :=
      mem_sumNat_le ha_filt f
    have hsub' : ∀ x ∈ as, x ∈ B.filter (fun x => !decide (x = a)) := by
      intro x hx
      rw [mem_filter_iff_prop]
      refine ⟨hsub x (List.mem_cons_of_mem a hx), ?_⟩
      have hne : x ≠ a := fun h => hnin (h ▸ hx)
      simp [hne]
    have hle_rest := ih hsub'
    simp only [sumNat]
    omega

theorem length_eq_sumNat_ones {α : Type} (xs : List α) :
    xs.length = sumNat xs (fun _ => 1) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [sumNat, ih]; omega

theorem filter_filter_eq {α : Type} (xs : List α) (p q r : α → Bool)
    (h : ∀ x ∈ xs, (p x && q x) = r x) :
    (xs.filter p).filter q = xs.filter r := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases hp : p a <;> cases hq : q a <;> simp_all [List.filter]

theorem filter_eq_nil_of_false {α : Type} (xs : List α) (p : α → Bool)
    (h : ∀ x ∈ xs, p x = false) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter, h a List.mem_cons_self]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ## 2. Exact Positive-Denominator Rational Arithmetic (`QRat`) -/

/-- Exact rational `num / den` with `0 < den`. -/
structure QRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq

namespace QRat

def zero : QRat := ⟨0, 1, Nat.zero_lt_one⟩
def one : QRat := ⟨1, 1, Nat.zero_lt_one⟩

def mkNat (n d : Nat) (hd : 0 < d) : QRat := ⟨(n : Int), d, hd⟩

def add (p q : QRat) : QRat :=
  ⟨p.num * (q.den : Int) + q.num * (p.den : Int),
   p.den * q.den,
   Nat.mul_pos p.den_pos q.den_pos⟩

def le (p q : QRat) : Prop :=
  p.num * (q.den : Int) ≤ q.num * (p.den : Int)

def lt (p q : QRat) : Prop :=
  p.num * (q.den : Int) < q.num * (p.den : Int)

def eqv (p q : QRat) : Prop :=
  p.num * (q.den : Int) = q.num * (p.den : Int)

instance (p q : QRat) : Decidable (le p q) := inferInstanceAs (Decidable (_ ≤ _))
instance (p q : QRat) : Decidable (lt p q) := inferInstanceAs (Decidable (_ < _))
instance (p q : QRat) : Decidable (eqv p q) := inferInstanceAs (Decidable (_ = _))

def sumList {α : Type} (xs : List α) (w : α → QRat) : QRat :=
  match xs with
  | [] => zero
  | x :: rest => add (w x) (sumList rest w)

theorem eqv_refl (p : QRat) : eqv p p := rfl

theorem le_of_eqv_left {p₁ p₂ q : QRat} (he : eqv p₁ p₂) (hl : le p₂ q) : le p₁ q := by
  unfold eqv at he
  unfold le at hl ⊢
  have hd2 : (0 : Int) < (p₂.den : Int) := Int.ofNat_lt.mpr p₂.den_pos
  have h1 : p₁.num * (p₂.den : Int) * (q.den : Int) = p₂.num * (p₁.den : Int) * (q.den : Int) := by
    rw [he]
  have h2 : p₂.num * (q.den : Int) * (p₁.den : Int) ≤ q.num * (p₂.den : Int) * (p₁.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hl (Int.ofNat_le.mpr (Nat.zero_le _))
  have h3 : p₂.num * (p₁.den : Int) * (q.den : Int) = p₂.num * (q.den : Int) * (p₁.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (p₁.den : Int) (q.den : Int), ← Int.mul_assoc]
  have h4 : q.num * (p₂.den : Int) * (p₁.den : Int) = q.num * (p₁.den : Int) * (p₂.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (p₂.den : Int) (p₁.den : Int), ← Int.mul_assoc]
  have h5 : (p₁.num * (q.den : Int)) * (p₂.den : Int) ≤ (q.num * (p₁.den : Int)) * (p₂.den : Int) := by
    have h1' : p₁.num * (q.den : Int) * (p₂.den : Int) = p₁.num * (p₂.den : Int) * (q.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (q.den : Int) (p₂.den : Int), ← Int.mul_assoc]
    omega
  exact Int.le_of_mul_le_mul_right h5 hd2

theorem sumList_const_den {α : Type} (xs : List α) (f : α → Nat) (D : Nat) (hD : 0 < D) :
    eqv (sumList xs (fun x => mkNat (f x) D hD)) (mkNat (sumNat xs f) D hD) := by
  induction xs with
  | nil =>
    simp [sumList, zero, mkNat, sumNat, eqv]
  | cons a as ih =>
    unfold eqv at ih ⊢
    simp only [sumList, add, mkNat, sumNat] at ih ⊢
    let S := sumList as (fun x => mkNat (f x) D hD)
    have hS : S.num * (D : Int) = (sumNat as f : Int) * (S.den : Int) := ih
    calc
      ((f a : Int) * (S.den : Int) + S.num * (D : Int)) * (D : Int)
          = (f a : Int) * (S.den : Int) * (D : Int) + (S.num * (D : Int)) * (D : Int) := by
            rw [Int.add_mul]
      _ = (f a : Int) * (S.den : Int) * (D : Int) + ((sumNat as f : Int) * (S.den : Int)) * (D : Int) := by
            rw [hS]
      _ = ((f a : Int) + (sumNat as f : Int)) * ((D : Int) * (S.den : Int)) := by
            rw [Int.add_mul]
            have t1 : (f a : Int) * (S.den : Int) * (D : Int) = (f a : Int) * ((D : Int) * (S.den : Int)) := by
              rw [Int.mul_assoc, Int.mul_comm (S.den : Int) (D : Int)]
            have t2 : (sumNat as f : Int) * (S.den : Int) * (D : Int) =
                (sumNat as f : Int) * ((D : Int) * (S.den : Int)) := by
              rw [Int.mul_assoc, Int.mul_comm (S.den : Int) (D : Int)]
            rw [t1, t2]
      _ = ((f a + sumNat as f : Nat) : Int) * ((D * S.den : Nat) : Int) := by
            simp [Int.ofNat_add, Int.ofNat_mul]

end QRat

/-! ## 3. Finite Geometric Lattices and Poset Concepts -/

/--
A finite geometric lattice `(L, ≤, ⊥, ⊤, ∧, ∨, rk)` on a decidable finite type `α`:
a finite bounded lattice that is graded by `rk`, upper semimodular, and atomistic
(every element is the join of the rank-1 atoms below it).
-/
structure GeometricLattice (α : Type) [DecidableEq α] where
  elems : List α
  nodup_elems : NoDup elems
  mem_elems : ∀ x : α, x ∈ elems
  leb : α → α → Bool
  bot : α
  top : α
  meet : α → α → α
  join : α → α → α
  rk : α → Nat
  le_refl : ∀ x, leb x x = true
  le_trans : ∀ {x y z}, leb x y = true → leb y z = true → leb x z = true
  le_antisymm : ∀ {x y}, leb x y = true → leb y x = true → x = y
  bot_le : ∀ x, leb bot x = true
  le_top : ∀ x, leb x top = true
  meet_le_left : ∀ x y, leb (meet x y) x = true
  meet_le_right : ∀ x y, leb (meet x y) y = true
  le_meet : ∀ {z x y}, leb z x = true → leb z y = true → leb z (meet x y) = true
  le_join_left : ∀ x y, leb x (join x y) = true
  le_join_right : ∀ x y, leb y (join x y) = true
  join_le : ∀ {x y z}, leb x z = true → leb y z = true → leb (join x y) z = true
  rk_bot : rk bot = 0
  lt_rk : ∀ {x y}, leb x y = true → x ≠ y → rk x < rk y
  exists_step : ∀ {x y}, leb x y = true → rk x + 1 < rk y →
    ∃ z, leb x z = true ∧ z ≠ x ∧ leb z y = true ∧ rk z = rk x + 1
  semimodular : ∀ x y, rk (meet x y) + rk (join x y) ≤ rk x + rk y
  atomistic : ∀ {x y}, (∀ a, rk a = 1 → leb a x = true → leb a y = true) → leb x y = true

namespace GeometricLattice

/-- Partial order proposition `x ≤ y`. -/
def le {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Prop :=
  L.leb x y = true

instance instDecidableLe {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) :
    Decidable (L.le x y) :=
  inferInstanceAs (Decidable (L.leb x y = true))

/-- Strict order `x < y` in `L`. -/
def Lt {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Prop :=
  L.le x y ∧ x ≠ y

/-- Covering relation `x ⋖ y`: `x < y` and there is no `z` with `x < z < y`. -/
def Covers {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Prop :=
  L.Lt x y ∧ ∀ z, L.Lt x z → L.le z y → z = y

/-- Jordan–Dedekind cover equivalence: `x ⋖ y ↔ x < y ∧ rk y = rk x + 1`. -/
theorem covers_iff_rk {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) :
    L.Covers x y ↔ L.Lt x y ∧ L.rk y = L.rk x + 1 := by
  constructor
  · rintro ⟨hlt, hmin⟩
    refine ⟨hlt, ?_⟩
    have hrk : L.rk x < L.rk y := L.lt_rk hlt.1 hlt.2
    exact Classical.byContradiction fun hne => by
      have hgt : L.rk x + 1 < L.rk y := by omega
      rcases L.exists_step hlt.1 hgt with ⟨z, hxz, hzx, hzy, hrz⟩
      have hzy_eq : z = y := hmin z ⟨hxz, Ne.symm hzx⟩ hzy
      subst hzy_eq
      omega
  · rintro ⟨hlt, hrk⟩
    refine ⟨hlt, ?_⟩
    intro z hxz hzy
    by_cases hzy_eq : z = y
    · exact hzy_eq
    · have h1 : L.rk x < L.rk z := L.lt_rk hxz.1 hxz.2
      have h2 : L.rk z < L.rk y := L.lt_rk hzy hzy_eq
      omega

/-- Join of a list of elements in `L`. -/
def joinList {α : Type} [DecidableEq α] (L : GeometricLattice α) : List α → α
  | [] => L.bot
  | x :: xs => L.join x (L.joinList xs)

theorem le_joinList_of_mem {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x : α} {xs : List α} (hx : x ∈ xs) :
    L.le x (L.joinList xs) := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    simp only [joinList]
    rcases List.mem_cons.mp hx with rfl | has
    · exact L.le_join_left x (L.joinList as)
    · exact L.le_trans (ih has) (L.le_join_right a (L.joinList as))

theorem joinList_le {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {xs : List α} {z : α} (h : ∀ x ∈ xs, L.le x z) :
    L.le (L.joinList xs) z := by
  induction xs with
  | nil => exact L.bot_le z
  | cons a as ih =>
    simp only [joinList]
    exact L.join_le (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- Every element of a geometric lattice equals the join of the rank-1 atoms below it. -/
def atomsBelow {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) : List α :=
  L.elems.filter (fun a => decide (L.rk a = 1) && L.leb a x)

theorem join_atomsBelow_eq {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) :
    L.joinList (L.atomsBelow x) = x := by
  apply L.le_antisymm
  · apply L.joinList_le
    intro a ha
    unfold atomsBelow at ha
    have hp := (mem_filter_iff_prop _ _ _).mp ha
    exact (Bool.and_eq_true _ _).mp hp.2 |>.2
  · apply L.atomistic
    intro a hrk hax
    apply L.le_joinList_of_mem
    unfold atomsBelow
    rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems a, Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hrk, hax⟩⟩

/-- Antichain predicate on a list of elements: duplicate-free and pairwise incomparable. -/
def IsAntichain {α : Type} [DecidableEq α] (L : GeometricLattice α) (A : List α) : Prop :=
  NoDup A ∧ ∀ x ∈ A, ∀ y ∈ A, L.le x y → x = y

instance instDecidableIsAntichain {α : Type} [DecidableEq α]
    (L : GeometricLattice α) (A : List α) : Decidable (L.IsAntichain A) := by
  unfold IsAntichain
  exact inferInstance

/-- Elements of rank `k` in `L`. -/
def rankLevel {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : List α :=
  L.elems.filter (fun x => decide (L.rk x = k))

/-- Whitney number of the second kind `W_k = |{x ∈ L : rk x = k}|`. -/
def whitney2 {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  (L.rankLevel k).length

theorem rankLevel_isAntichain {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) :
    L.IsAntichain (L.rankLevel k) := by
  refine ⟨nodup_filter _ L.nodup_elems, ?_⟩
  intro x hx y hy hxy
  by_cases heq : x = y
  · exact heq
  · unfold rankLevel at hx hy
    have hkx : L.rk x = k := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hx).2
    have hky : L.rk y = k := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hy).2
    have hlt : L.rk x < L.rk y := L.lt_rk hxy heq
    omega

/-! ## 4. Incidence-Algebra Möbius Function `μ(x, y)` -/

/-- Closed order interval `[x, y] = {z ∈ L : x ≤ z ∧ z ≤ y}`. -/
def interval {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : List α :=
  L.elems.filter (fun z => L.leb x z && L.leb z y)

/-- Half-open lower interval `[x, y) = {z ∈ L : x ≤ z ∧ z ≤ y ∧ z ≠ y}`. -/
def intervalLt {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : List α :=
  L.elems.filter (fun z => L.leb x z && L.leb z y && !decide (z = y))

/-- Half-open upper interval `(x, y] = {z ∈ L : x ≤ z ∧ z ≤ y ∧ z ≠ x}`. -/
def intervalGt {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : List α :=
  L.elems.filter (fun z => L.leb x z && L.leb z y && !decide (z = x))

/-- Fuel-indexed recursion for `μ(x, y)` along `rk y - rk x`. -/
def mobiusAux {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat → α → α → Int
  | 0, x, y => if x = y then 1 else 0
  | d + 1, x, y =>
    if !L.leb x y then 0
    else if x = y then 1
    else - sumInt (L.intervalLt x y) (fun z => L.mobiusAux d x z)

theorem mobiusAux_irrel {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (d₁ d₂ : Nat) (x y : α),
      (L.leb x y = true → L.rk y - L.rk x ≤ d₁) →
      (L.leb x y = true → L.rk y - L.rk x ≤ d₂) →
      L.mobiusAux d₁ x y = L.mobiusAux d₂ x y
  | 0, 0, _, _, _, _ => rfl
  | 0, d₂ + 1, x, y, h1, _ => by
    simp only [mobiusAux]
    cases hleb : L.leb x y
    · have hne : x ≠ y := fun h => by subst h; rw [L.le_refl x] at hleb; contradiction
      simp [hne]
    · by_cases heq : x = y
      · simp [heq]
      · have hrk := L.lt_rk hleb heq
        have hd1 := h1 hleb
        omega
  | d₁ + 1, 0, x, y, _, h2 => by
    simp only [mobiusAux]
    cases hleb : L.leb x y
    · have hne : x ≠ y := fun h => by subst h; rw [L.le_refl x] at hleb; contradiction
      simp [hne]
    · by_cases heq : x = y
      · simp [heq]
      · have hrk := L.lt_rk hleb heq
        have hd2 := h2 hleb
        omega
  | d₁ + 1, d₂ + 1, x, y, h1, h2 => by
    simp only [mobiusAux]
    cases hleb : L.leb x y
    · rfl
    · by_cases heq : x = y
      · simp [heq]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, heq]
        congr 1
        apply sumInt_congr
        intro z hz
        unfold intervalLt at hz
        have hp := ((mem_filter_iff_prop _ _ _).mp hz).2
        rcases (Bool.and_eq_true _ _).mp hp with ⟨hp12, hzne_b⟩
        rcases (Bool.and_eq_true _ _).mp hp12 with ⟨_, hzy⟩
        have hzne : z ≠ y := by intro h; subst h; simp at hzne_b
        have hzy_lt : L.rk z < L.rk y := L.lt_rk hzy hzne
        have hd1 := h1 hleb
        have hd2 := h2 hleb
        exact L.mobiusAux_irrel d₁ d₂ x z (fun _ => by omega) (fun _ => by omega)

/-- The exact incidence-algebra Möbius function `μ(x, y)` of `L`. -/
def mobius {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Int :=
  L.mobiusAux (L.rk y - L.rk x) x y

theorem mobius_of_not_le {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (h : ¬ L.le x y) : L.mobius x y = 0 := by
  unfold le at h
  have hleb : L.leb x y = false := Bool.eq_false_iff.mpr h
  unfold mobius
  rw [L.mobiusAux_irrel (L.rk y - L.rk x) 1 x y
    (fun ht => by rw [hleb] at ht; contradiction)
    (fun ht => by rw [hleb] at ht; contradiction)]
  simp [mobiusAux, hleb]

theorem mobius_self {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) :
    L.mobius x x = 1 := by
  unfold mobius
  simp [Nat.sub_self, mobiusAux]

theorem mobius_of_lt {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) (hne : x ≠ y) :
    L.mobius x y = - sumInt (L.intervalLt x y) (fun z => L.mobius x z) := by
  have hrk : L.rk x < L.rk y := L.lt_rk hle hne
  unfold mobius
  rw [L.mobiusAux_irrel (L.rk y - L.rk x) ((L.rk y - L.rk x - 1) + 1) x y
    (fun _ => Nat.le_refl _) (fun _ => by omega)]
  unfold le at hle
  simp only [mobiusAux, hle, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne]
  congr 1
  apply sumInt_congr
  intro z hz
  unfold intervalLt at hz
  have hp := ((mem_filter_iff_prop _ _ _).mp hz).2
  rcases (Bool.and_eq_true _ _).mp hp with ⟨hp12, hzne_b⟩
  rcases (Bool.and_eq_true _ _).mp hp12 with ⟨_, hzy⟩
  have hzne : z ≠ y := by intro h; subst h; simp at hzne_b
  have hzy_lt : L.rk z < L.rk y := L.lt_rk hzy hzne
  exact L.mobiusAux_irrel (L.rk y - L.rk x - 1) (L.rk z - L.rk x) x z
    (fun _ => by omega) (fun _ => Nat.le_refl _)

/-- Left incidence-algebra inversion law: `∑_{x ≤ z ≤ y} μ(x, z) = δ_{x, y}`. -/
theorem mobius_sum_left {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) :
    sumInt (L.interval x y) (fun z => L.mobius x z) = if x = y then 1 else 0 := by
  have hsplit := sumInt_filter_split (L.interval x y) (fun z => decide (z = y)) (fun z => L.mobius x z)
  have hhit : sumInt ((L.interval x y).filter (fun z => decide (z = y))) (fun z => L.mobius x z) =
      L.mobius x y := by
    rw [sumInt_filter_eq_sumInt_ite]
    have hy_mem : y ∈ L.interval x y := by
      unfold interval; rw [mem_filter_iff_prop]
      exact ⟨L.mem_elems y, Bool.and_eq_true _ _ |>.mpr ⟨hle, L.le_refl y⟩⟩
    have hc : sumInt (L.interval x y) (fun z => if decide (z = y) = true then L.mobius x z else 0) =
        sumInt (L.interval x y) (fun z => if z = y then L.mobius x z else 0) := by
      apply sumInt_congr; intro z _; by_cases hzy : z = y <;> simp [hzy]
    rw [hc]
    exact sumInt_single_hit (nodup_filter _ L.nodup_elems) hy_mem (fun z => L.mobius x z)
  have hrest : (L.interval x y).filter (fun z => !decide (z = y)) = L.intervalLt x y := by
    unfold interval intervalLt
    exact filter_filter_eq L.elems _ _ _ (fun _ _ => rfl)
  rw [hhit, hrest] at hsplit
  by_cases heq : x = y
  · subst heq
    have hempty : L.intervalLt x x = [] := by
      unfold intervalLt
      apply filter_eq_nil_of_false
      intro z _
      cases h1 : L.leb x z <;> cases h2 : L.leb z x
      · simp
      · simp
      · simp
      · have hz_eq : z = x := L.le_antisymm h2 h1
        simp [hz_eq]
    rw [hempty] at hsplit
    simp only [sumInt, Int.add_zero] at hsplit
    rw [← hsplit, L.mobius_self x]
    simp
  · simp only [heq, ↓reduceIte]
    rw [← hsplit, L.mobius_of_lt hle heq]
    omega

/-- Dual fuel-indexed recursion from the top down, used to prove the right inversion law. -/
def mobiusRightAux {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat → α → α → Int
  | 0, x, y => if x = y then 1 else 0
  | d + 1, x, y =>
    if !L.leb x y then 0
    else if x = y then 1
    else - sumInt (L.intervalGt x y) (fun z => L.mobiusRightAux d z y)

theorem mobiusRightAux_irrel {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (d₁ d₂ : Nat) (x y : α),
      (L.leb x y = true → L.rk y - L.rk x ≤ d₁) →
      (L.leb x y = true → L.rk y - L.rk x ≤ d₂) →
      L.mobiusRightAux d₁ x y = L.mobiusRightAux d₂ x y
  | 0, 0, _, _, _, _ => rfl
  | 0, d₂ + 1, x, y, h1, _ => by
    simp only [mobiusRightAux]
    cases hleb : L.leb x y
    · have hne : x ≠ y := fun h => by subst h; rw [L.le_refl x] at hleb; contradiction
      simp [hne]
    · by_cases heq : x = y
      · simp [heq]
      · have hrk := L.lt_rk hleb heq; have hd1 := h1 hleb; omega
  | d₁ + 1, 0, x, y, _, h2 => by
    simp only [mobiusRightAux]
    cases hleb : L.leb x y
    · have hne : x ≠ y := fun h => by subst h; rw [L.le_refl x] at hleb; contradiction
      simp [hne]
    · by_cases heq : x = y
      · simp [heq]
      · have hrk := L.lt_rk hleb heq; have hd2 := h2 hleb; omega
  | d₁ + 1, d₂ + 1, x, y, h1, h2 => by
    simp only [mobiusRightAux]
    cases hleb : L.leb x y
    · rfl
    · by_cases heq : x = y
      · simp [heq]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, heq]
        congr 1
        apply sumInt_congr
        intro z hz
        unfold intervalGt at hz
        have hp := ((mem_filter_iff_prop _ _ _).mp hz).2
        rcases (Bool.and_eq_true _ _).mp hp with ⟨hp12, hzx_b⟩
        rcases (Bool.and_eq_true _ _).mp hp12 with ⟨hxz, _⟩
        have hzx : x ≠ z := by intro h; subst h; simp at hzx_b
        have hxz_lt : L.rk x < L.rk z := L.lt_rk hxz hzx
        have hd1 := h1 hleb; have hd2 := h2 hleb
        exact L.mobiusRightAux_irrel d₁ d₂ z y (fun _ => by omega) (fun _ => by omega)

def mobiusRight {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Int :=
  L.mobiusRightAux (L.rk y - L.rk x) x y

theorem mobiusRight_of_not_le {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (h : ¬ L.le x y) : L.mobiusRight x y = 0 := by
  unfold le at h
  have hleb : L.leb x y = false := Bool.eq_false_iff.mpr h
  unfold mobiusRight
  rw [L.mobiusRightAux_irrel (L.rk y - L.rk x) 1 x y
    (fun ht => by rw [hleb] at ht; contradiction)
    (fun ht => by rw [hleb] at ht; contradiction)]
  simp [mobiusRightAux, hleb]

theorem mobiusRight_self {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) :
    L.mobiusRight x x = 1 := by
  unfold mobiusRight
  simp [Nat.sub_self, mobiusRightAux]

theorem mobiusRight_of_lt {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) (hne : x ≠ y) :
    L.mobiusRight x y = - sumInt (L.intervalGt x y) (fun z => L.mobiusRight z y) := by
  have hrk : L.rk x < L.rk y := L.lt_rk hle hne
  unfold mobiusRight
  rw [L.mobiusRightAux_irrel (L.rk y - L.rk x) ((L.rk y - L.rk x - 1) + 1) x y
    (fun _ => Nat.le_refl _) (fun _ => by omega)]
  unfold le at hle
  simp only [mobiusRightAux, hle, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne]
  congr 1
  apply sumInt_congr
  intro z hz
  unfold intervalGt at hz
  have hp := ((mem_filter_iff_prop _ _ _).mp hz).2
  rcases (Bool.and_eq_true _ _).mp hp with ⟨hp12, hzx_b⟩
  rcases (Bool.and_eq_true _ _).mp hp12 with ⟨hxz, _⟩
  have hzx : x ≠ z := by intro h; subst h; simp at hzx_b
  have hxz_lt : L.rk x < L.rk z := L.lt_rk hxz hzx
  exact L.mobiusRightAux_irrel (L.rk y - L.rk x - 1) (L.rk y - L.rk z) z y
    (fun _ => by omega) (fun _ => Nat.le_refl _)

theorem mobiusRight_sum {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) :
    sumInt (L.interval x y) (fun z => L.mobiusRight z y) = if x = y then 1 else 0 := by
  have hsplit := sumInt_filter_split (L.interval x y) (fun z => decide (z = x))
    (fun z => L.mobiusRight z y)
  have hhit : sumInt ((L.interval x y).filter (fun z => decide (z = x)))
      (fun z => L.mobiusRight z y) = L.mobiusRight x y := by
    rw [sumInt_filter_eq_sumInt_ite]
    have hx_mem : x ∈ L.interval x y := by
      unfold interval; rw [mem_filter_iff_prop]
      exact ⟨L.mem_elems x, Bool.and_eq_true _ _ |>.mpr ⟨L.le_refl x, hle⟩⟩
    have hc : sumInt (L.interval x y)
        (fun z => if decide (z = x) = true then L.mobiusRight z y else 0) =
        sumInt (L.interval x y) (fun z => if z = x then L.mobiusRight z y else 0) := by
      apply sumInt_congr; intro z _; by_cases hzx : z = x <;> simp [hzx]
    rw [hc]
    exact sumInt_single_hit (nodup_filter _ L.nodup_elems) hx_mem (fun z => L.mobiusRight z y)
  have hrest : (L.interval x y).filter (fun z => !decide (z = x)) = L.intervalGt x y := by
    unfold interval intervalGt
    exact filter_filter_eq L.elems _ _ _ (fun _ _ => rfl)
  rw [hhit, hrest] at hsplit
  by_cases heq : x = y
  · subst heq
    have hempty : L.intervalGt x x = [] := by
      unfold intervalGt
      apply filter_eq_nil_of_false
      intro z _
      cases h1 : L.leb x z <;> cases h2 : L.leb z x
      · simp
      · simp
      · simp
      · have hz_eq : z = x := L.le_antisymm h2 h1
        simp [hz_eq]
    rw [hempty] at hsplit
    simp only [sumInt, Int.add_zero] at hsplit
    rw [← hsplit, L.mobiusRight_self x]
    simp
  · simp only [heq, ↓reduceIte]
    rw [← hsplit, L.mobiusRight_of_lt hle heq]
    omega

/-- Incidence-algebra associativity proves `mobius = mobiusRight`. -/
theorem mobius_eq_mobiusRight {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) :
    L.mobius x y = L.mobiusRight x y := by
  by_cases hxy : L.le x y
  · have lhs_id : L.mobius x y =
        sumInt L.elems (fun z =>
          L.mobius x z * sumInt L.elems (fun w =>
            if L.le x z ∧ L.le z w ∧ L.le w y then L.mobiusRight w y else 0)) := by
      have hcongr : sumInt L.elems (fun z =>
          L.mobius x z * sumInt L.elems (fun w =>
            if L.le x z ∧ L.le z w ∧ L.le w y then L.mobiusRight w y else 0)) =
          sumInt L.elems (fun z => if z = y then L.mobius x z else 0) := by
        apply sumInt_congr
        intro z _
        by_cases hxz : L.le x z
        · by_cases hzy : L.le z y
          · have hsub : sumInt L.elems (fun w =>
                if L.le x z ∧ L.le z w ∧ L.le w y then L.mobiusRight w y else 0) =
                sumInt (L.interval z y) (fun w => L.mobiusRight w y) := by
              unfold interval
              rw [sumInt_filter_eq_sumInt_ite]
              apply sumInt_congr
              intro w _
              by_cases hw : L.le z w ∧ L.le w y
              · have hwb : (L.leb z w && L.leb w y) = true :=
                  Bool.and_eq_true _ _ |>.mpr hw
                simp [hxz, hw, hwb]
              · have hwb : (L.leb z w && L.leb w y) = false :=
                  Bool.eq_false_iff.mpr (fun ht => hw ((Bool.and_eq_true _ _).mp ht))
                have hw' : ¬ (L.le x z ∧ L.le z w ∧ L.le w y) := fun hh => hw ⟨hh.2.1, hh.2.2⟩
                simp [hw', hwb]
            rw [hsub, L.mobiusRight_sum hzy]
            by_cases hzy_eq : z = y <;> simp [hzy_eq]
          · have hne : z ≠ y := fun h => hzy (h ▸ L.le_refl z)
            have hz0 : sumInt L.elems (fun w =>
                if L.le x z ∧ L.le z w ∧ L.le w y then L.mobiusRight w y else 0) = 0 := by
              apply sumInt_eq_zero
              intro w _
              have hn : ¬ (L.le x z ∧ L.le z w ∧ L.le w y) :=
                fun hh => hzy (L.le_trans hh.2.1 hh.2.2)
              simp [hn]
            simp [hne, hz0]
        · have hmu0 : L.mobius x z = 0 := L.mobius_of_not_le hxz
          have hne : z ≠ y := fun h => hxz (h ▸ hxy)
          simp [hmu0, hne]
      rw [hcongr, sumInt_single_hit L.nodup_elems (L.mem_elems y)]
    have rhs_id : L.mobiusRight x y =
        sumInt L.elems (fun w =>
          (sumInt L.elems (fun z =>
            if L.le x z ∧ L.le z w ∧ L.le w y then L.mobius x z else 0)) * L.mobiusRight w y) := by
      have hcongr : sumInt L.elems (fun w =>
          (sumInt L.elems (fun z =>
            if L.le x z ∧ L.le z w ∧ L.le w y then L.mobius x z else 0)) * L.mobiusRight w y) =
          sumInt L.elems (fun w => if w = x then L.mobiusRight w y else 0) := by
        apply sumInt_congr
        intro w _
        by_cases hxw : L.le x w
        · by_cases hwy : L.le w y
          · have hsub : sumInt L.elems (fun z =>
                if L.le x z ∧ L.le z w ∧ L.le w y then L.mobius x z else 0) =
                sumInt (L.interval x w) (fun z => L.mobius x z) := by
              unfold interval
              rw [sumInt_filter_eq_sumInt_ite]
              apply sumInt_congr
              intro z _
              by_cases hz : L.le x z ∧ L.le z w
              · have hzb : (L.leb x z && L.leb z w) = true :=
                  Bool.and_eq_true _ _ |>.mpr hz
                simp [hz, hwy, hzb]
              · have hzb : (L.leb x z && L.leb z w) = false :=
                  Bool.eq_false_iff.mpr (fun ht => hz ((Bool.and_eq_true _ _).mp ht))
                have hz' : ¬ (L.le x z ∧ L.le z w ∧ L.le w y) := fun hh => hz ⟨hh.1, hh.2.1⟩
                simp [hz', hzb]
            rw [hsub, L.mobius_sum_left hxw]
            by_cases hwx_eq : w = x
            · subst hwx_eq; simp
            · have hxw_ne : x ≠ w := Ne.symm hwx_eq
              simp [hwx_eq, hxw_ne]
          · have hmu0 : L.mobiusRight w y = 0 := L.mobiusRight_of_not_le hwy
            have hne : w ≠ x := fun h => hwy (h ▸ hxy)
            simp [hmu0, hne]
        · have hne : w ≠ x := fun h => hxw (h ▸ L.le_refl w)
          have hz0 : sumInt L.elems (fun z =>
              if L.le x z ∧ L.le z w ∧ L.le w y then L.mobius x z else 0) = 0 := by
            apply sumInt_eq_zero
            intro z _
            have hn : ¬ (L.le x z ∧ L.le z w ∧ L.le w y) :=
              fun hh => hxw (L.le_trans hh.1 hh.2.1)
            simp [hn]
          simp [hne, hz0]
      rw [hcongr, sumInt_single_hit L.nodup_elems (L.mem_elems x)]
    rw [lhs_id, rhs_id]
    have hmul : sumInt L.elems (fun z =>
        L.mobius x z * sumInt L.elems (fun w =>
          if L.le x z ∧ L.le z w ∧ L.le w y then L.mobiusRight w y else 0)) =
        sumInt L.elems (fun z => sumInt L.elems (fun w =>
          (if L.le x z ∧ L.le z w ∧ L.le w y then L.mobius x z else 0) * L.mobiusRight w y)) := by
      apply sumInt_congr
      intro z _
      rw [← sumInt_mul_left]
      apply sumInt_congr
      intro w _
      by_cases h : L.le x z ∧ L.le z w ∧ L.le w y <;> simp [h]
    rw [hmul, sumInt_double_swap]
    apply sumInt_congr
    intro w _
    rw [sumInt_mul_right]
  · rw [L.mobius_of_not_le hxy, L.mobiusRight_of_not_le hxy]

/-- Right incidence-algebra inversion law: `∑_{x ≤ z ≤ y} μ(z, y) = δ_{x, y}`. -/
theorem mobius_sum_right {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) :
    sumInt (L.interval x y) (fun z => L.mobius z y) = if x = y then 1 else 0 := by
  have hcongr : sumInt (L.interval x y) (fun z => L.mobius z y) =
      sumInt (L.interval x y) (fun z => L.mobiusRight z y) := by
    apply sumInt_congr; intro z _; exact L.mobius_eq_mobiusRight z y
  rw [hcongr]
  exact L.mobiusRight_sum hle

/-- Dual top-down unfolding for `μ(x, y)` when `x < y`. -/
theorem mobius_of_lt_upper {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) (hne : x ≠ y) :
    L.mobius x y = - sumInt (L.intervalGt x y) (fun z => L.mobius z y) := by
  rw [L.mobius_eq_mobiusRight x y, L.mobiusRight_of_lt hle hne]
  congr 1
  apply sumInt_congr; intro z _; exact (L.mobius_eq_mobiusRight z y).symm

/-- Absolute value `|μ(x, y)|` as a natural number. -/
def absMobius {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Nat :=
  (L.mobius x y).natAbs

/-- Unsigned Whitney number of the first kind `|w_k(L)| = ∑_{rk y = k} |μ(⊥, y)|`. -/
def absWhitney1 {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  sumNat (L.rankLevel k) (fun y => L.absMobius L.bot y)

/-- Upper Möbius rank sum `∑_{rk y = k} |μ(y, ⊤)|`. -/
def upperMobiusRankSum {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  sumNat (L.rankLevel k) (fun y => L.absMobius y L.top)

/-- Two-sided Möbius rank sum `∑_{rk y = k} |μ(⊥, y) · μ(y, ⊤)|`. -/
def twoSidedMobiusRankSum {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  sumNat (L.rankLevel k) (fun y => L.absMobius L.bot y * L.absMobius y L.top)

end GeometricLattice

end Conjecture00000008533
