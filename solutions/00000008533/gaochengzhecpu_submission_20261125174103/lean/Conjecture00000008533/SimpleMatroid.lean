/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization for Conjecture 00000008533:
General SimpleMatroid-to-GeometricLattice bridge theorem (`SimpleMatroid.toGeometricLattice`),
constructed over length-indexed bitvectors `Sub m` with zero external dependencies.
-/
import Conjecture00000008533.Basic
import Conjecture00000008533.LubellLYM

namespace Conjecture00000008533

/-! ## 1. Length-Indexed Subset Representation `Sub m` -/

/-- Subset of `{0, ..., m - 1}` represented as a length-`m` boolean vector. -/
inductive Sub : Nat → Type where
  | nil : Sub 0
  | cons {m : Nat} (b : Bool) (rest : Sub m) : Sub (m + 1)
  deriving DecidableEq

namespace Sub

def empty : (m : Nat) → Sub m
  | 0 => .nil
  | m + 1 => .cons false (empty m)

def univ : (m : Nat) → Sub m
  | 0 => .nil
  | m + 1 => .cons true (univ m)

def mem : {m : Nat} → Fin m → Sub m → Bool
  | _ + 1, ⟨0, _⟩, .cons b _ => b
  | _ + 1, ⟨k + 1, hk⟩, .cons _ rest => mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩ rest

def insert : {m : Nat} → Fin m → Sub m → Sub m
  | _ + 1, ⟨0, _⟩, .cons _ rest => .cons true rest
  | _ + 1, ⟨k + 1, hk⟩, .cons b rest => .cons b (insert ⟨k, Nat.lt_of_succ_lt_succ hk⟩ rest)

def singleton {m : Nat} (i : Fin m) : Sub m :=
  insert i (empty m)

def inter : {m : Nat} → Sub m → Sub m → Sub m
  | 0, .nil, .nil => .nil
  | _ + 1, .cons b₁ r₁, .cons b₂ r₂ => .cons (b₁ && b₂) (inter r₁ r₂)

def union : {m : Nat} → Sub m → Sub m → Sub m
  | 0, .nil, .nil => .nil
  | _ + 1, .cons b₁ r₁, .cons b₂ r₂ => .cons (b₁ || b₂) (union r₁ r₂)

def subset : {m : Nat} → Sub m → Sub m → Bool
  | 0, .nil, .nil => true
  | _ + 1, .cons b₁ r₁, .cons b₂ r₂ => (!b₁ || b₂) && subset r₁ r₂

def card : {m : Nat} → Sub m → Nat
  | 0, .nil => 0
  | _ + 1, .cons b r => (if b then 1 else 0) + card r

def ofBoolFn : (m : Nat) → (Fin m → Bool) → Sub m
  | 0, _ => .nil
  | m + 1, f => .cons (f ⟨0, Nat.zero_lt_succ m⟩)
      (ofBoolFn m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

def allSubs : (m : Nat) → List (Sub m)
  | 0 => [.nil]
  | m + 1 => (allSubs m).map (Sub.cons false) ++ (allSubs m).map (Sub.cons true)

/-! ### Subset Algebra Lemmas -/

theorem mem_ofBoolFn {m : Nat} (f : Fin m → Bool) (i : Fin m) :
    mem i (ofBoolFn m f) = f i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => rfl
    | succ k => exact ih (fun j => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem ext_mem : {m : Nat} → {S T : Sub m} → (∀ i : Fin m, mem i S = mem i T) → S = T
  | 0, .nil, .nil, _ => rfl
  | m + 1, .cons b₁ r₁, .cons b₂ r₂, h => by
    have h0 : b₁ = b₂ := h ⟨0, Nat.zero_lt_succ m⟩
    have hr : r₁ = r₂ := ext_mem (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    rw [h0, hr]

theorem mem_empty : {m : Nat} → (i : Fin m) → mem i (empty m) = false
  | _ + 1, ⟨0, _⟩ => rfl
  | _ + 1, ⟨k + 1, hk⟩ => mem_empty ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem mem_univ : {m : Nat} → (i : Fin m) → mem i (univ m) = true
  | _ + 1, ⟨0, _⟩ => rfl
  | _ + 1, ⟨k + 1, hk⟩ => mem_univ ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem mem_insert : {m : Nat} → (i j : Fin m) → (S : Sub m) →
    mem i (insert j S) = (decide (i = j) || mem i S)
  | _ + 1, ⟨0, _⟩, ⟨0, _⟩, .cons _ _ => by
    change true = (decide ((⟨0, _⟩ : Fin _) = ⟨0, _⟩) || _)
    simp
  | _ + 1, ⟨0, _⟩, ⟨_ + 1, _⟩, .cons b _ => by
    change b = (decide ((⟨0, _⟩ : Fin _) = ⟨_ + 1, _⟩) || b)
    simp
  | _ + 1, ⟨k + 1, hk⟩, ⟨0, _⟩, .cons _ r => by
    change mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r =
      (decide ((⟨k + 1, hk⟩ : Fin _) = ⟨0, _⟩) || mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r)
    simp
  | _ + 1, ⟨k₁ + 1, h₁⟩, ⟨k₂ + 1, h₂⟩, .cons _ r => by
    change mem ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ (insert ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩ r) =
      (decide ((⟨k₁ + 1, h₁⟩ : Fin _) = ⟨k₂ + 1, h₂⟩) || mem ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ r)
    rw [mem_insert ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩ r]
    by_cases heq : k₁ = k₂
    · subst heq; simp
    · have hne : (⟨k₁ + 1, h₁⟩ : Fin _) ≠ ⟨k₂ + 1, h₂⟩ := by intro h; cases h; exact heq rfl
      have hne' : (⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ : Fin _) ≠ ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩ := by
        intro h; cases h; exact heq rfl
      simp [hne, hne']

theorem mem_singleton {m : Nat} (i j : Fin m) :
    mem i (singleton j) = decide (i = j) := by
  unfold singleton
  rw [mem_insert, mem_empty, Bool.or_false]

theorem mem_inter : {m : Nat} → (i : Fin m) → (S T : Sub m) →
    mem i (inter S T) = (mem i S && mem i T)
  | _ + 1, ⟨0, _⟩, .cons _ _, .cons _ _ => rfl
  | _ + 1, ⟨k + 1, hk⟩, .cons _ r₁, .cons _ r₂ =>
    mem_inter ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r₁ r₂

theorem mem_union : {m : Nat} → (i : Fin m) → (S T : Sub m) →
    mem i (union S T) = (mem i S || mem i T)
  | _ + 1, ⟨0, _⟩, .cons _ _, .cons _ _ => rfl
  | _ + 1, ⟨k + 1, hk⟩, .cons _ r₁, .cons _ r₂ =>
    mem_union ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r₁ r₂

theorem subset_iff_mem : {m : Nat} → (S T : Sub m) →
    (subset S T = true ↔ ∀ i : Fin m, mem i S = true → mem i T = true)
  | 0, .nil, .nil => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | m + 1, .cons b₁ r₁, .cons b₂ r₂ => by
    simp only [subset, Bool.and_eq_true]
    constructor
    · rintro ⟨hb, hr⟩ ⟨k, hk⟩
      cases k with
      | zero =>
        change b₁ = true → b₂ = true
        intro h1; subst h1; simp at hb; exact hb
      | succ k =>
        exact (subset_iff_mem r₁ r₂).mp hr ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    · intro hall
      refine ⟨?_, (subset_iff_mem r₁ r₂).mpr (fun i => hall ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)⟩
      have h0 : b₁ = true → b₂ = true := hall ⟨0, Nat.zero_lt_succ m⟩
      cases b₁ <;> cases b₂
      · rfl
      · rfl
      · exact absurd (h0 rfl) (by decide)
      · rfl

theorem subset_refl {m : Nat} (S : Sub m) : subset S S = true :=
  (subset_iff_mem S S).mpr (fun _ h => h)

theorem subset_trans {m : Nat} {A B C : Sub m}
    (h1 : subset A B = true) (h2 : subset B C = true) : subset A C = true :=
  (subset_iff_mem A C).mpr fun i ha =>
    (subset_iff_mem B C).mp h2 i ((subset_iff_mem A B).mp h1 i ha)

theorem subset_antisymm {m : Nat} {A B : Sub m}
    (h1 : subset A B = true) (h2 : subset B A = true) : A = B := by
  apply ext_mem; intro i
  have p1 := (subset_iff_mem A B).mp h1 i
  have p2 := (subset_iff_mem B A).mp h2 i
  cases ha : mem i A <;> cases hb : mem i B
  · rfl
  · rw [hb] at p2; rw [ha] at p2; exact p2 rfl
  · rw [ha] at p1; rw [hb] at p1; exact (p1 rfl).symm
  · rfl

theorem empty_subset {m : Nat} (S : Sub m) : subset (empty m) S = true :=
  (subset_iff_mem _ _).mpr fun i h => by rw [mem_empty] at h; contradiction

theorem subset_univ {m : Nat} (S : Sub m) : subset S (univ m) = true :=
  (subset_iff_mem _ _).mpr fun i _ => mem_univ i

theorem inter_subset_left {m : Nat} (S T : Sub m) : subset (inter S T) S = true :=
  (subset_iff_mem _ _).mpr fun i h => by rw [mem_inter] at h; exact ((Bool.and_eq_true _ _).mp h).1

theorem inter_subset_right {m : Nat} (S T : Sub m) : subset (inter S T) T = true :=
  (subset_iff_mem _ _).mpr fun i h => by rw [mem_inter] at h; exact ((Bool.and_eq_true _ _).mp h).2

theorem subset_inter {m : Nat} {Z S T : Sub m}
    (h1 : subset Z S = true) (h2 : subset Z T = true) : subset Z (inter S T) = true :=
  (subset_iff_mem _ _).mpr fun i hz => by
    rw [mem_inter, Bool.and_eq_true]
    exact ⟨(subset_iff_mem _ _).mp h1 i hz, (subset_iff_mem _ _).mp h2 i hz⟩

theorem subset_union_left {m : Nat} (S T : Sub m) : subset S (union S T) = true :=
  (subset_iff_mem _ _).mpr fun i h => by rw [mem_union, h]; rfl

theorem subset_union_right {m : Nat} (S T : Sub m) : subset T (union S T) = true :=
  (subset_iff_mem _ _).mpr fun i h => by rw [mem_union, h, Bool.or_true]

theorem union_subset {m : Nat} {S T Z : Sub m}
    (h1 : subset S Z = true) (h2 : subset T Z = true) : subset (union S T) Z = true :=
  (subset_iff_mem _ _).mpr fun i hu => by
    rw [mem_union, Bool.or_eq_true] at hu
    rcases hu with hs | ht
    · exact (subset_iff_mem _ _).mp h1 i hs
    · exact (subset_iff_mem _ _).mp h2 i ht

theorem insert_eq_of_mem {m : Nat} {i : Fin m} {S : Sub m} (h : mem i S = true) :
    insert i S = S := by
  apply ext_mem; intro j
  rw [mem_insert]
  by_cases hij : j = i
  · subst hij; simp [h]
  · simp [hij]

theorem subset_insert {m : Nat} (i : Fin m) (S : Sub m) : subset S (insert i S) = true :=
  (subset_iff_mem _ _).mpr fun j hj => by rw [mem_insert, hj, Bool.or_true]

theorem exists_not_mem_of_lt {m : Nat} {S T : Sub m}
    (hsub : subset S T = true) (hne : S ≠ T) :
    ∃ i : Fin m, mem i T = true ∧ mem i S = false := by
  exact Classical.byContradiction fun hall => by
    apply hne
    apply subset_antisymm hsub
    rw [subset_iff_mem]
    intro i hiT
    cases hiS : mem i S
    · exact False.elim (hall ⟨i, hiT, hiS⟩)
    · rfl

/-! ### Cardinality and Splitting Identities (for Fast `omega` Submodularity Proofs) -/

theorem card_empty : (m : Nat) → card (empty m) = 0
  | 0 => rfl
  | m + 1 => by simp [empty, card, card_empty m]

theorem card_insert_of_not_mem : {m : Nat} → (i : Fin m) → (S : Sub m) →
    mem i S = false → card (insert i S) = card S + 1
  | _ + 1, ⟨0, _⟩, .cons b r, hm => by
    change b = false at hm; subst hm
    change 1 + card r = (0 + card r) + 1
    omega
  | _ + 1, ⟨k + 1, hk⟩, .cons b r, hm => by
    change mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r = false at hm
    change (if b then 1 else 0) + card (insert ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r) =
      ((if b then 1 else 0) + card r) + 1
    rw [card_insert_of_not_mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r hm]
    omega

theorem card_singleton {m : Nat} (i : Fin m) : card (singleton i) = 1 := by
  unfold singleton
  rw [card_insert_of_not_mem i (empty m) (mem_empty i), card_empty]

theorem card_inter_add_union : {m : Nat} → (S T : Sub m) →
    card (inter S T) + card (union S T) = card S + card T
  | 0, .nil, .nil => rfl
  | _ + 1, .cons b₁ r₁, .cons b₂ r₂ => by
    simp only [inter, union, card]
    have ih := card_inter_add_union r₁ r₂
    cases b₁ <;> cases b₂ <;> simp <;> omega

theorem card_mono : {m : Nat} → {S T : Sub m} → subset S T = true → card S ≤ card T
  | 0, .nil, .nil, _ => Nat.le_refl 0
  | _ + 1, .cons b₁ r₁, .cons b₂ r₂, h => by
    simp only [subset, Bool.and_eq_true] at h
    have ih := card_mono h.2
    simp only [card]
    cases b₁ <;> cases b₂ <;> simp_all <;> omega

theorem mem_allSubs : {m : Nat} → (S : Sub m) → S ∈ allSubs m
  | 0, .nil => List.mem_singleton.mpr rfl
  | _ + 1, .cons false r =>
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨r, mem_allSubs r, rfl⟩))
  | _ + 1, .cons true r =>
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r, mem_allSubs r, rfl⟩))

theorem nodup_map_sub_cons {m : Nat} (b : Bool) {xs : List (Sub m)} (hnd : NoDup xs) :
    NoDup (xs.map (Sub.cons b)) := by
  induction hnd with
  | nil => exact NoDup.nil
  | cons hnin _ ih =>
    simp only [List.map]
    refine NoDup.cons ?_ ih
    intro hm
    rcases List.mem_map.mp hm with ⟨_, hx, heq⟩
    cases heq
    exact hnin hx

theorem nodup_allSubs : (m : Nat) → NoDup (allSubs m)
  | 0 => NoDup.cons (by simp) NoDup.nil
  | m + 1 => by
    simp only [allSubs]
    have ih := nodup_allSubs m
    exact GeometricLattice.nodup_append_of_disjoint
      (nodup_map_sub_cons false ih)
      (nodup_map_sub_cons true ih)
      (fun z h1 h2 => by
        rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
        rcases List.mem_map.mp h2 with ⟨_, _, heq⟩
        cases heq)

end Sub

/-! ## 2. Simple Matroids and the Bridge Theorem to `GeometricLattice` -/

/--
A finite simple matroid on `{0, ..., m - 1}`, specified by its rank function `r : Sub m → Nat`
satisfying the standard matroid rank axioms plus simplicity (`r(∅) = 0`, `r({i}) = 1`, `r({i,j}) = 2`).
-/
structure SimpleMatroid (m : Nat) where
  r : Sub m → Nat
  r_empty : r (Sub.empty m) = 0
  r_singleton : ∀ i : Fin m, r (Sub.singleton i) = 1
  r_pair : ∀ i j : Fin m, i ≠ j → r (Sub.insert i (Sub.singleton j)) = 2
  r_insert_bounds : ∀ (S : Sub m) (i : Fin m), r S ≤ r (Sub.insert i S) ∧ r (Sub.insert i S) ≤ r S + 1
  r_submod : ∀ S T : Sub m, r (Sub.inter S T) + r (Sub.union S T) ≤ r S + r T

namespace SimpleMatroid

variable {m : Nat} (M : SimpleMatroid m)

/-- Monotonicity of matroid rank: `S ⊆ T → r S ≤ r T`. -/
theorem r_mono {S T : Sub m} (h : Sub.subset S T = true) : M.r S ≤ M.r T := by
  suffices ∀ k : Nat, ∀ A : Sub m, Sub.subset A T = true → Sub.card T - Sub.card A ≤ k → M.r A ≤ M.r T by
    exact this (Sub.card T - Sub.card S) S h (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro A hAT hdiff
    by_cases heq : A = T
    · subst heq; exact Nat.le_refl _
    · rcases Sub.exists_not_mem_of_lt hAT heq with ⟨i, hiT, hiA⟩
      have hins_sub : Sub.subset (Sub.insert i A) T = true := by
        rw [Sub.subset_iff_mem]; intro j hj
        rw [Sub.mem_insert, Bool.or_eq_true] at hj
        rcases hj with hj_eq | hjA
        · rw [of_decide_eq_true hj_eq]; exact hiT
        · exact (Sub.subset_iff_mem A T).mp hAT j hjA
      have hc1 := Sub.card_insert_of_not_mem i A hiA
      have hc2 := Sub.card_mono hins_sub
      omega
  | succ k ih =>
    intro A hAT hdiff
    by_cases heq : A = T
    · subst heq; exact Nat.le_refl _
    · rcases Sub.exists_not_mem_of_lt hAT heq with ⟨i, hiT, hiA⟩
      have hins_sub : Sub.subset (Sub.insert i A) T = true := by
        rw [Sub.subset_iff_mem]; intro j hj
        rw [Sub.mem_insert, Bool.or_eq_true] at hj
        rcases hj with hj_eq | hjA
        · rw [of_decide_eq_true hj_eq]; exact hiT
        · exact (Sub.subset_iff_mem A T).mp hAT j hjA
      have hc1 := Sub.card_insert_of_not_mem i A hiA
      have hstep := (M.r_insert_bounds A i).1
      have hrest := ih (Sub.insert i A) hins_sub (by omega)
      omega

/-- Matroid closure operator `cl(S) = {i : r(S ∪ {i}) = r(S)}`. -/
def cl (S : Sub m) : Sub m :=
  Sub.ofBoolFn m (fun i => decide (M.r (Sub.insert i S) = M.r S))

theorem mem_cl_iff (S : Sub m) (i : Fin m) :
    Sub.mem i (M.cl S) = true ↔ M.r (Sub.insert i S) = M.r S := by
  unfold cl
  rw [Sub.mem_ofBoolFn]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem subset_cl (S : Sub m) : Sub.subset S (M.cl S) = true := by
  rw [Sub.subset_iff_mem]
  intro i hi
  rw [M.mem_cl_iff, Sub.insert_eq_of_mem hi]

/-- Adding any subset of `cl S` preserves rank `r S`. -/
theorem r_eq_of_subset_cl {S T : Sub m}
    (hST : Sub.subset S T = true) (hTcl : Sub.subset T (M.cl S) = true) :
    M.r T = M.r S := by
  suffices ∀ k : Nat, ∀ A : Sub m,
      Sub.subset S A = true → Sub.subset A T = true → Sub.card A - Sub.card S ≤ k → M.r A = M.r S by
    exact this (Sub.card T - Sub.card S) T hST (Sub.subset_refl T) (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro A hSA _ hdiff
    by_cases heq : A = S
    · subst heq; rfl
    · rcases Sub.exists_not_mem_of_lt hSA (Ne.symm heq) with ⟨i, hiA, hiS⟩
      have hins : Sub.subset (Sub.insert i S) A = true := by
        rw [Sub.subset_iff_mem]; intro j hj
        rw [Sub.mem_insert, Bool.or_eq_true] at hj
        rcases hj with hj_eq | hjS
        · rw [of_decide_eq_true hj_eq]; exact hiA
        · exact (Sub.subset_iff_mem S A).mp hSA j hjS
      have hc1 := Sub.card_insert_of_not_mem i S hiS
      have hc2 := Sub.card_mono hins
      omega
  | succ k ih =>
    intro A hSA hAT hdiff
    by_cases heq : A = S
    · subst heq; rfl
    · rcases Sub.exists_not_mem_of_lt hSA (Ne.symm heq) with ⟨i, hiA, hiS⟩
      let A' := Sub.ofBoolFn m (fun j => Sub.mem j A && !decide (j = i))
      have hA_eq : Sub.insert i A' = A := by
        apply Sub.ext_mem; intro j
        rw [Sub.mem_insert, Sub.mem_ofBoolFn]
        by_cases hji : j = i
        · subst hji; simp [hiA]
        · simp [hji]
      have hiA' : Sub.mem i A' = false := by simp [A', Sub.mem_ofBoolFn]
      have hSA' : Sub.subset S A' = true := by
        rw [Sub.subset_iff_mem]; intro j hjS
        rw [Sub.mem_ofBoolFn]
        have hjA := (Sub.subset_iff_mem S A).mp hSA j hjS
        have hji : j ≠ i := fun h => by subst h; rw [hjS] at hiS; contradiction
        simp [hjA, hji]
      have hA'T : Sub.subset A' T = true :=
        Sub.subset_trans (by rw [← hA_eq]; exact Sub.subset_insert i A') hAT
      have hcA : Sub.card A = Sub.card A' + 1 := by
        rw [← hA_eq]; exact Sub.card_insert_of_not_mem i A' hiA'
      have hrA' : M.r A' = M.r S := ih A' hSA' hA'T (by omega)
      have hi_cl : M.r (Sub.insert i S) = M.r S := by
        rw [← M.mem_cl_iff]
        exact (Sub.subset_iff_mem T (M.cl S)).mp hTcl i ((Sub.subset_iff_mem A T).mp hAT i hiA)
      have hinter_S : Sub.subset S (Sub.inter A' (Sub.insert i S)) = true :=
        Sub.subset_inter hSA' (Sub.subset_insert i S)
      have hunion_eq : Sub.union A' (Sub.insert i S) = A := by
        apply Sub.ext_mem; intro j
        rw [Sub.mem_union, Sub.mem_insert, Sub.mem_ofBoolFn]
        by_cases hji : j = i
        · subst hji; simp [hiA]
        · simp only [hji, decide_false, Bool.not_false, Bool.and_true, Bool.false_or]
          cases hjS : Sub.mem j S
          · simp
          · have hjA := (Sub.subset_iff_mem S A).mp hSA j hjS
            simp [hjA]
      have hsub := M.r_submod A' (Sub.insert i S)
      rw [hunion_eq, hrA', hi_cl] at hsub
      have hlow1 : M.r S ≤ M.r (Sub.inter A' (Sub.insert i S)) := M.r_mono hinter_S
      have hlow2 : M.r S ≤ M.r A := M.r_mono hSA
      omega

theorem r_cl (S : Sub m) : M.r (M.cl S) = M.r S :=
  M.r_eq_of_subset_cl (M.subset_cl S) (Sub.subset_refl _)

theorem cl_mono {S T : Sub m} (h : Sub.subset S T = true) :
    Sub.subset (M.cl S) (M.cl T) = true := by
  rw [Sub.subset_iff_mem]
  intro i hi
  rw [M.mem_cl_iff] at hi ⊢
  have hinter : Sub.subset S (Sub.inter T (Sub.insert i S)) = true :=
    Sub.subset_inter h (Sub.subset_insert i S)
  have hunion : Sub.union T (Sub.insert i S) = Sub.insert i T := by
    apply Sub.ext_mem; intro j
    rw [Sub.mem_union, Sub.mem_insert, Sub.mem_insert]
    by_cases hji : j = i
    · subst hji; simp
    · simp only [hji, decide_false, Bool.false_or]
      cases hjS : Sub.mem j S
      · simp
      · simp [(Sub.subset_iff_mem S T).mp h j hjS]
  have hsub := M.r_submod T (Sub.insert i S)
  rw [hunion, hi] at hsub
  have h1 : M.r S ≤ M.r (Sub.inter T (Sub.insert i S)) := M.r_mono hinter
  have h2 : M.r T ≤ M.r (Sub.insert i T) := (M.r_insert_bounds T i).1
  omega

theorem cl_idem (S : Sub m) : M.cl (M.cl S) = M.cl S := by
  apply Sub.subset_antisymm
  · rw [Sub.subset_iff_mem]
    intro i hi
    rw [M.mem_cl_iff] at hi ⊢
    have h1 : M.r S ≤ M.r (Sub.insert i S) := (M.r_insert_bounds S i).1
    have h2 : M.r (Sub.insert i S) ≤ M.r (Sub.insert i (M.cl S)) := by
      apply M.r_mono
      rw [Sub.subset_iff_mem]; intro j hj
      rw [Sub.mem_insert, Bool.or_eq_true] at hj
      rw [Sub.mem_insert, Bool.or_eq_true]
      rcases hj with hji | hjS
      · exact Or.inl hji
      · exact Or.inr ((Sub.subset_iff_mem S (M.cl S)).mp (M.subset_cl S) j hjS)
    have h3 := M.r_cl S
    omega
  · exact M.subset_cl (M.cl S)

/-- Flat predicate: `cl F = F`. -/
def IsFlat (F : Sub m) : Prop := M.cl F = F

instance (F : Sub m) : Decidable (M.IsFlat F) := inferInstanceAs (Decidable (M.cl F = F))

theorem empty_isFlat : M.IsFlat (Sub.empty m) := by
  unfold IsFlat
  apply Sub.subset_antisymm _ (M.subset_cl _)
  rw [Sub.subset_iff_mem]; intro i hi
  rw [M.mem_cl_iff] at hi
  have hs : Sub.insert i (Sub.empty m) = Sub.singleton i := rfl
  rw [hs, M.r_singleton i, M.r_empty] at hi
  omega

theorem univ_isFlat : M.IsFlat (Sub.univ m) := by
  unfold IsFlat
  exact Sub.subset_antisymm (Sub.subset_univ _) (M.subset_cl _)

theorem singleton_isFlat (i : Fin m) : M.IsFlat (Sub.singleton i) := by
  unfold IsFlat
  apply Sub.subset_antisymm _ (M.subset_cl _)
  rw [Sub.subset_iff_mem]; intro j hj
  rw [M.mem_cl_iff] at hj
  by_cases hji : j = i
  · subst hji; rw [Sub.mem_singleton]; simp
  · rw [M.r_pair j i hji, M.r_singleton i] at hj
    omega

theorem cl_isFlat (S : Sub m) : M.IsFlat (M.cl S) := M.cl_idem S

theorem inter_isFlat {F₁ F₂ : Sub m} (h₁ : M.IsFlat F₁) (h₂ : M.IsFlat F₂) :
    M.IsFlat (Sub.inter F₁ F₂) := by
  unfold IsFlat at h₁ h₂ ⊢
  apply Sub.subset_antisymm _ (M.subset_cl _)
  have s1 : Sub.subset (M.cl (Sub.inter F₁ F₂)) F₁ = true :=
    Sub.subset_trans (M.cl_mono (Sub.inter_subset_left F₁ F₂))
      (by rw [h₁]; exact Sub.subset_refl F₁)
  have s2 : Sub.subset (M.cl (Sub.inter F₁ F₂)) F₂ = true :=
    Sub.subset_trans (M.cl_mono (Sub.inter_subset_right F₁ F₂))
      (by rw [h₂]; exact Sub.subset_refl F₂)
  exact Sub.subset_inter s1 s2

theorem flat_lt_r {F₁ F₂ : Sub m} (h₁ : M.IsFlat F₁) (hle : Sub.subset F₁ F₂ = true) (hne : F₁ ≠ F₂) :
    M.r F₁ < M.r F₂ := by
  rcases Sub.exists_not_mem_of_lt hle hne with ⟨i, hi₂, hi₁⟩
  have hnot : M.r (Sub.insert i F₁) ≠ M.r F₁ := by
    intro heq
    have hm : Sub.mem i (M.cl F₁) = true := (M.mem_cl_iff F₁ i).mpr heq
    rw [h₁, hi₁] at hm; contradiction
  have hb := M.r_insert_bounds F₁ i
  have hins_le : Sub.subset (Sub.insert i F₁) F₂ = true := by
    rw [Sub.subset_iff_mem]; intro j hj
    rw [Sub.mem_insert, Bool.or_eq_true] at hj
    rcases hj with hji | hj₁
    · rw [of_decide_eq_true hji]; exact hi₂
    · exact (Sub.subset_iff_mem F₁ F₂).mp hle j hj₁
  have hrm := M.r_mono hins_le
  omega

/-- Carrier type of flats `{ F : Sub m // M.IsFlat F }`. -/
abbrev Flat := { F : Sub m // M.IsFlat F }

/--
**Theorem (`SimpleMatroid.toGeometricLattice`):**
Given any `SimpleMatroid m` and any duplicate-free list `rawFlats : List (Sub m)` containing
precisely the flats of `M` (`S ∈ rawFlats ↔ M.IsFlat S`), the lattice of flats of `M` is a
genuine `GeometricLattice`.
-/
def toGeometricLattice (rawFlats : List (Sub m))
    (hnd : NoDup rawFlats)
    (hmem_iff : ∀ S : Sub m, S ∈ rawFlats ↔ M.IsFlat S) :
    GeometricLattice M.Flat := by
  have hraw : ∀ S ∈ rawFlats, M.IsFlat S := fun S hS => (hmem_iff S).mp hS
  have hnd_lift : NoDup (rawFlats.pmap Subtype.mk hraw) := by
    clear hmem_iff
    induction hnd with
    | nil => exact NoDup.nil
    | @cons a as hnin _ ih =>
      simp only [List.pmap]
      refine NoDup.cons ?_ (ih (fun S hS => hraw S (List.mem_cons_of_mem a hS)))
      intro hm
      rw [List.mem_pmap] at hm
      rcases hm with ⟨b, hb, heq⟩
      cases heq
      exact hnin hb
  have hmem_lift : ∀ x : M.Flat, x ∈ rawFlats.pmap Subtype.mk hraw := by
    rintro ⟨F, hF⟩
    rw [List.mem_pmap]
    exact ⟨F, (hmem_iff F).mpr hF, rfl⟩
  exact {
    elems := rawFlats.pmap Subtype.mk hraw
    nodup_elems := hnd_lift
    mem_elems := hmem_lift
    leb := fun x y => Sub.subset x.1 y.1
    bot := ⟨Sub.empty m, M.empty_isFlat⟩
    top := ⟨Sub.univ m, M.univ_isFlat⟩
    meet := fun x y => ⟨Sub.inter x.1 y.1, M.inter_isFlat x.2 y.2⟩
    join := fun x y => ⟨M.cl (Sub.union x.1 y.1), M.cl_isFlat _⟩
    rk := fun x => M.r x.1
    le_refl := fun x => Sub.subset_refl x.1
    le_trans := fun h1 h2 => Sub.subset_trans h1 h2
    le_antisymm := fun h1 h2 => Subtype.eq (Sub.subset_antisymm h1 h2)
    bot_le := fun x => Sub.empty_subset x.1
    le_top := fun x => Sub.subset_univ x.1
    meet_le_left := fun x y => Sub.inter_subset_left x.1 y.1
    meet_le_right := fun x y => Sub.inter_subset_right x.1 y.1
    le_meet := fun h1 h2 => Sub.subset_inter h1 h2
    le_join_left := fun x y => Sub.subset_trans (Sub.subset_union_left x.1 y.1) (M.subset_cl _)
    le_join_right := fun x y => Sub.subset_trans (Sub.subset_union_right x.1 y.1) (M.subset_cl _)
    join_le := fun {x y z} h1 h2 => by
      have hu : Sub.subset (Sub.union x.1 y.1) z.1 = true := Sub.union_subset h1 h2
      have hcl : Sub.subset (M.cl (Sub.union x.1 y.1)) (M.cl z.1) = true := M.cl_mono hu
      rwa [z.2] at hcl
    rk_bot := M.r_empty
    lt_rk := fun {x y} hle hne => M.flat_lt_r x.2 hle (fun h => hne (Subtype.eq h))
    exists_step := fun {x y} hle hgt => by
      have hne : x.1 ≠ y.1 := by
        intro h; have : M.r x.1 = M.r y.1 := by rw [h]
        omega
      rcases Sub.exists_not_mem_of_lt hle hne with ⟨i, hiy, hix⟩
      let Z : M.Flat := ⟨M.cl (Sub.insert i x.1), M.cl_isFlat _⟩
      have hxZ : Sub.subset x.1 Z.1 = true :=
        Sub.subset_trans (Sub.subset_insert i x.1) (M.subset_cl _)
      have hZx_ne : Z ≠ x := by
        intro h
        have hiZ : Sub.mem i Z.1 = true :=
          (Sub.subset_iff_mem _ _).mp (M.subset_cl (Sub.insert i x.1)) i
            (by rw [Sub.mem_insert]; simp)
        rw [h, hix] at hiZ; contradiction
      have hZy : Sub.subset Z.1 y.1 = true := by
        have hins_y : Sub.subset (Sub.insert i x.1) y.1 = true := by
          rw [Sub.subset_iff_mem]; intro j hj
          rw [Sub.mem_insert, Bool.or_eq_true] at hj
          rcases hj with hji | hjx
          · rw [of_decide_eq_true hji]; exact hiy
          · exact (Sub.subset_iff_mem x.1 y.1).mp hle j hjx
        have hcl_y := M.cl_mono hins_y
        rwa [y.2] at hcl_y
      have hrZ : M.r Z.1 = M.r x.1 + 1 := by
        change M.r (M.cl (Sub.insert i x.1)) = M.r x.1 + 1
        rw [M.r_cl]
        have hb := M.r_insert_bounds x.1 i
        have hnot : M.r (Sub.insert i x.1) ≠ M.r x.1 := by
          intro heq
          have hm : Sub.mem i (M.cl x.1) = true := (M.mem_cl_iff x.1 i).mpr heq
          rw [x.2, hix] at hm; contradiction
        omega
      exact ⟨Z, hxZ, hZx_ne, hZy, hrZ⟩
    semimodular := fun x y => by
      change M.r (Sub.inter x.1 y.1) + M.r (M.cl (Sub.union x.1 y.1)) ≤ M.r x.1 + M.r y.1
      rw [M.r_cl]
      exact M.r_submod x.1 y.1
    atomistic := fun {x y} hall => by
      rw [Sub.subset_iff_mem]
      intro i hix
      let A : M.Flat := ⟨Sub.singleton i, M.singleton_isFlat i⟩
      have hrA : M.r A.1 = 1 := M.r_singleton i
      have hAx : Sub.subset A.1 x.1 = true := by
        rw [Sub.subset_iff_mem]; intro j hj
        rw [Sub.mem_singleton] at hj
        rw [of_decide_eq_true hj]; exact hix
      have hAy : Sub.subset A.1 y.1 = true := hall A hrA hAx
      exact (Sub.subset_iff_mem A.1 y.1).mp hAy i (by rw [Sub.mem_singleton]; simp)
  }

/-- Default canonical `GeometricLattice` filtering `Sub.allSubs m` by `M.IsFlat`. -/
def defaultGeometricLattice : GeometricLattice M.Flat :=
  M.toGeometricLattice
    ((Sub.allSubs m).filter (fun S => decide (M.IsFlat S)))
    (nodup_filter _ (Sub.nodup_allSubs m))
    (fun S => by
      rw [mem_filter_iff_prop]
      exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨Sub.mem_allSubs S, decide_eq_true h⟩⟩)

end SimpleMatroid

end Conjecture00000008533
