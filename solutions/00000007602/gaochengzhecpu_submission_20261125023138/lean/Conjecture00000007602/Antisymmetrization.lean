/-
  Conjecture 00000007602 — Module 2: Symmetric Group S_k, Inversion Sign,
  Tensor Powers T^k(R^n), Full Antisymmetrization Alt_k, and the Positive
  Characteristic-0 / Invertible-k! Realization Theorem for all n, k ∈ ℕ.

  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000007602.BinomialThreshold

namespace Conjecture00000007602

/-! ## 1. Constructive Finite Lists, Duplicate-Freeness, and Commutative Monoid Sums -/

/-- Elementary duplicate-free predicate on lists. -/
def NoDup {α : Type} : List α → Prop
  | [] => True
  | a :: l => a ∉ l ∧ NoDup l

def listFlatMap {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | a :: l, f => f a ++ listFlatMap l f

theorem mem_listFlatMap {α β : Type} {f : α → List β} {b : β} :
    ∀ {l : List α}, b ∈ listFlatMap l f ↔ ∃ a ∈ l, b ∈ f a
  | [] => by simp [listFlatMap]
  | a :: t => by
      simp only [listFlatMap, List.mem_append, mem_listFlatMap, List.mem_cons]
      constructor
      · intro h
        cases h with
        | inl hfa => exact ⟨a, Or.inl rfl, hfa⟩
        | inr hex =>
            rcases hex with ⟨x, hxt, hfx⟩
            exact ⟨x, Or.inr hxt, hfx⟩
      · rintro ⟨x, hx, hfx⟩
        cases hx with
        | inl hxa => subst hxa; exact Or.inl hfx
        | inr hxt => exact Or.inr ⟨x, hxt, hfx⟩

theorem listFlatMap_length_const {α β : Type} (f : α → List β) (c : Nat) :
    ∀ {l : List α}, (∀ a ∈ l, (f a).length = c) → (listFlatMap l f).length = l.length * c
  | [], _ => by simp [listFlatMap]
  | a :: t, h => by
      have ha : (f a).length = c := h a (List.Mem.head t)
      have ht : ∀ x ∈ t, (f x).length = c := fun x hx => h x (List.Mem.tail a hx)
      simp [listFlatMap, List.length_append, ha, listFlatMap_length_const f c ht, Nat.succ_mul,
        Nat.add_comm]

theorem mem_split {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l → ∃ u v : List α, l = u ++ x :: v
  | [], h => nomatch h
  | a :: t, h => by
      cases List.mem_cons.mp h with
      | inl hxa =>
          subst hxa
          exact ⟨[], t, rfl⟩
      | inr hxt =>
          rcases mem_split hxt with ⟨u, v, rfl⟩
          exact ⟨a :: u, v, rfl⟩

theorem noDup_append {α : Type} :
    ∀ {l1 l2 : List α}, NoDup l1 → NoDup l2 → (∀ x ∈ l1, x ∉ l2) → NoDup (l1 ++ l2)
  | [], _, _, h2, _ => h2
  | a :: t, l2, ⟨hat, hnd1⟩, h2, hdisj => by
      refine ⟨?_, noDup_append hnd1 h2 (fun x hx => hdisj x (List.Mem.tail a hx))⟩
      intro hmem
      cases List.mem_append.mp hmem with
      | inl h1 => exact hat h1
      | inr h2m => exact hdisj a (List.Mem.head t) h2m

theorem noDup_remove_middle {α : Type} {a : α} :
    ∀ {u v : List α}, NoDup (u ++ a :: v) → a ∉ u ∧ a ∉ v ∧ NoDup (u ++ v)
  | [], v, ⟨hav, hndv⟩ => ⟨by simp, hav, hndv⟩
  | b :: u, v, ⟨hbuv, hnd⟩ => by
      rcases noDup_remove_middle hnd with ⟨hau, hav, hnd_uv⟩
      have hba : b ≠ a := by
        intro h
        subst h
        exact hbuv (List.mem_append.mpr (Or.inr (List.Mem.head v)))
      refine ⟨?_, hav, ⟨?_, hnd_uv⟩⟩
      · intro hmem
        cases List.mem_cons.mp hmem with
        | inl hab => exact hba hab.symm
        | inr hmu => exact hau hmu
      · intro hmem
        apply hbuv
        cases List.mem_append.mp hmem with
        | inl hmu => exact List.mem_append.mpr (Or.inl hmu)
        | inr hmv => exact List.mem_append.mpr (Or.inr (List.Mem.tail a hmv))

theorem noDup_map_of_inj {α β : Type} (f : α → β)
    (hinj : ∀ x y, f x = f y → x = y) :
    ∀ {l : List α}, NoDup l → NoDup (l.map f)
  | [], _ => trivial
  | a :: t, ⟨hat, hndt⟩ => by
      refine ⟨?_, noDup_map_of_inj f hinj hndt⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨x, hxt, hfx⟩
      have hxa : x = a := hinj x a hfx
      subst hxa
      exact hat hxt

theorem noDup_filter {α : Type} (p : α → Bool) :
    ∀ {l : List α}, NoDup l → NoDup (l.filter p)
  | [], _ => trivial
  | a :: t, ⟨hat, hndt⟩ => by
      simp only [List.filter]
      cases p a with
      | false => exact noDup_filter p hndt
      | true =>
          refine ⟨?_, noDup_filter p hndt⟩
          intro hmem
          exact hat (List.mem_filter.mp hmem).1

theorem noDup_listFlatMap {α β : Type} {l : List α} {f : α → List β}
    (hl : NoDup l)
    (hf : ∀ a ∈ l, NoDup (f a))
    (hdisj : ∀ a1 ∈ l, ∀ a2 ∈ l, a1 ≠ a2 → ∀ b, b ∈ f a1 → b ∉ f a2) :
    NoDup (listFlatMap l f) := by
  induction l with
  | nil => trivial
  | cons a t ih =>
      rcases hl with ⟨hat, hndt⟩
      apply noDup_append (hf a (List.Mem.head t))
      · exact ih hndt
          (fun x hx => hf x (List.Mem.tail a hx))
          (fun x1 hx1 x2 hx2 hne =>
            hdisj x1 (List.Mem.tail a hx1) x2 (List.Mem.tail a hx2) hne)
      · intro b hba hbt
        rcases mem_listFlatMap.mp hbt with ⟨x, hxt, hbx⟩
        have hax : a ≠ x := fun heq => by subst heq; exact hat hxt
        exact hdisj a (List.Mem.head t) x (List.Mem.tail a hxt) hax b hba hbx

/-- Commutative monoid structure for finite reindexed sums. -/
structure CommMonoidOps (M : Type) where
  zero : M
  add : M → M → M
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a

theorem cm_add_zero {M : Type} (cm : CommMonoidOps M) (a : M) :
    cm.add a cm.zero = a := by
  rw [cm.add_comm, cm.zero_add]

def listSum {α M : Type} (cm : CommMonoidOps M) : List α → (α → M) → M
  | [], _ => cm.zero
  | a :: l, f => cm.add (f a) (listSum cm l f)

theorem listSum_append {α M : Type} (cm : CommMonoidOps M) (f : α → M) :
    ∀ (l1 l2 : List α), listSum cm (l1 ++ l2) f = cm.add (listSum cm l1 f) (listSum cm l2 f)
  | [], l2 => by simp [listSum, cm.zero_add]
  | a :: t, l2 => by
      simp [listSum, listSum_append cm f t l2, cm.add_assoc]

theorem listSum_map {α β M : Type} (cm : CommMonoidOps M) (g : α → β) (f : β → M) :
    ∀ (l : List α), listSum cm (l.map g) f = listSum cm l (fun x => f (g x))
  | [] => rfl
  | a :: t => by simp [listSum, listSum_map cm g f t]

theorem listSum_congr {α M : Type} (cm : CommMonoidOps M) {f g : α → M} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → listSum cm l f = listSum cm l g
  | [], _ => rfl
  | a :: t, h => by
      simp [listSum, h a (List.Mem.head t),
        listSum_congr cm (fun x hx => h x (List.Mem.tail a hx))]

theorem listSum_eq_zero {α M : Type} (cm : CommMonoidOps M) {f : α → M} :
    ∀ {l : List α}, (∀ x ∈ l, f x = cm.zero) → listSum cm l f = cm.zero
  | [], _ => rfl
  | a :: t, h => by
      simp [listSum, h a (List.Mem.head t),
        listSum_eq_zero cm (fun x hx => h x (List.Mem.tail a hx)), cm.zero_add]

theorem listSum_add_fn {α M : Type} (cm : CommMonoidOps M) (f g : α → M) :
    ∀ (l : List α),
      listSum cm l (fun x => cm.add (f x) (g x)) = cm.add (listSum cm l f) (listSum cm l g)
  | [] => by simp [listSum, cm.zero_add]
  | a :: t => by
      simp only [listSum, listSum_add_fn cm f g t]
      calc
        cm.add (cm.add (f a) (g a)) (cm.add (listSum cm t f) (listSum cm t g))
            = cm.add (f a) (cm.add (g a) (cm.add (listSum cm t f) (listSum cm t g))) :=
              cm.add_assoc _ _ _
        _ = cm.add (f a) (cm.add (cm.add (g a) (listSum cm t f)) (listSum cm t g)) := by
              rw [cm.add_assoc (g a)]
        _ = cm.add (f a) (cm.add (cm.add (listSum cm t f) (g a)) (listSum cm t g)) := by
              rw [cm.add_comm (g a) (listSum cm t f)]
        _ = cm.add (f a) (cm.add (listSum cm t f) (cm.add (g a) (listSum cm t g))) := by
              rw [cm.add_assoc (listSum cm t f)]
        _ = cm.add (cm.add (f a) (listSum cm t f)) (cm.add (g a) (listSum cm t g)) := by
              rw [← cm.add_assoc (f a)]

theorem listSum_filter_split {α M : Type} (cm : CommMonoidOps M) (p : α → Bool) (f : α → M) :
    ∀ (l : List α),
      listSum cm l f =
        cm.add (listSum cm (l.filter (fun x => !p x)) f) (listSum cm (l.filter p) f)
  | [] => by simp [listSum, cm.zero_add]
  | a :: t => by
      simp only [List.filter]
      cases hp : p a with
      | false =>
          simp only [Bool.not_false, listSum, listSum_filter_split cm p f t, cm.add_assoc]
      | true =>
          simp only [Bool.not_true, listSum, listSum_filter_split cm p f t]
          calc
            cm.add (f a)
                (cm.add (listSum cm (List.filter (fun x => !p x) t) f)
                  (listSum cm (List.filter p t) f))
                = cm.add
                    (cm.add (f a) (listSum cm (List.filter (fun x => !p x) t) f))
                    (listSum cm (List.filter p t) f) := by rw [← cm.add_assoc]
            _ = cm.add
                  (cm.add (listSum cm (List.filter (fun x => !p x) t) f) (f a))
                  (listSum cm (List.filter p t) f) := by
                rw [cm.add_comm (f a)]
            _ = cm.add (listSum cm (List.filter (fun x => !p x) t) f)
                  (cm.add (f a) (listSum cm (List.filter p t) f)) := by
                rw [cm.add_assoc]

/-- Reindexing invariance of `listSum` across duplicate-free lists with identical elements. -/
theorem listSum_nodup_perm {α M : Type} (cm : CommMonoidOps M) (f : α → M) :
    ∀ {l1 l2 : List α}, NoDup l1 → NoDup l2 → (∀ x, x ∈ l1 ↔ x ∈ l2) →
      listSum cm l1 f = listSum cm l2 f
  | [], l2, _, _, hmem => by
      cases l2 with
      | nil => rfl
      | cons b bs =>
          have hb : b ∈ ([] : List α) := (hmem b).mpr (List.Mem.head bs)
          nomatch hb
  | a :: t, l2, ⟨hat, hndt⟩, hnd2, hmem => by
      have hal2 : a ∈ l2 := (hmem a).mp (List.Mem.head t)
      rcases mem_split hal2 with ⟨u, v, rfl⟩
      rcases noDup_remove_middle hnd2 with ⟨hau, hav, hnd_uv⟩
      have hmem' : ∀ x, x ∈ t ↔ x ∈ u ++ v := by
        intro x
        constructor
        · intro hxt
          have hxa : x ≠ a := fun heq => by subst heq; exact hat hxt
          have hx2 : x ∈ u ++ a :: v := (hmem x).mp (List.Mem.tail a hxt)
          cases List.mem_append.mp hx2 with
          | inl hxu => exact List.mem_append.mpr (Or.inl hxu)
          | inr hxav =>
              cases List.mem_cons.mp hxav with
              | inl heq => exact False.elim (hxa heq)
              | inr hxv => exact List.mem_append.mpr (Or.inr hxv)
        · intro hxuv
          have hxa : x ≠ a := by
            intro heq
            subst heq
            cases List.mem_append.mp hxuv with
            | inl hxu => exact hau hxu
            | inr hxv => exact hav hxv
          have hx2 : x ∈ u ++ a :: v := by
            cases List.mem_append.mp hxuv with
            | inl hxu => exact List.mem_append.mpr (Or.inl hxu)
            | inr hxv => exact List.mem_append.mpr (Or.inr (List.Mem.tail a hxv))
          cases List.mem_cons.mp ((hmem x).mpr hx2) with
          | inl heq => exact False.elim (hxa heq)
          | inr hxt => exact hxt
      have ih := listSum_nodup_perm cm f hndt hnd_uv hmem'
      simp only [listSum, listSum_append cm f u (a :: v), listSum_append cm f u v] at ih ⊢
      rw [ih]
      calc
        cm.add (f a) (cm.add (listSum cm u f) (listSum cm v f))
            = cm.add (cm.add (f a) (listSum cm u f)) (listSum cm v f) := by rw [← cm.add_assoc]
        _ = cm.add (cm.add (listSum cm u f) (f a)) (listSum cm v f) := by
              rw [cm.add_comm (f a)]
        _ = cm.add (listSum cm u f) (cm.add (f a) (listSum cm v f)) := by rw [cm.add_assoc]

/-! ## 2. Enumeration of `Fin m` and Decidable Equality of Tuples -/

def finList : (m : Nat) → List (Fin m)
  | 0 => []
  | m + 1 =>
      ⟨0, Nat.succ_pos m⟩ ::
        (finList m).map (fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem finList_length : ∀ m : Nat, (finList m).length = m
  | 0 => rfl
  | m + 1 => by simp [finList, finList_length m]

theorem finList_mem : ∀ {m : Nat} (x : Fin m), x ∈ finList m
  | 0, x => nomatch x.isLt
  | m + 1, ⟨0, _⟩ => List.Mem.head _
  | m + 1, ⟨v + 1, hv⟩ => by
      simp only [finList, List.mem_cons, List.mem_map]
      right
      exact ⟨⟨v, Nat.lt_of_succ_lt_succ hv⟩, finList_mem _, rfl⟩

theorem finList_noDup : ∀ m : Nat, NoDup (finList m)
  | 0 => trivial
  | m + 1 => by
      refine ⟨?_, noDup_map_of_inj _ ?_ (finList_noDup m)⟩
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _, hi⟩
        have hv : i.val + 1 = 0 := congrArg Fin.val hi
        omega
      · intro x y hxy
        have hv : x.val + 1 = y.val + 1 := congrArg Fin.val hxy
        exact Fin.ext (by omega)

/-- Constructive boolean equality on finite tuples `Fin k → Fin n`. -/
def vecEq {k n : Nat} (u v : Fin k → Fin n) : Bool :=
  (finList k).all (fun i => decide (u i = v i))

theorem vecEq_iff {k n : Nat} (u v : Fin k → Fin n) : vecEq u v = true ↔ u = v := by
  unfold vecEq
  rw [List.all_eq_true]
  constructor
  · intro h
    funext i
    exact of_decide_eq_true (h i (finList_mem i))
  · intro h i _
    subst h
    exact decide_eq_true rfl

/-! ## 3. Symmetric Group `Perm k`, Exhaustive `k!`-Enumeration, and Inversion Sign -/

structure Perm (k : Nat) where
  toFun : Fin k → Fin k
  invFun : Fin k → Fin k
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

theorem Perm.ext {k : Nat} {σ τ : Perm k} (h : ∀ i, σ.toFun i = τ.toFun i) : σ = τ := by
  have hto : σ.toFun = τ.toFun := funext h
  have hinv : σ.invFun = τ.invFun := by
    funext y
    calc
      σ.invFun y = σ.invFun (τ.toFun (τ.invFun y)) := by rw [τ.right_inv]
      _ = σ.invFun (σ.toFun (τ.invFun y)) := by rw [hto]
      _ = τ.invFun y := σ.left_inv _
  cases σ
  cases τ
  simp only [mk.injEq]
  exact ⟨hto, hinv⟩

def Perm.id (k : Nat) : Perm k where
  toFun := fun i => i
  invFun := fun i => i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def Perm.comp {k : Nat} (σ τ : Perm k) : Perm k where
  toFun := fun i => σ.toFun (τ.toFun i)
  invFun := fun i => τ.invFun (σ.invFun i)
  left_inv := fun i => by rw [σ.left_inv, τ.left_inv]
  right_inv := fun i => by rw [τ.right_inv, σ.right_inv]

def Perm.inv {k : Nat} (σ : Perm k) : Perm k where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

theorem Perm.comp_assoc {k : Nat} (σ τ ρ : Perm k) :
    Perm.comp (Perm.comp σ τ) ρ = Perm.comp σ (Perm.comp τ ρ) :=
  Perm.ext (fun _ => rfl)

theorem Perm.inv_comp {k : Nat} (σ : Perm k) : Perm.comp σ.inv σ = Perm.id k :=
  Perm.ext σ.left_inv

theorem Perm.comp_inv {k : Nat} (σ : Perm k) : Perm.comp σ σ.inv = Perm.id k :=
  Perm.ext σ.right_inv

theorem Perm.toFun_injective {k : Nat} (σ : Perm k) {i j : Fin k}
    (h : σ.toFun i = σ.toFun j) : i = j := by
  calc
    i = σ.invFun (σ.toFun i) := (σ.left_inv i).symm
    _ = σ.invFun (σ.toFun j) := by rw [h]
    _ = j := σ.left_inv j

def unskipFin {m : Nat} (r y : Fin (m + 1)) (hne : y ≠ r) : Fin m :=
  if hlt : y.val < r.val then
    ⟨y.val, by have := r.isLt; omega⟩
  else
    ⟨y.val - 1, by
      have hvne : y.val ≠ r.val := fun hv => hne (Fin.ext hv)
      have hy := y.isLt
      omega⟩

@[simp] theorem unskipFin_val {m : Nat} (r y : Fin (m + 1)) (hne : y ≠ r) :
    (unskipFin r y hne).val = if y.val < r.val then y.val else y.val - 1 := by
  unfold unskipFin
  split <;> rfl

theorem skipFin_unskipFin {m : Nat} (r y : Fin (m + 1)) (hne : y ≠ r) :
    skipFin r (unskipFin r y hne) = y := by
  have hvne : y.val ≠ r.val := fun hv => hne (Fin.ext hv)
  apply Fin.ext
  rw [skipFin_val, unskipFin_val]
  split <;> (try split) <;> omega

theorem unskipFin_skipFin {m : Nat} (r : Fin (m + 1)) (i : Fin m)
    (hne : skipFin r i ≠ r) :
    unskipFin r (skipFin r i) hne = i := by
  apply Fin.ext
  rw [unskipFin_val, skipFin_val]
  split <;> (try split) <;> omega

/-- Insert image `r = σ(0)` on `0` and shift `π : Perm k` onto `Fin (k + 1) \ {r}`. -/
def insertPerm {k : Nat} (r : Fin (k + 1)) (π : Perm k) : Perm (k + 1) where
  toFun := fun x =>
    match x with
    | ⟨0, _⟩ => r
    | ⟨v + 1, hv⟩ => skipFin r (π.toFun ⟨v, Nat.lt_of_succ_lt_succ hv⟩)
  invFun := fun y =>
    if h : y = r then
      ⟨0, Nat.succ_pos k⟩
    else
      let j := π.invFun (unskipFin r y h)
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  left_inv := by
    intro x
    match x with
    | ⟨0, _⟩ => exact dif_pos rfl
    | ⟨v + 1, hv⟩ =>
        have hne : skipFin r (π.toFun ⟨v, Nat.lt_of_succ_lt_succ hv⟩) ≠ r :=
          skipFin_ne r _
        rw [dif_neg hne]
        apply Fin.ext
        dsimp only
        rw [unskipFin_skipFin, π.left_inv]
  right_inv := by
    intro y
    by_cases h : y = r
    · subst h
      rw [dif_pos rfl]
    · rw [dif_neg h]
      dsimp only
      rw [π.right_inv]
      exact skipFin_unskipFin r y h

def eraseZeroPerm {k : Nat} (σ : Perm (k + 1)) : Perm k where
  toFun := fun i =>
    let x : Fin (k + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    have hne : σ.toFun x ≠ σ.toFun ⟨0, Nat.succ_pos k⟩ := by
      intro heq
      have hx0 := σ.toFun_injective heq
      have hv : i.val + 1 = 0 := congrArg Fin.val hx0
      omega
    unskipFin (σ.toFun ⟨0, Nat.succ_pos k⟩) (σ.toFun x) hne
  invFun := fun j =>
    let y := skipFin (σ.toFun ⟨0, Nat.succ_pos k⟩) j
    have hy : y ≠ σ.toFun ⟨0, Nat.succ_pos k⟩ := skipFin_ne _ j
    have hinv0 : σ.invFun y ≠ ⟨0, Nat.succ_pos k⟩ := by
      intro heq
      apply hy
      calc
        y = σ.toFun (σ.invFun y) := (σ.right_inv y).symm
        _ = σ.toFun ⟨0, Nat.succ_pos k⟩ := by rw [heq]
    ⟨(σ.invFun y).val - 1, by
      have hlt := (σ.invFun y).isLt
      have hv0 : (σ.invFun y).val ≠ 0 := fun hv => hinv0 (Fin.ext hv)
      omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    dsimp only
    have hsk :
        skipFin (σ.toFun ⟨0, Nat.succ_pos k⟩)
            (unskipFin (σ.toFun ⟨0, Nat.succ_pos k⟩)
              (σ.toFun ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (by
                intro heq
                have hx0 := σ.toFun_injective heq
                have hv : i.val + 1 = 0 := congrArg Fin.val hx0
                omega)) =
          σ.toFun ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ :=
      skipFin_unskipFin _ _ _
    have hinv :
        σ.invFun
            (skipFin (σ.toFun ⟨0, Nat.succ_pos k⟩)
              (unskipFin (σ.toFun ⟨0, Nat.succ_pos k⟩)
                (σ.toFun ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                (by
                  intro heq
                  have hx0 := σ.toFun_injective heq
                  have hv : i.val + 1 = 0 := congrArg Fin.val hx0
                  omega))) =
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
      rw [hsk, σ.left_inv]
    have hv := congrArg Fin.val hinv
    dsimp only at hv
    omega
  right_inv := by
    intro j
    let r := σ.toFun ⟨0, Nat.succ_pos k⟩
    let y := skipFin r j
    have hy : y ≠ r := skipFin_ne r j
    have hinv0 : (σ.invFun y).val ≠ 0 := by
      intro hv
      have heq : σ.invFun y = ⟨0, Nat.succ_pos k⟩ := Fin.ext hv
      apply hy
      calc
        y = σ.toFun (σ.invFun y) := (σ.right_inv y).symm
        _ = r := by rw [heq]
    have hsucc : (⟨(σ.invFun y).val - 1 + 1,
        Nat.succ_lt_succ (by have := (σ.invFun y).isLt; omega)⟩ : Fin (k + 1)) = σ.invFun y := by
      apply Fin.ext
      dsimp only
      omega
    apply Fin.ext
    dsimp only
    rw [unskipFin_val]
    have hsy : σ.toFun ⟨(σ.invFun y).val - 1 + 1,
        Nat.succ_lt_succ (by have := (σ.invFun y).isLt; omega)⟩ = y := by
      rw [hsucc, σ.right_inv]
    rw [hsy]
    have h2 := unskipFin_skipFin r j hy
    have hv2 := congrArg Fin.val h2
    rw [unskipFin_val] at hv2
    exact hv2

theorem insertPerm_eraseZero {k : Nat} (σ : Perm (k + 1)) :
    insertPerm (σ.toFun ⟨0, Nat.succ_pos k⟩) (eraseZeroPerm σ) = σ := by
  apply Perm.ext
  intro x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨v + 1, hv⟩ =>
      dsimp only [insertPerm, eraseZeroPerm]
      exact skipFin_unskipFin _ _ _

theorem insertPerm_inj {k : Nat} {r1 r2 : Fin (k + 1)} {π1 π2 : Perm k}
    (h : insertPerm r1 π1 = insertPerm r2 π2) : r1 = r2 ∧ π1 = π2 := by
  have h0 : (insertPerm r1 π1).toFun ⟨0, Nat.succ_pos k⟩ =
      (insertPerm r2 π2).toFun ⟨0, Nat.succ_pos k⟩ := by rw [h]
  dsimp only [insertPerm] at h0
  subst h0
  refine ⟨rfl, Perm.ext (fun i => ?_)⟩
  have hi : (insertPerm r1 π1).toFun ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      (insertPerm r1 π2).toFun ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by rw [h]
  dsimp only [insertPerm] at hi
  exact skipFin_injective r1 hi

/-- Exhaustive duplicate-free list of all `k!` permutations of `Fin k`. -/
def allPerms : (k : Nat) → List (Perm k)
  | 0 => [Perm.id 0]
  | k + 1 => listFlatMap (finList (k + 1)) (fun r => (allPerms k).map (insertPerm r))

theorem allPerms_length : ∀ k : Nat, (allPerms k).length = factorial k
  | 0 => rfl
  | k + 1 => by
      simp only [allPerms]
      rw [listFlatMap_length_const _ (factorial k)]
      · rw [finList_length, factorial]
      · intro r _
        simp [allPerms_length k]

theorem allPerms_mem : ∀ {k : Nat} (σ : Perm k), σ ∈ allPerms k
  | 0, σ => by
      have h : σ = Perm.id 0 := Perm.ext (fun i => nomatch i.isLt)
      subst h
      exact List.Mem.head []
  | k + 1, σ => by
      rw [← insertPerm_eraseZero σ]
      simp only [allPerms, mem_listFlatMap]
      refine ⟨σ.toFun ⟨0, Nat.succ_pos k⟩, finList_mem _, ?_⟩
      exact List.mem_map.mpr ⟨eraseZeroPerm σ, allPerms_mem _, rfl⟩

theorem allPerms_noDup : ∀ k : Nat, NoDup (allPerms k)
  | 0 => ⟨by simp, trivial⟩
  | k + 1 => by
      simp only [allPerms]
      apply noDup_listFlatMap (finList_noDup (k + 1))
      · intro r _
        exact noDup_map_of_inj (insertPerm r) (fun p1 p2 hp => (insertPerm_inj hp).2)
          (allPerms_noDup k)
      · intro r1 _ r2 _ hne b hb1 hb2
        rcases List.mem_map.mp hb1 with ⟨p1, _, hp1⟩
        rcases List.mem_map.mp hb2 with ⟨p2, _, hp2⟩
        rw [← hp1] at hp2
        exact hne (insertPerm_inj hp2).1.symm

/-- Duplicate-free list of ordered index pairs `(i, j)` with `i < j < k`. -/
def orderedPairs (k : Nat) : List (Fin k × Fin k) :=
  listFlatMap (finList k) (fun i =>
    ((finList k).filter (fun j => decide (i.val < j.val))).map (fun j => (i, j)))

theorem mem_orderedPairs {k : Nat} (p : Fin k × Fin k) :
    p ∈ orderedPairs k ↔ p.1.val < p.2.val := by
  unfold orderedPairs
  rw [mem_listFlatMap]
  constructor
  · rintro ⟨i, _, hmem⟩
    rcases List.mem_map.mp hmem with ⟨j, hjf, hp⟩
    rw [← hp]
    exact of_decide_eq_true (List.mem_filter.mp hjf).2
  · intro hlt
    refine ⟨p.1, finList_mem p.1, List.mem_map.mpr ⟨p.2, ?_, ?_⟩⟩
    · exact List.mem_filter.mpr ⟨finList_mem p.2, decide_eq_true hlt⟩
    · cases p; rfl

theorem orderedPairs_noDup (k : Nat) : NoDup (orderedPairs k) := by
  unfold orderedPairs
  apply noDup_listFlatMap (finList_noDup k)
  · intro i _
    apply noDup_map_of_inj (fun j => (i, j))
    · intro j1 j2 h
      injection h
    · exact noDup_filter _ (finList_noDup k)
  · intro i1 _ i2 _ hne p hp1 hp2
    rcases List.mem_map.mp hp1 with ⟨j1, _, he1⟩
    rcases List.mem_map.mp hp2 with ⟨j2, _, he2⟩
    rw [← he1] at he2
    injection he2 with hi _
    exact hne hi.symm

def xorMonoid : CommMonoidOps Bool where
  zero := false
  add := xor
  add_assoc := Bool.xor_assoc
  add_comm := Bool.xor_comm
  zero_add := Bool.false_xor

/-- Inversion parity (`false` = even / `+1`, `true` = odd / `-1`) of `σ ∈ S_k`. -/
def parity {k : Nat} (σ : Perm k) : Bool :=
  listSum xorMonoid (orderedPairs k) (fun p => decide ((σ.toFun p.2).val < (σ.toFun p.1).val))

theorem parity_id (k : Nat) : parity (Perm.id k) = false := by
  unfold parity
  apply listSum_eq_zero xorMonoid
  intro p hp
  have hlt : p.1.val < p.2.val := (mem_orderedPairs p).mp hp
  have hnot : ¬ (p.2.val < p.1.val) := by omega
  exact decide_eq_false hnot

def ordPair {k : Nat} (a b : Fin k) : Fin k × Fin k :=
  if a.val < b.val then (a, b) else (b, a)

theorem ordPair_lt {k : Nat} {a b : Fin k} (hne : a ≠ b) :
    (ordPair a b).1.val < (ordPair a b).2.val := by
  have hv : a.val ≠ b.val := fun h => hne (Fin.ext h)
  unfold ordPair
  split <;> simp <;> omega

/-- Homomorphism law `parity (σ ∘ τ) = parity σ ⊕ parity τ` for all `σ, τ ∈ S_k`. -/
theorem parity_comp {k : Nat} (σ τ : Perm k) :
    parity (Perm.comp σ τ) = xor (parity σ) (parity τ) := by
  let φ : Fin k × Fin k → Fin k × Fin k := fun p => ordPair (τ.toFun p.1) (τ.toFun p.2)
  have hterm : ∀ p ∈ orderedPairs k,
      decide ((σ.toFun (τ.toFun p.2)).val < (σ.toFun (τ.toFun p.1)).val) =
        xor (decide ((σ.toFun (φ p).2).val < (σ.toFun (φ p).1).val))
            (decide ((τ.toFun p.2).val < (τ.toFun p.1).val)) := by
    intro p hp
    have hp_lt : p.1.val < p.2.val := (mem_orderedPairs p).mp hp
    have hp_ne : p.1 ≠ p.2 := fun heq => by rw [heq] at hp_lt; exact Nat.lt_irrefl _ hp_lt
    have ht_ne : τ.toFun p.1 ≠ τ.toFun p.2 := fun heq => hp_ne (τ.toFun_injective heq)
    have htv_ne : (τ.toFun p.1).val ≠ (τ.toFun p.2).val := fun hv => ht_ne (Fin.ext hv)
    have hs_ne : σ.toFun (τ.toFun p.1) ≠ σ.toFun (τ.toFun p.2) :=
      fun heq => ht_ne (σ.toFun_injective heq)
    have hsv_ne : (σ.toFun (τ.toFun p.1)).val ≠ (σ.toFun (τ.toFun p.2)).val :=
      fun hv => hs_ne (Fin.ext hv)
    by_cases htl : (τ.toFun p.1).val < (τ.toFun p.2).val
    · have hnot : ¬ ((τ.toFun p.2).val < (τ.toFun p.1).val) := by omega
      have hphi : φ p = (τ.toFun p.1, τ.toFun p.2) := by
        show ordPair (τ.toFun p.1) (τ.toFun p.2) = _
        unfold ordPair
        simp [htl]
      rw [hphi, decide_eq_false hnot, Bool.xor_false]
    · have htgt : (τ.toFun p.2).val < (τ.toFun p.1).val := by omega
      have hphi : φ p = (τ.toFun p.2, τ.toFun p.1) := by
        show ordPair (τ.toFun p.1) (τ.toFun p.2) = _
        unfold ordPair
        simp [htl]
      rw [hphi, decide_eq_true htgt]
      by_cases hsl : (σ.toFun (τ.toFun p.2)).val < (σ.toFun (τ.toFun p.1)).val
      · have hsnot : ¬ ((σ.toFun (τ.toFun p.1)).val < (σ.toFun (τ.toFun p.2)).val) := by omega
        simp [hsl, hsnot]
      · have hsgt : (σ.toFun (τ.toFun p.1)).val < (σ.toFun (τ.toFun p.2)).val := by omega
        simp [hsl, hsgt]
  unfold parity
  dsimp only [Perm.comp]
  rw [listSum_congr xorMonoid hterm]
  have hadd := listSum_add_fn xorMonoid
    (fun x => decide ((σ.toFun (φ x).2).val < (σ.toFun (φ x).1).val))
    (fun x => decide ((τ.toFun x.2).val < (τ.toFun x.1).val))
    (orderedPairs k)
  change listSum xorMonoid (orderedPairs k)
      (fun x => xorMonoid.add (decide ((σ.toFun (φ x).2).val < (σ.toFun (φ x).1).val))
        (decide ((τ.toFun x.2).val < (τ.toFun x.1).val))) = _
  rw [hadd]
  show xor _ _ = xor _ _
  congr 1
  have hinj_on : ∀ p1 ∈ orderedPairs k, ∀ p2 ∈ orderedPairs k, φ p1 = φ p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 hfeq
    have h1 : p1.1.val < p1.2.val := (mem_orderedPairs p1).mp hp1
    have h2 : p2.1.val < p2.2.val := (mem_orderedPairs p2).mp hp2
    have hfeq' : ordPair (τ.toFun p1.1) (τ.toFun p1.2) =
        ordPair (τ.toFun p2.1) (τ.toFun p2.2) := hfeq
    unfold ordPair at hfeq'
    have hset : (τ.toFun p1.1 = τ.toFun p2.1 ∧ τ.toFun p1.2 = τ.toFun p2.2) ∨
        (τ.toFun p1.1 = τ.toFun p2.2 ∧ τ.toFun p1.2 = τ.toFun p2.1) := by
      split at hfeq' <;> split at hfeq'
      · injection hfeq' with ha hb; exact Or.inl ⟨ha, hb⟩
      · injection hfeq' with ha hb; exact Or.inr ⟨ha, hb⟩
      · injection hfeq' with ha hb; exact Or.inr ⟨hb, ha⟩
      · injection hfeq' with ha hb; exact Or.inl ⟨hb, ha⟩
    cases hset with
    | inl hsame =>
        have e1 := τ.toFun_injective hsame.1
        have e2 := τ.toFun_injective hsame.2
        cases p1; cases p2; simp only [Prod.mk.injEq] at *; exact ⟨e1, e2⟩
    | inr hswap =>
        have e1 := τ.toFun_injective hswap.1
        have e2 := τ.toFun_injective hswap.2
        rw [e1, e2] at h1
        omega
  have hmap_nd : NoDup ((orderedPairs k).map φ) := by
    have haux : ∀ (l : List (Fin k × Fin k)), NoDup l →
        (∀ x ∈ l, x ∈ orderedPairs k) → NoDup (l.map φ) := by
      intro l
      induction l with
      | nil => intro _ _; trivial
      | cons a t ih =>
          rintro ⟨hat, hndt⟩ hsub
          refine ⟨?_, ih hndt (fun x hx => hsub x (List.Mem.tail a hx))⟩
          intro hmem
          rcases List.mem_map.mp hmem with ⟨x, hxt, hfx⟩
          have hxa : x = a :=
            hinj_on x (hsub x (List.Mem.tail a hxt)) a (hsub a (List.Mem.head t)) hfx
          subst hxa
          exact hat hxt
    exact haux (orderedPairs k) (orderedPairs_noDup k) (fun _ hx => hx)
  have hmem_eq : ∀ q, q ∈ (orderedPairs k).map φ ↔ q ∈ orderedPairs k := by
    intro q
    constructor
    · intro hq
      rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
      have hp_lt : p.1.val < p.2.val := (mem_orderedPairs p).mp hp
      have hp_ne : p.1 ≠ p.2 := fun heq => by rw [heq] at hp_lt; exact Nat.lt_irrefl _ hp_lt
      have ht_ne : τ.toFun p.1 ≠ τ.toFun p.2 := fun heq => hp_ne (τ.toFun_injective heq)
      exact (mem_orderedPairs _).mpr (ordPair_lt ht_ne)
    · intro hq
      have hq_lt : q.1.val < q.2.val := (mem_orderedPairs q).mp hq
      have hq_ne : q.1 ≠ q.2 := fun heq => by rw [heq] at hq_lt; exact Nat.lt_irrefl _ hq_lt
      let p0 := ordPair (τ.invFun q.1) (τ.invFun q.2)
      have hinv_ne : τ.invFun q.1 ≠ τ.invFun q.2 :=
        fun heq => hq_ne (τ.inv.toFun_injective heq)
      have hp0_mem : p0 ∈ orderedPairs k := (mem_orderedPairs p0).mpr (ordPair_lt hinv_ne)
      refine List.mem_map.mpr ⟨p0, hp0_mem, ?_⟩
      show ordPair (τ.toFun p0.1) (τ.toFun p0.2) = q
      unfold p0 ordPair
      by_cases hil : (τ.invFun q.1).val < (τ.invFun q.2).val
      · simp only [hil, ↓reduceIte, τ.right_inv, hq_lt]
      · simp only [hil, ↓reduceIte, τ.right_inv]
        have hnotq : ¬ (q.2.val < q.1.val) := by omega
        simp only [hnotq, ↓reduceIte]
  rw [← listSum_map xorMonoid φ (fun p => decide ((σ.toFun p.2).val < (σ.toFun p.1).val))
    (orderedPairs k)]
  exact listSum_nodup_perm xorMonoid
    (fun p => decide ((σ.toFun p.2).val < (σ.toFun p.1).val))
    hmap_nd (orderedPairs_noDup k) hmem_eq

/-- Transposition swapping `p` and `q` in `Fin k`. -/
def swapPerm {k : Nat} (p q : Fin k) : Perm k where
  toFun := fun x => if x = p then q else if x = q then p else x
  invFun := fun x => if x = p then q else if x = q then p else x
  left_inv := by
    intro x
    by_cases hxp : x = p
    · subst hxp; by_cases hpq : x = q <;> simp [hpq]
    · by_cases hxq : x = q
      · subst hxq; simp [hxp]
      · simp [hxp, hxq]
  right_inv := by
    intro x
    by_cases hxp : x = p
    · subst hxp; by_cases hpq : x = q <;> simp [hpq]
    · by_cases hxq : x = q
      · subst hxq; simp [hxp]
      · simp [hxp, hxq]

def adjSwap {k : Nat} (m : Nat) (hm : m + 1 < k) : Perm k :=
  swapPerm ⟨m, by omega⟩ ⟨m + 1, hm⟩

theorem listSum_single_true {α : Type} (a0 : α) :
    ∀ {l : List α} {f : α → Bool}, NoDup l → a0 ∈ l → f a0 = true →
      (∀ x ∈ l, x ≠ a0 → f x = false) → listSum xorMonoid l f = true
  | [], _, _, hmem, _, _ => nomatch hmem
  | a :: t, f, ⟨hat, hndt⟩, hmem, htrue, hfalse => by
      cases List.mem_cons.mp hmem with
      | inl hxa =>
          subst hxa
          have hzero : listSum xorMonoid t f = false := by
            apply listSum_eq_zero xorMonoid
            intro x hxt
            exact hfalse x (List.Mem.tail a0 hxt) (fun heq => by subst heq; exact hat hxt)
          simp only [listSum, htrue, hzero]
          rfl
      | inr hxt =>
          have hfa : f a = false :=
            hfalse a (List.Mem.head t) (fun heq => by subst heq; exact hat hxt)
          have iht := listSum_single_true a0 hndt hxt htrue
            (fun x hx hne => hfalse x (List.Mem.tail a hx) hne)
          simp only [listSum, hfa, iht]
          rfl

@[simp] theorem adjSwap_val {k : Nat} (m : Nat) (hm : m + 1 < k) (x : Fin k) :
    ((adjSwap m hm).toFun x).val =
      if x.val = m then m + 1 else if x.val = m + 1 then m else x.val := by
  dsimp only [adjSwap, swapPerm]
  by_cases h1 : x = ⟨m, by omega⟩
  · have hv : x.val = m := congrArg Fin.val h1
    simp [h1, hv]
  · have hv1 : x.val ≠ m := fun hv => h1 (Fin.ext hv)
    by_cases h2 : x = ⟨m + 1, hm⟩
    · have hv2 : x.val = m + 1 := congrArg Fin.val h2
      simp [h1, h2, hv1, hv2]
    · have hv2 : x.val ≠ m + 1 := fun hv => h2 (Fin.ext hv)
      simp [h1, h2, hv1, hv2]

theorem parity_adjSwap {k : Nat} (m : Nat) (hm : m + 1 < k) :
    parity (adjSwap m hm) = true := by
  let p0 : Fin k × Fin k := (⟨m, by omega⟩, ⟨m + 1, hm⟩)
  have hp0 : p0 ∈ orderedPairs k := (mem_orderedPairs p0).mpr (by simp [p0])
  unfold parity
  apply listSum_single_true p0 (orderedPairs_noDup k) hp0
  · simp [p0, adjSwap_val]
  · intro p hp hnep0
    have hlt : p.1.val < p.2.val := (mem_orderedPairs p).mp hp
    have hval_ne : ¬ (p.1.val = m ∧ p.2.val = m + 1) := by
      intro ⟨h1, h2⟩
      apply hnep0
      cases p with
      | mk a b =>
          simp only [p0, Prod.mk.injEq]
          exact ⟨Fin.ext h1, Fin.ext h2⟩
    have hord : ((adjSwap m hm).toFun p.1).val < ((adjSwap m hm).toFun p.2).val := by
      rw [adjSwap_val, adjSwap_val]
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    exact decide_eq_false (by omega)

@[simp] theorem swapPerm_val {k : Nat} (p q x : Fin k) :
    ((swapPerm p q).toFun x).val =
      if x.val = p.val then q.val else if x.val = q.val then p.val else x.val := by
  dsimp only [swapPerm]
  by_cases h1 : x = p
  · subst h1
    simp
  · have hv1 : x.val ≠ p.val := fun hv => h1 (Fin.ext hv)
    by_cases h2 : x = q
    · subst h2
      simp [h1, hv1]
    · have hv2 : x.val ≠ q.val := fun hv => h2 (Fin.ext hv)
      simp [h1, h2, hv1, hv2]

theorem parity_swap_lt {k : Nat} :
    ∀ (d : Nat) (p q : Fin k), p.val < q.val → q.val - p.val - 1 = d →
      parity (swapPerm p q) = true
  | 0, p, q, hpq, hd => by
      have hq : q.val = p.val + 1 := by omega
      have hlt : p.val + 1 < k := by have := q.isLt; omega
      have heq : swapPerm p q = adjSwap p.val hlt := by
        unfold adjSwap
        congr 1
        exact Fin.ext hq
      rw [heq]
      exact parity_adjSwap p.val hlt
  | d + 1, p, q, hpq, hd => by
      have hqlt := q.isLt
      let r : Fin k := ⟨q.val - 1, by omega⟩
      have hrv : r.val = q.val - 1 := rfl
      have hpr : p.val < r.val := by omega
      have hr1 : r.val + 1 < k := by omega
      have hconj : swapPerm p q =
          Perm.comp (adjSwap r.val hr1) (Perm.comp (swapPerm p r) (adjSwap r.val hr1)) := by
        apply Perm.ext
        intro x
        apply Fin.ext
        dsimp only [Perm.comp]
        rw [swapPerm_val, adjSwap_val, swapPerm_val, adjSwap_val]
        split <;> (try split) <;> (try split) <;> (try split) <;>
          (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
      rw [hconj, parity_comp, parity_comp, parity_adjSwap]
      have ih := parity_swap_lt d p r hpr (by omega)
      rw [ih]
      rfl

/-- Every transposition `(p q)` (`p ≠ q`) has odd parity (`parity = true`). -/
theorem parity_swap {k : Nat} {p q : Fin k} (hne : p ≠ q) :
    parity (swapPerm p q) = true := by
  have hv : p.val ≠ q.val := fun h => hne (Fin.ext h)
  cases Nat.lt_or_gt_of_ne hv with
  | inl hlt => exact parity_swap_lt (q.val - p.val - 1) p q hlt rfl
  | inr hgt =>
      have hsym : swapPerm p q = swapPerm q p := by
        apply Perm.ext
        intro x
        apply Fin.ext
        rw [swapPerm_val, swapPerm_val]
        split <;> (try split) <;> (try split) <;> omega
      rw [hsym]
      exact parity_swap_lt (p.val - q.val - 1) q p hgt rfl

/-! ## 4. Commutative Rings, Tensor Powers `T^k(R^n)`, and Full Antisymmetrization `Alt_k` -/

structure CommRingOps (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

def CommRingOps.toAddMonoid {R : Type} (cr : CommRingOps R) : CommMonoidOps R where
  zero := cr.zero
  add := cr.add
  add_assoc := cr.add_assoc
  add_comm := cr.add_comm
  zero_add := cr.zero_add

theorem cr_add_zero {R : Type} (cr : CommRingOps R) (a : R) : cr.add a cr.zero = a := by
  rw [cr.add_comm, cr.zero_add]

theorem cr_neg_add {R : Type} (cr : CommRingOps R) (a : R) : cr.add (cr.neg a) a = cr.zero := by
  rw [cr.add_comm, cr.add_neg]

theorem cr_add_left_cancel {R : Type} (cr : CommRingOps R) {a b c : R}
    (h : cr.add a b = cr.add a c) : b = c := by
  calc
    b = cr.add cr.zero b := (cr.zero_add b).symm
    _ = cr.add (cr.add (cr.neg a) a) b := by rw [cr_neg_add]
    _ = cr.add (cr.neg a) (cr.add a b) := cr.add_assoc _ _ _
    _ = cr.add (cr.neg a) (cr.add a c) := by rw [h]
    _ = cr.add (cr.add (cr.neg a) a) c := (cr.add_assoc _ _ _).symm
    _ = cr.add cr.zero c := by rw [cr_neg_add]
    _ = c := cr.zero_add c

theorem cr_neg_zero {R : Type} (cr : CommRingOps R) : cr.neg cr.zero = cr.zero := by
  apply cr_add_left_cancel cr (a := cr.zero)
  rw [cr.add_neg, cr.zero_add]

theorem cr_neg_neg {R : Type} (cr : CommRingOps R) (a : R) : cr.neg (cr.neg a) = a := by
  apply cr_add_left_cancel cr (a := cr.neg a)
  rw [cr.add_neg, cr_neg_add]

theorem cr_neg_add_distrib {R : Type} (cr : CommRingOps R) (a b : R) :
    cr.neg (cr.add a b) = cr.add (cr.neg a) (cr.neg b) := by
  apply cr_add_left_cancel cr (a := cr.add a b)
  rw [cr.add_neg]
  calc
    cr.zero = cr.add a (cr.neg a) := (cr.add_neg a).symm
    _ = cr.add a (cr.add cr.zero (cr.neg a)) := by rw [cr.zero_add]
    _ = cr.add a (cr.add (cr.add b (cr.neg b)) (cr.neg a)) := by rw [cr.add_neg b]
    _ = cr.add a (cr.add b (cr.add (cr.neg b) (cr.neg a))) := by rw [cr.add_assoc b]
    _ = cr.add (cr.add a b) (cr.add (cr.neg a) (cr.neg b)) := by
          rw [← cr.add_assoc a b, cr.add_comm (cr.neg b) (cr.neg a)]

theorem cr_mul_zero {R : Type} (cr : CommRingOps R) (a : R) : cr.mul a cr.zero = cr.zero := by
  apply cr_add_left_cancel cr (a := cr.mul a cr.zero)
  rw [← cr.left_distrib, cr.zero_add, cr_add_zero]

theorem cr_zero_mul {R : Type} (cr : CommRingOps R) (a : R) : cr.mul cr.zero a = cr.zero := by
  rw [cr.mul_comm, cr_mul_zero]

theorem cr_right_distrib {R : Type} (cr : CommRingOps R) (a b c : R) :
    cr.mul (cr.add a b) c = cr.add (cr.mul a c) (cr.mul b c) := by
  rw [cr.mul_comm, cr.left_distrib, cr.mul_comm c a, cr.mul_comm c b]

theorem cr_mul_neg {R : Type} (cr : CommRingOps R) (a b : R) :
    cr.mul a (cr.neg b) = cr.neg (cr.mul a b) := by
  apply cr_add_left_cancel cr (a := cr.mul a b)
  rw [← cr.left_distrib, cr.add_neg, cr_mul_zero, cr.add_neg]

theorem cr_neg_mul {R : Type} (cr : CommRingOps R) (a b : R) :
    cr.mul (cr.neg a) b = cr.neg (cr.mul a b) := by
  rw [cr.mul_comm, cr_mul_neg, cr.mul_comm]

def natCast {R : Type} (cr : CommRingOps R) : Nat → R
  | 0 => cr.zero
  | m + 1 => cr.add (natCast cr m) cr.one

theorem natCast_add {R : Type} (cr : CommRingOps R) (a : Nat) :
    ∀ b : Nat, natCast cr (a + b) = cr.add (natCast cr a) (natCast cr b)
  | 0 => by simp [natCast, cr_add_zero]
  | b + 1 => by simp [Nat.add_succ, natCast, natCast_add cr a b, cr.add_assoc]

theorem natCast_mul {R : Type} (cr : CommRingOps R) (a : Nat) :
    ∀ b : Nat, natCast cr (a * b) = cr.mul (natCast cr a) (natCast cr b)
  | 0 => by simp [natCast, cr_mul_zero]
  | b + 1 => by
      rw [Nat.mul_succ, natCast_add, natCast, cr.left_distrib, natCast_mul cr a b,
        cr.mul_comm _ cr.one, cr.one_mul]

/-- Sign action `±x` of `b : Bool` (`false ↦ +x`, `true ↦ -x`). -/
def sgnVal {R : Type} (cr : CommRingOps R) (b : Bool) (x : R) : R :=
  if b then cr.neg x else x

theorem sgnVal_xor {R : Type} (cr : CommRingOps R) (b1 b2 : Bool) (x : R) :
    sgnVal cr (xor b1 b2) x = sgnVal cr b1 (sgnVal cr b2 x) := by
  cases b1 <;> cases b2 <;> simp [sgnVal, cr_neg_neg]

theorem sgnVal_self {R : Type} (cr : CommRingOps R) (b : Bool) (x : R) :
    sgnVal cr b (sgnVal cr b x) = x := by
  rw [← sgnVal_xor, Bool.xor_self]
  rfl

theorem sgnVal_add {R : Type} (cr : CommRingOps R) (b : Bool) (x y : R) :
    sgnVal cr b (cr.add x y) = cr.add (sgnVal cr b x) (sgnVal cr b y) := by
  cases b <;> simp [sgnVal, cr_neg_add_distrib]

theorem sgnVal_mul_right {R : Type} (cr : CommRingOps R) (b : Bool) (c x : R) :
    cr.mul c (sgnVal cr b x) = sgnVal cr b (cr.mul c x) := by
  cases b <;> simp [sgnVal, cr_mul_neg]

theorem listSum_sgnVal {α R : Type} (cr : CommRingOps R) (b : Bool) (f : α → R) :
    ∀ (l : List α),
      listSum cr.toAddMonoid l (fun x => sgnVal cr b (f x)) =
        sgnVal cr b (listSum cr.toAddMonoid l f)
  | [] => by
      cases b
      · rfl
      · exact (cr_neg_zero cr).symm
  | a :: t => by
      simp only [listSum]
      change cr.add (sgnVal cr b (f a))
          (listSum cr.toAddMonoid t (fun x => sgnVal cr b (f x))) =
        sgnVal cr b (cr.add (f a) (listSum cr.toAddMonoid t f))
      rw [listSum_sgnVal cr b f t, sgnVal_add]

theorem listSum_mul {α R : Type} (cr : CommRingOps R) (c : R) (f : α → R) :
    ∀ (l : List α),
      listSum cr.toAddMonoid l (fun x => cr.mul c (f x)) =
        cr.mul c (listSum cr.toAddMonoid l f)
  | [] => (cr_mul_zero cr c).symm
  | a :: t => by
      simp only [listSum]
      change cr.add (cr.mul c (f a)) (listSum cr.toAddMonoid t (fun x => cr.mul c (f x))) =
        cr.mul c (cr.add (f a) (listSum cr.toAddMonoid t f))
      rw [listSum_mul cr c f t, cr.left_distrib]

theorem listSum_const {α R : Type} (cr : CommRingOps R) (x : R) :
    ∀ (l : List α), listSum cr.toAddMonoid l (fun _ => x) = cr.mul (natCast cr l.length) x
  | [] => (cr_zero_mul cr x).symm
  | _ :: t => by
      simp only [List.length_cons, listSum, natCast]
      change cr.add x (listSum cr.toAddMonoid t (fun _ => x)) =
        cr.mul (cr.add (natCast cr t.length) cr.one) x
      rw [listSum_const cr x t, cr_right_distrib, cr.one_mul, cr.add_comm]

theorem listSum_cancel_neg {α R : Type} (cr : CommRingOps R) (f : α → R) :
    ∀ (l : List α),
      cr.add (listSum cr.toAddMonoid l f) (listSum cr.toAddMonoid l (fun x => cr.neg (f x))) =
        cr.zero
  | [] => cr.zero_add cr.zero
  | a :: t => by
      change cr.toAddMonoid.add (listSum cr.toAddMonoid (a :: t) f)
          (listSum cr.toAddMonoid (a :: t) (fun x => cr.neg (f x))) = cr.toAddMonoid.zero
      rw [← listSum_add_fn cr.toAddMonoid f (fun x => cr.neg (f x)) (a :: t)]
      apply listSum_eq_zero cr.toAddMonoid
      intro x _
      exact cr.add_neg (f x)

/-- Coordinate model of the `k`-th tensor power `T^k(R^n) ≅ ((Fin k → Fin n) → R)`. -/
abbrev Tensor (R : Type) (n k : Nat) : Type := (Fin k → Fin n) → R

def zeroTensor {R : Type} (cr : CommRingOps R) {n k : Nat} : Tensor R n k :=
  fun _ => cr.zero

def smulTensor {R : Type} (cr : CommRingOps R) {n k : Nat} (c : R) (T : Tensor R n k) :
    Tensor R n k :=
  fun I => cr.mul c (T I)

def sgnTensor {R : Type} (cr : CommRingOps R) {n k : Nat} (b : Bool) (T : Tensor R n k) :
    Tensor R n k :=
  fun I => sgnVal cr b (T I)

/-- Left action of `S_k` on `T^k(R^n)`: `(σ · T)(I) = T(I ∘ σ)`. -/
def actTensor {R : Type} {n k : Nat} (σ : Perm k) (T : Tensor R n k) : Tensor R n k :=
  fun I => T (fun r => I (σ.toFun r))

theorem actTensor_comp {R : Type} {n k : Nat} (σ τ : Perm k) (T : Tensor R n k) :
    actTensor σ (actTensor τ T) = actTensor (Perm.comp σ τ) T :=
  rfl

/-- Standard coordinate basis tensor `E_I` (`E_I(J) = 1` iff `J = I`, else `0`). -/
def basisTensor {R : Type} (cr : CommRingOps R) {n k : Nat} (I : Fin k → Fin n) :
    Tensor R n k :=
  fun J => if vecEq J I then cr.one else cr.zero

/-- The fully antisymmetric (`S_k`-sign-equivariant) subspace `A^k_sgn(R^n)`. -/
def IsAntisym {R : Type} (cr : CommRingOps R) {n k : Nat} (T : Tensor R n k) : Prop :=
  ∀ σ : Perm k, actTensor σ T = sgnTensor cr (parity σ) T

/-- Unnormalized full antisymmetrizer `Alt_k(T) = ∑_{σ ∈ S_k} sgn(σ) (σ · T)`. -/
def alt {R : Type} (cr : CommRingOps R) {n k : Nat} (T : Tensor R n k) : Tensor R n k :=
  fun I =>
    listSum cr.toAddMonoid (allPerms k)
      (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r))))

/-- Normalized full antisymmetrizer `Π_k(T) = u · Alt_k(T)` where `u = (k!)⁻¹`. -/
def normAlt {R : Type} (cr : CommRingOps R) {n k : Nat} (u : R) (T : Tensor R n k) :
    Tensor R n k :=
  smulTensor cr u (alt cr T)

/-! ## 5. Universal Algebraic Identities of `Alt_k` and Positive Realization Theorem -/

/-- Reindexing sum over `allPerms k` by left multiplication `τ ∘ ·`. -/
theorem sum_allPerms_left_mul {R : Type} (cr : CommRingOps R) {k : Nat} (τ : Perm k)
    (F : Perm k → R) :
    listSum cr.toAddMonoid (allPerms k) (fun σ => F (Perm.comp τ σ)) =
      listSum cr.toAddMonoid (allPerms k) F := by
  rw [← listSum_map cr.toAddMonoid (Perm.comp τ) F (allPerms k)]
  have hinj : ∀ s1 s2 : Perm k, Perm.comp τ s1 = Perm.comp τ s2 → s1 = s2 := by
    intro s1 s2 heq
    calc
      s1 = Perm.comp (Perm.id k) s1 := rfl
      _ = Perm.comp (Perm.comp τ.inv τ) s1 := by rw [Perm.inv_comp]
      _ = Perm.comp τ.inv (Perm.comp τ s1) := Perm.comp_assoc _ _ _
      _ = Perm.comp τ.inv (Perm.comp τ s2) := by rw [heq]
      _ = Perm.comp (Perm.comp τ.inv τ) s2 := (Perm.comp_assoc _ _ _).symm
      _ = s2 := by rw [Perm.inv_comp]; rfl
  have hnd : NoDup ((allPerms k).map (Perm.comp τ)) :=
    noDup_map_of_inj (Perm.comp τ) hinj (allPerms_noDup k)
  have hmem : ∀ ρ : Perm k, ρ ∈ (allPerms k).map (Perm.comp τ) ↔ ρ ∈ allPerms k := by
    intro ρ
    constructor
    · intro _; exact allPerms_mem ρ
    · intro _
      refine List.mem_map.mpr ⟨Perm.comp τ.inv ρ, allPerms_mem _, ?_⟩
      rw [← Perm.comp_assoc, Perm.comp_inv]
      rfl
  exact listSum_nodup_perm cr.toAddMonoid F hnd (allPerms_noDup k) hmem

/-- Skew-equivariance: for all `T`, `Alt_k(T)` lies in `A^k_sgn(R^n)`. -/
theorem alt_isAntisym {R : Type} (cr : CommRingOps R) {n k : Nat} (T : Tensor R n k) :
    IsAntisym cr (alt cr T) := by
  intro τ
  funext I
  unfold actTensor alt sgnTensor
  have hre :
      listSum cr.toAddMonoid (allPerms k)
          (fun σ => sgnVal cr (parity σ) (T (fun r => I (τ.toFun (σ.toFun r))))) =
        listSum cr.toAddMonoid (allPerms k)
          (fun σ =>
            sgnVal cr (parity τ)
              (sgnVal cr (parity (Perm.comp τ σ)) (T (fun r => I ((Perm.comp τ σ).toFun r))))) := by
    apply listSum_congr cr.toAddMonoid
    intro σ _
    rw [parity_comp τ σ, ← sgnVal_xor]
    have hxor : xor (parity τ) (xor (parity τ) (parity σ)) = parity σ := by
      rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    rw [hxor]
    rfl
  rw [hre, listSum_sgnVal cr (parity τ)]
  congr 1
  exact sum_allPerms_left_mul cr τ
    (fun ρ => sgnVal cr (parity ρ) (T (fun r => I (ρ.toFun r))))

/-- Action on already-antisymmetric tensors: `T ∈ A^k_sgn(R^n) ⟹ Alt_k(T) = k! · T`. -/
theorem alt_of_isAntisym {R : Type} (cr : CommRingOps R) {n k : Nat} {T : Tensor R n k}
    (hT : IsAntisym cr T) :
    alt cr T = smulTensor cr (natCast cr (factorial k)) T := by
  funext I
  unfold alt smulTensor
  have hcongr :
      listSum cr.toAddMonoid (allPerms k)
          (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r)))) =
        listSum cr.toAddMonoid (allPerms k) (fun _ => T I) := by
    apply listSum_congr cr.toAddMonoid
    intro σ _
    have hact : T (fun r => I (σ.toFun r)) = sgnVal cr (parity σ) (T I) :=
      congrFun (hT σ) I
    rw [hact, sgnVal_self]
  rw [hcongr, listSum_const cr (T I) (allPerms k), allPerms_length]

/-- Universal Factorial Scaling Law over ANY commutative ring: `Alt_k(Alt_k(T)) = k! · Alt_k(T)`. -/
theorem alt_idem_scaled {R : Type} (cr : CommRingOps R) {n k : Nat} (T : Tensor R n k) :
    alt cr (alt cr T) = smulTensor cr (natCast cr (factorial k)) (alt cr T) :=
  alt_of_isAntisym cr (alt_isAntisym cr T)

theorem alt_smul {R : Type} (cr : CommRingOps R) {n k : Nat} (c : R) (T : Tensor R n k) :
    alt cr (smulTensor cr c T) = smulTensor cr c (alt cr T) := by
  funext I
  unfold alt smulTensor
  rw [← listSum_mul cr c]
  apply listSum_congr cr.toAddMonoid
  intro σ _
  exact (sgnVal_mul_right cr (parity σ) c _).symm

/-- Positive Realization Theorem (Part 1 — Idempotent Projection):
    When `u * (k! : R) = 1`, `Π_k = u · Alt_k` is an idempotent projection onto `A^k_sgn(R^n)`. -/
theorem normAlt_idem {R : Type} (cr : CommRingOps R) {n k : Nat} {u : R}
    (hu : cr.mul u (natCast cr (factorial k)) = cr.one) (T : Tensor R n k) :
    normAlt cr u (normAlt cr u T) = normAlt cr u T := by
  unfold normAlt
  rw [alt_smul, alt_idem_scaled]
  funext I
  unfold smulTensor
  calc
    cr.mul u (cr.mul u (cr.mul (natCast cr (factorial k)) (alt cr T I)))
        = cr.mul u (cr.mul (cr.mul u (natCast cr (factorial k))) (alt cr T I)) := by
            rw [← cr.mul_assoc u (natCast cr (factorial k))]
    _ = cr.mul u (cr.mul cr.one (alt cr T I)) := by rw [hu]
    _ = cr.mul u (alt cr T I) := by rw [cr.one_mul]

theorem normAlt_isAntisym {R : Type} (cr : CommRingOps R) {n k : Nat} (u : R)
    (T : Tensor R n k) : IsAntisym cr (normAlt cr u T) := by
  intro σ
  funext I
  unfold normAlt smulTensor actTensor sgnTensor
  dsimp only
  have h := congrFun (alt_isAntisym cr T σ) I
  unfold actTensor sgnTensor at h
  rw [h, sgnVal_mul_right]

/-- Exact characterization of the image of `Π_k`: `T ∈ A^k_sgn(R^n) ↔ Π_k(T) = T`. -/
theorem isAntisym_iff_normAlt_eq {R : Type} (cr : CommRingOps R) {n k : Nat} {u : R}
    (hu : cr.mul u (natCast cr (factorial k)) = cr.one) (T : Tensor R n k) :
    IsAntisym cr T ↔ normAlt cr u T = T := by
  constructor
  · intro hT
    unfold normAlt
    rw [alt_of_isAntisym cr hT]
    funext I
    unfold smulTensor
    rw [← cr.mul_assoc, hu, cr.one_mul]
  · intro hfix
    rw [← hfix]
    exact normAlt_isAntisym cr u T

/-! ## 6. Exact Binomial-Zero Vanishing Above `n` and Coordinate Duality Below/At `n` -/

/-- Repeated-slot sign cancellation: if `p ≠ q` and `I p = I q`, `Alt_k(T)(I) = 0`
    over EVERY commutative ring `R` (including characteristic `2`). -/
theorem alt_apply_of_repeat {R : Type} (cr : CommRingOps R) {n k : Nat} (T : Tensor R n k)
    {I : Fin k → Fin n} {p q : Fin k} (hne : p ≠ q) (hrep : I p = I q) :
    alt cr T I = cr.zero := by
  let τ := swapPerm p q
  have hpar_τ : parity τ = true := parity_swap hne
  have hIτ : ∀ r : Fin k, I (τ.toFun r) = I r := by
    intro r
    dsimp only [τ, swapPerm]
    by_cases hrp : r = p
    · subst hrp; simp [hrep]
    · by_cases hrq : r = q
      · subst hrq; simp [hrp, hrep]
      · simp [hrp, hrq]
  let evens := (allPerms k).filter (fun σ => !parity σ)
  let odds := (allPerms k).filter (fun σ => parity σ)
  unfold alt
  rw [listSum_filter_split cr.toAddMonoid (fun σ => parity σ) _ (allPerms k)]
  have hinj : ∀ s1 s2 : Perm k, Perm.comp τ s1 = Perm.comp τ s2 → s1 = s2 := by
    intro s1 s2 heq
    calc
      s1 = Perm.comp (Perm.comp τ.inv τ) s1 := by rw [Perm.inv_comp]; rfl
      _ = Perm.comp τ.inv (Perm.comp τ s1) := Perm.comp_assoc _ _ _
      _ = Perm.comp τ.inv (Perm.comp τ s2) := by rw [heq]
      _ = Perm.comp (Perm.comp τ.inv τ) s2 := (Perm.comp_assoc _ _ _).symm
      _ = s2 := by rw [Perm.inv_comp]; rfl
  have hnd_map : NoDup (evens.map (Perm.comp τ)) :=
    noDup_map_of_inj (Perm.comp τ) hinj (noDup_filter _ (allPerms_noDup k))
  have hnd_odds : NoDup odds := noDup_filter _ (allPerms_noDup k)
  have hmem : ∀ ρ : Perm k, ρ ∈ evens.map (Perm.comp τ) ↔ ρ ∈ odds := by
    intro ρ
    constructor
    · intro hρ
      rcases List.mem_map.mp hρ with ⟨σ, hσ, rfl⟩
      have hσ_ev : (!parity σ) = true := (List.mem_filter.mp hσ).2
      have hσ_f : parity σ = false := by revert hσ_ev; cases parity σ <;> decide
      exact List.mem_filter.mpr ⟨allPerms_mem _, by rw [parity_comp, hpar_τ, hσ_f]; rfl⟩
    · intro hρ
      have hρ_odd : parity ρ = true := (List.mem_filter.mp hρ).2
      let σ := Perm.comp τ.inv ρ
      have hτinv : parity τ.inv = true := by
        have h1 := parity_comp τ.inv τ
        rw [Perm.inv_comp, parity_id, hpar_τ] at h1
        revert h1; cases parity τ.inv <;> decide
      have hσ_mem : σ ∈ evens := by
        refine List.mem_filter.mpr ⟨allPerms_mem σ, ?_⟩
        simp [σ, parity_comp, hτinv, hρ_odd]
      refine List.mem_map.mpr ⟨σ, hσ_mem, ?_⟩
      simp only [σ, ← Perm.comp_assoc, Perm.comp_inv]
      rfl
  have hodd_eq :
      listSum cr.toAddMonoid odds
          (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r)))) =
        listSum cr.toAddMonoid evens
          (fun σ => cr.neg (T (fun r => I (σ.toFun r)))) := by
    rw [← listSum_nodup_perm cr.toAddMonoid _ hnd_map hnd_odds hmem,
      listSum_map cr.toAddMonoid (Perm.comp τ)]
    apply listSum_congr cr.toAddMonoid
    intro σ hσ
    have hσ_ev : (!parity σ) = true := (List.mem_filter.mp hσ).2
    have hσ_f : parity σ = false := by revert hσ_ev; cases parity σ <;> decide
    have hcomp_t : parity (Perm.comp τ σ) = true := by rw [parity_comp, hpar_τ, hσ_f]; rfl
    have hfun : (fun r => I ((Perm.comp τ σ).toFun r)) = (fun r => I (σ.toFun r)) := by
      funext r
      exact hIτ (σ.toFun r)
    rw [hcomp_t, hfun]
    rfl
  have hev_eq :
      listSum cr.toAddMonoid evens
          (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r)))) =
        listSum cr.toAddMonoid evens (fun σ => T (fun r => I (σ.toFun r))) := by
    apply listSum_congr cr.toAddMonoid
    intro σ hσ
    have hσ_ev : (!parity σ) = true := (List.mem_filter.mp hσ).2
    have hσ_f : parity σ = false := by revert hσ_ev; cases parity σ <;> decide
    rw [hσ_f]
    rfl
  show cr.add
      (listSum cr.toAddMonoid evens
        (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r)))))
      (listSum cr.toAddMonoid odds
        (fun σ => sgnVal cr (parity σ) (T (fun r => I (σ.toFun r))))) = cr.zero
  rw [hev_eq, hodd_eq]
  exact listSum_cancel_neg cr (fun σ => T (fun r => I (σ.toFun r))) evens

/-- Pigeonhole Vanishing Above the Threshold (`n < k ⟺ choose n k = 0`):
    `Alt_k` vanishes identically on `T^k(R^n)` for every `n < k` and every `R`. -/
theorem alt_vanishes_of_lt {R : Type} (cr : CommRingOps R) {n k : Nat} (h : n < k)
    (T : Tensor R n k) : alt cr T = zeroTensor cr := by
  funext I
  rcases pigeonhole_fin h I with ⟨p, q, hne, hpq⟩
  exact alt_apply_of_repeat cr T hne hpq

/-- When `n < k` and `k!` is invertible in `R`, the fully antisymmetric subspace
    `A^k_sgn(R^n)` vanishes (`T ∈ A^k_sgn(R^n) ↔ T = 0`). -/
theorem antisym_vanishes_of_lt {R : Type} (cr : CommRingOps R) {n k : Nat} {u : R}
    (hu : cr.mul u (natCast cr (factorial k)) = cr.one) (h : n < k) (T : Tensor R n k) :
    IsAntisym cr T ↔ T = zeroTensor cr := by
  rw [isAntisym_iff_normAlt_eq cr hu]
  unfold normAlt
  rw [alt_vanishes_of_lt cr h T]
  have hz : smulTensor cr u (zeroTensor cr (n := n) (k := k)) = zeroTensor cr := by
    funext _; exact cr_mul_zero cr u
  rw [hz]
  exact ⟨Eq.symm, Eq.symm⟩

/-- Strictly monotone maps `Fin k → Fin k` are equal to the identity. -/
theorem strictMonoFin_self_eq_id {k : Nat} {f : Fin k → Fin k} (hf : StrictMonoFin f) :
    ∀ r : Fin k, f r = r := by
  have hlow : ∀ (m : Nat) (hm : m < k), m ≤ (f ⟨m, hm⟩).val := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hstep := hf ⟨m, by omega⟩ ⟨m + 1, hm⟩ (Nat.lt_succ_self m)
        omega
  have hhigh : ∀ (d m : Nat) (hm : m < k), m + d + 1 = k → (f ⟨m, hm⟩).val ≤ m := by
    intro d
    induction d with
    | zero =>
        intro m hm hsum
        have hlt := (f ⟨m, hm⟩).isLt
        omega
    | succ d ih =>
        intro m hm hsum
        have hm1 : m + 1 < k := by omega
        have hnext := ih (m + 1) hm1 (by omega)
        have hstep := hf ⟨m, hm⟩ ⟨m + 1, hm1⟩ (Nat.lt_succ_self m)
        omega
  intro r
  apply Fin.ext
  have h1 : r.val ≤ (f r).val := hlow r.val r.isLt
  have h2 : (f r).val ≤ r.val := hhigh (k - 1 - r.val) r.val r.isLt (by have := r.isLt; omega)
  omega

theorem listSum_single_elem {α R : Type} (cr : CommRingOps R) (a0 : α) (val : R) :
    ∀ {l : List α} {f : α → R}, NoDup l → a0 ∈ l → f a0 = val →
      (∀ x ∈ l, x ≠ a0 → f x = cr.zero) → listSum cr.toAddMonoid l f = val
  | [], _, _, hmem, _, _ => nomatch hmem
  | a :: t, f, ⟨hat, hndt⟩, hmem, hval, hzero => by
      cases List.mem_cons.mp hmem with
      | inl hxa =>
          subst hxa
          have htz : listSum cr.toAddMonoid t f = cr.zero :=
            listSum_eq_zero cr.toAddMonoid
              (fun x hxt => hzero x (List.Mem.tail a0 hxt) (fun heq => by subst heq; exact hat hxt))
          simp only [listSum]
          change cr.add (f a0) (listSum cr.toAddMonoid t f) = val
          rw [hval, htz, cr_add_zero]
      | inr hxt =>
          have hfa : f a = cr.zero :=
            hzero a (List.Mem.head t) (fun heq => by subst heq; exact hat hxt)
          have iht := listSum_single_elem cr a0 val hndt hxt hval
            (fun x hx hne => hzero x (List.Mem.tail a hx) hne)
          simp only [listSum]
          change cr.add (f a) (listSum cr.toAddMonoid t f) = val
          rw [hfa, iht, cr.zero_add]

/-- Exact Coordinate Duality on Strictly Monotone Multi-Indices (`I, J : Fin k → Fin n`):
    `Alt_k(E_I)(J) = 1` if `J = I`, and `0` if `J ≠ I`. -/
theorem alt_basis_duality {R : Type} (cr : CommRingOps R) {n k : Nat}
    {I J : Fin k → Fin n} (hI : StrictMonoFin I) (hJ : StrictMonoFin J) :
    alt cr (basisTensor cr I) J = if vecEq J I then cr.one else cr.zero := by
  have hkey : ∀ σ : Perm k, (fun r => J (σ.toFun r)) = I ↔ σ = Perm.id k ∧ J = I := by
    intro σ
    constructor
    · intro heq
      have hmonoσ : StrictMonoFin σ.toFun := by
        intro a b hab
        have hIab : (I a).val < (I b).val := hI a b hab
        have h1 : J (σ.toFun a) = I a := congrFun heq a
        have h2 : J (σ.toFun b) = I b := congrFun heq b
        rw [← h1, ← h2] at hIab
        cases Nat.lt_or_ge (σ.toFun a).val (σ.toFun b).val with
        | inl hlt => exact hlt
        | inr hge =>
            cases Nat.eq_or_lt_of_le hge with
            | inl hev =>
                have hs : σ.toFun a = σ.toFun b := Fin.ext hev.symm
                rw [hs] at hIab
                exact absurd hIab (Nat.lt_irrefl _)
            | inr hgt =>
                have hJba := hJ (σ.toFun b) (σ.toFun a) hgt
                omega
      have hσid : σ = Perm.id k := Perm.ext (strictMonoFin_self_eq_id hmonoσ)
      subst hσid
      exact ⟨rfl, heq⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  by_cases hJI : vecEq J I = true
  · have heqJI : J = I := (vecEq_iff J I).mp hJI
    subst heqJI
    rw [if_pos hJI]
    unfold alt
    apply listSum_single_elem cr (Perm.id k) cr.one (allPerms_noDup k) (allPerms_mem _)
    · rw [parity_id]
      dsimp only [Perm.id]
      simp [sgnVal, basisTensor, hJI]
    · intro σ _ hne
      have hnot : vecEq (fun r => J (σ.toFun r)) J = false := by
        cases hv : vecEq (fun r => J (σ.toFun r)) J with
        | false => rfl
        | true =>
            have h1 := (hkey σ).mp ((vecEq_iff _ _).mp hv)
            exact False.elim (hne h1.1)
      simp only [basisTensor, hnot]
      cases parity σ
      · rfl
      · exact cr_neg_zero cr
  · rw [if_neg hJI]
    have hneJI : J ≠ I := fun heq => hJI ((vecEq_iff J I).mpr heq)
    unfold alt
    apply listSum_eq_zero cr.toAddMonoid
    intro σ _
    have hnot : vecEq (fun r => J (σ.toFun r)) I = false := by
      cases hv : vecEq (fun r => J (σ.toFun r)) I with
      | false => rfl
      | true =>
          have h1 := (hkey σ).mp ((vecEq_iff _ _).mp hv)
          exact False.elim (hneJI h1.2)
    simp only [basisTensor, hnot]
    cases parity σ
    · rfl
    · exact cr_neg_zero cr

/-- Canonical rising multi-index `0 < 1 < ... < k - 1` in `Fin n` whenever `k ≤ n`. -/
def canonicalMono {n k : Nat} (h : k ≤ n) : Fin k → Fin n :=
  fun r => ⟨r.val, Nat.lt_of_lt_of_le r.isLt h⟩

theorem canonicalMono_strict {n k : Nat} (h : k ≤ n) : StrictMonoFin (canonicalMono h) :=
  fun _ _ hab => hab

/-- Non-vanishing of `Alt_k` below and at the threshold (`k ≤ n`) over any non-trivial ring. -/
theorem alt_nonvanishing_of_le {R : Type} (cr : CommRingOps R) (hone : cr.one ≠ cr.zero)
    {n k : Nat} (h : k ≤ n) :
    ∃ T : Tensor R n k, alt cr T ≠ zeroTensor cr := by
  let I0 := canonicalMono h
  refine ⟨basisTensor cr I0, ?_⟩
  intro hz
  have heval : alt cr (basisTensor cr I0) I0 = cr.zero := congrFun hz I0
  rw [alt_basis_duality cr (canonicalMono_strict h) (canonicalMono_strict h)] at heval
  have hself : vecEq I0 I0 = true := (vecEq_iff I0 I0).mpr rfl
  rw [if_pos hself] at heval
  exact hone heval

/-- Exact Positive Binomial-Zero Threshold Master Theorem (Characteristic-0 / Invertible `k!`):
    Over any non-trivial commutative ring `R` (`1 ≠ 0`) in which `k!` has an inverse `u`,
    the normalized antisymmetrizer `Π_k = u · Alt_k` and the fully antisymmetric subspace
    `A^k_sgn(R^n)` vanish identically **if and only if** `choose n k = 0` (`n < k`). -/
theorem positive_binomial_threshold_master {R : Type} (cr : CommRingOps R)
    (hone : cr.one ≠ cr.zero) {n k : Nat} {u : R}
    (hu : cr.mul u (natCast cr (factorial k)) = cr.one) :
    ((∀ T : Tensor R n k, normAlt cr u T = zeroTensor cr) ↔ choose n k = 0) ∧
    ((∀ T : Tensor R n k, IsAntisym cr T → T = zeroTensor cr) ↔ choose n k = 0) := by
  have hunz : u ≠ cr.zero := by
    intro huz
    rw [huz, cr_zero_mul] at hu
    exact hone hu.symm
  constructor
  · rw [choose_eq_zero_iff]
    constructor
    · intro hall
      cases Nat.lt_or_ge n k with
      | inl hlt => exact hlt
      | inr hge =>
          let I0 := canonicalMono hge
          have hval : alt cr (basisTensor cr I0) I0 = cr.one := by
            rw [alt_basis_duality cr (canonicalMono_strict hge) (canonicalMono_strict hge),
              if_pos ((vecEq_iff I0 I0).mpr rfl)]
          have hnorm0 : normAlt cr u (basisTensor cr I0) I0 = cr.zero :=
            congrFun (hall (basisTensor cr I0)) I0
          unfold normAlt smulTensor at hnorm0
          rw [hval, cr.mul_comm, cr.one_mul] at hnorm0
          exact False.elim (hunz hnorm0)
    · intro hlt T
      unfold normAlt
      rw [alt_vanishes_of_lt cr hlt T]
      funext _; exact cr_mul_zero cr u
  · rw [choose_eq_zero_iff]
    constructor
    · intro hall
      cases Nat.lt_or_ge n k with
      | inl hlt => exact hlt
      | inr hge =>
          let I0 := canonicalMono hge
          let W := normAlt cr u (basisTensor cr I0)
          have hW : IsAntisym cr W := normAlt_isAntisym cr u (basisTensor cr I0)
          have hW0 : W I0 = cr.zero := congrFun (hall W hW) I0
          unfold W normAlt smulTensor at hW0
          rw [alt_basis_duality cr (canonicalMono_strict hge) (canonicalMono_strict hge),
            if_pos ((vecEq_iff I0 I0).mpr rfl), cr.mul_comm, cr.one_mul] at hW0
          exact False.elim (hunz hW0)
    · intro hlt T hT
      exact (antisym_vanishes_of_lt cr hu hlt T).mp hT

end Conjecture00000007602
