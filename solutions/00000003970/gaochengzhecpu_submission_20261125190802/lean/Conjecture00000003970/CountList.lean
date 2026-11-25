/-
  Conjecture 00000003970 — Finite Counting & Enumeration Combinators
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

namespace Conjecture00000003970

/-- Duplicate-free list predicate (`Nodup` in Core Lean 4). -/
inductive Nodup {α : Type u} : List α → Prop where
  | nil : Nodup []
  | cons {x : α} {xs : List α} : x ∉ xs → Nodup xs → Nodup (x :: xs)

/-- Sum of a list of natural numbers. -/
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Count elements in `L` satisfying boolean predicate `P`. -/
def countWhere {α : Type u} (L : List α) (P : α → Bool) : Nat :=
  (L.filter P).length

/-- Cartesian product of two lists. -/
def listProd {α : Type u} {β : Type v} : List α → List β → List (α × β)
  | [], _ => []
  | x :: xs, ys => ys.map (fun y => (x, y)) ++ listProd xs ys

theorem listSum_append (xs ys : List Nat) :
    listSum (xs ++ ys) = listSum xs + listSum ys := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp [listSum, ih, Nat.add_assoc]

theorem listSum_const_zero {α : Type u} (L : List α) :
    listSum (L.map (fun _ => 0)) = 0 := by
  induction L with
  | nil => rfl
  | cons _ xs ih => simp [listSum, ih]

theorem listSum_map_add {α : Type u} (L : List α) (f g : α → Nat) :
    listSum (L.map (fun x => f x + g x)) = listSum (L.map f) + listSum (L.map g) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, listSum, ih]
    omega

theorem listSum_map_const {α : Type u} (L : List α) (c : Nat) :
    listSum (L.map (fun _ => c)) = c * L.length := by
  induction L with
  | nil => simp [listSum]
  | cons _ xs ih =>
    simp only [List.map, listSum, List.length, ih, Nat.mul_succ]
    omega

theorem listSum_congr {α : Type u} {L : List α} {f g : α → Nat}
    (h : ∀ x ∈ L, f x = g x) :
    listSum (L.map f) = listSum (L.map g) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, listSum]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem nodup_filter {α : Type u} {L : List α} (P : α → Bool) (h : Nodup L) :
    Nodup (L.filter P) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    unfold List.filter
    split
    · refine .cons ?_ ih
      intro hmem
      exact hx (List.mem_filter.mp hmem).1
    · exact ih

theorem nodup_map_of_inj_on {α : Type u} {β : Type v} {L : List α} {f : α → β}
    (hnd : Nodup L)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) :
    Nodup (L.map f) := by
  induction hnd with
  | nil => exact .nil
  | @cons x xs hx _ ih =>
    refine .cons ?_ (ih (fun a ha b hb hfab =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hfab))
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    have hxy := hinj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) hfy
    exact hx (hxy ▸ hy)

theorem nodup_append {α : Type u} {xs ys : List α}
    (hx : Nodup xs) (hy : Nodup ys) (hdisj : ∀ z, z ∈ xs → z ∈ ys → False) :
    Nodup (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | @cons x xs' hx' _ ih =>
    refine .cons ?_ (ih (fun z hz hzy => hdisj z (List.mem_cons_of_mem _ hz) hzy))
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact hx' h1
    · exact hdisj x (List.mem_cons_self ..) h2

/-- Remove the first occurrence of `a` from `L` using decidable propositional equality. -/
def removeOne {α : Type u} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: removeOne a xs

theorem length_removeOne_of_mem {α : Type u} [DecidableEq α] {a : α} {L : List α}
    (h : a ∈ L) : L.length = (removeOne a L).length + 1 := by
  induction L with
  | nil => cases h
  | cons x xs ih =>
    unfold removeOne
    by_cases hxa : x = a
    · simp [hxa]
    · simp only [hxa, ↓reduceIte, List.length]
      rcases List.mem_cons.mp h with rfl | hxs
      · exact False.elim (hxa rfl)
      · have := ih hxs
        omega

theorem mem_removeOne_of_ne {α : Type u} [DecidableEq α] {a b : α} {L : List α}
    (hab : b ≠ a) (hb : b ∈ L) : b ∈ removeOne a L := by
  induction L with
  | nil => cases hb
  | cons x xs ih =>
    unfold removeOne
    by_cases hxa : x = a
    · subst hxa
      simp only [↓reduceIte]
      rcases List.mem_cons.mp hb with rfl | hxs
      · exact False.elim (hab rfl)
      · exact hxs
    · simp only [hxa, ↓reduceIte]
      rcases List.mem_cons.mp hb with rfl | hxs
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hxs)

theorem nodup_length_le_of_subset {α : Type u} [DecidableEq α] {M N : List α}
    (hM : Nodup M) (hsub : ∀ x ∈ M, x ∈ N) : M.length ≤ N.length := by
  induction hM generalizing N with
  | nil => exact Nat.zero_le _
  | @cons x xs hx _ ih =>
    have hxN : x ∈ N := hsub x (List.mem_cons_self ..)
    have hlenN := length_removeOne_of_mem hxN
    have hsub' : ∀ y ∈ xs, y ∈ removeOne x N := by
      intro y hy
      have hyx : y ≠ x := fun h => hx (h ▸ hy)
      exact mem_removeOne_of_ne hyx (hsub y (List.mem_cons_of_mem _ hy))
    have hle := ih hsub'
    simp only [List.length]
    omega

/-- Bijection principle for `countWhere` over duplicate-free lists. -/
theorem countWhere_bij {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    {L₁ : List α} {L₂ : List β} {P₁ : α → Bool} {P₂ : β → Bool}
    (f : α → β) (g : β → α)
    (hnd₁ : Nodup L₁) (hnd₂ : Nodup L₂)
    (hf : ∀ x ∈ L₁, P₁ x = true → f x ∈ L₂ ∧ P₂ (f x) = true ∧ g (f x) = x)
    (hg : ∀ y ∈ L₂, P₂ y = true → g y ∈ L₁ ∧ P₁ (g y) = true ∧ f (g y) = y) :
    countWhere L₁ P₁ = countWhere L₂ P₂ := by
  unfold countWhere
  let A := L₁.filter P₁
  let B := L₂.filter P₂
  have hndA : Nodup A := nodup_filter P₁ hnd₁
  have hndB : Nodup B := nodup_filter P₂ hnd₂
  have hAB : A.length ≤ B.length := by
    have hndMap : Nodup (A.map f) := by
      refine nodup_map_of_inj_on hndA ?_
      intro x hx y hy hfxy
      have hx' := List.mem_filter.mp hx
      have hy' := List.mem_filter.mp hy
      have hgx := (hf x hx'.1 hx'.2).2.2
      have hgy := (hf y hy'.1 hy'.2).2.2
      rw [← hgx, ← hgy, hfxy]
    have hsub : ∀ z ∈ A.map f, z ∈ B := by
      intro z hz
      rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
      have hx' := List.mem_filter.mp hx
      have hfx := hf x hx'.1 hx'.2
      exact List.mem_filter.mpr ⟨hfx.1, hfx.2.1⟩
    have hle := nodup_length_le_of_subset hndMap hsub
    simpa [List.length_map] using hle
  have hBA : B.length ≤ A.length := by
    have hndMap : Nodup (B.map g) := by
      refine nodup_map_of_inj_on hndB ?_
      intro x hx y hy hgxy
      have hx' := List.mem_filter.mp hx
      have hy' := List.mem_filter.mp hy
      have hfx := (hg x hx'.1 hx'.2).2.2
      have hfy := (hg y hy'.1 hy'.2).2.2
      rw [← hfx, ← hfy, hgxy]
    have hsub : ∀ z ∈ B.map g, z ∈ A := by
      intro z hz
      rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
      have hy' := List.mem_filter.mp hy
      have hgy := hg y hy'.1 hy'.2
      exact List.mem_filter.mpr ⟨hgy.1, hgy.2.1⟩
    have hle := nodup_length_le_of_subset hndMap hsub
    simpa [List.length_map] using hle
  exact Nat.le_antisymm hAB hBA

theorem listSum_indicator_of_nodup {τ : Type w} [DecidableEq τ]
    {tags : List τ} (htags : Nodup tags) {t₀ : τ} (ht₀ : t₀ ∈ tags) :
    listSum (tags.map (fun t => if decide (t₀ = t) then 1 else 0)) = 1 := by
  induction htags with
  | nil => cases ht₀
  | @cons t ts ht _ ih =>
    simp only [List.map, listSum]
    by_cases heq : t₀ = t
    · subst heq
      simp only [decide_true, ↓reduceIte]
      have hzero : listSum (ts.map (fun t' => if decide (t₀ = t') then 1 else 0)) = 0 := by
        have := listSum_congr (L := ts) (f := fun t' => if decide (t₀ = t') then 1 else 0)
          (g := fun _ => 0) (fun t' ht' => by
            have hne : t₀ ≠ t' := fun h => ht (h ▸ ht')
            simp [hne])
        rw [this, listSum_const_zero]
      omega
    · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rcases List.mem_cons.mp ht₀ with rfl | hts
      · exact False.elim (heq rfl)
      · exact ih hts

/-- Partition / fiber-sum formula for `countWhere`. -/
theorem countWhere_partition {α : Type u} {τ : Type w} [DecidableEq τ]
    {L : List α} {P : α → Bool} {tags : List τ} (htags : Nodup tags)
    (classify : α → τ)
    (hmem : ∀ x ∈ L, P x = true → classify x ∈ tags) :
    countWhere L P =
      listSum (tags.map (fun t => countWhere L (fun x => P x && decide (classify x = t)))) := by
  induction L with
  | nil =>
    simp only [countWhere, List.filter]
    have := listSum_const_zero tags
    simpa using this.symm
  | cons x xs ih =>
    have ih' := ih (fun y hy hPy => hmem y (List.mem_cons_of_mem _ hy) hPy)
    by_cases hPx : P x = true
    · have hc : classify x ∈ tags := hmem x (List.mem_cons_self ..) hPx
      have hhead : countWhere (x :: xs) P = 1 + countWhere xs P := by
        simp only [countWhere, List.filter, hPx, List.length]
        omega
      rw [hhead, ih']
      have hstep :
          tags.map (fun t => countWhere (x :: xs) (fun y => P y && decide (classify y = t))) =
          tags.map (fun t =>
            (if decide (classify x = t) then 1 else 0) +
              countWhere xs (fun y => P y && decide (classify y = t))) := by
        refine List.map_congr_left ?_
        intro t _
        by_cases hct : classify x = t
        · simp only [countWhere, List.filter, hPx, hct, decide_true, Bool.and_self, ↓reduceIte, List.length]
          omega
        · simp [countWhere, List.filter, hPx, hct]
      rw [hstep, listSum_map_add, listSum_indicator_of_nodup htags hc]
    · have hPxF : P x = false := Bool.eq_false_iff.mpr hPx
      have hhead : countWhere (x :: xs) P = countWhere xs P := by
        simp [countWhere, List.filter, hPxF]
      rw [hhead, ih']
      have hstep :
          tags.map (fun t => countWhere (x :: xs) (fun y => P y && decide (classify y = t))) =
          tags.map (fun t => countWhere xs (fun y => P y && decide (classify y = t))) := by
        refine List.map_congr_left ?_
        intro t _
        simp [countWhere, List.filter, hPxF]
      rw [hstep]

/-- Uniform fiber-size formula: if every valid tag in `tags` has fiber size `c`,
    and every `x` with `P x = true` maps to a valid tag, then `countWhere L P = c * countWhere tags Q`. -/
theorem countWhere_uniform_fiber {α : Type u} {τ : Type w} [DecidableEq τ]
    {L : List α} {P : α → Bool} {tags : List τ} {Q : τ → Bool}
    (htags : Nodup tags) (classify : α → τ) (c : Nat)
    (hmap : ∀ x ∈ L, P x = true → classify x ∈ tags ∧ Q (classify x) = true)
    (hfiber : ∀ t ∈ tags, Q t = true →
      countWhere L (fun x => P x && decide (classify x = t)) = c) :
    countWhere L P = c * countWhere tags Q := by
  have hsub : ∀ x ∈ L, P x = true → classify x ∈ tags.filter Q := by
    intro x hx hPx
    exact List.mem_filter.mpr (hmap x hx hPx)
  have hndQ : Nodup (tags.filter Q) := nodup_filter Q htags
  rw [countWhere_partition hndQ classify hsub]
  have hcongr :
      listSum ((tags.filter Q).map (fun t => countWhere L (fun x => P x && decide (classify x = t)))) =
      listSum ((tags.filter Q).map (fun _ => c)) := by
    refine listSum_congr ?_
    intro t ht
    have ht' := List.mem_filter.mp ht
    exact hfiber t ht'.1 ht'.2
  rw [hcongr, listSum_map_const]
  rfl

theorem mem_listProd {α : Type u} {β : Type v} {xs : List α} {ys : List β} {p : α × β} :
    p ∈ listProd xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih =>
    simp only [listProd, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨h1, h2⟩)
      · exact ⟨List.mem_cons_self .., hy⟩
      · exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rintro ⟨hx, hy⟩
      rcases List.mem_cons.mp hx with h1 | h1
      · left
        refine ⟨p.2, hy, ?_⟩
        cases p
        simp_all
      · exact Or.inr ⟨h1, hy⟩

theorem nodup_listProd {α : Type u} {β : Type v} {xs : List α} {ys : List β}
    (hx : Nodup xs) (hy : Nodup ys) : Nodup (listProd xs ys) := by
  induction hx with
  | nil => exact .nil
  | @cons x xs' hx' _ ih =>
    unfold listProd
    refine nodup_append ?_ ih ?_
    · refine nodup_map_of_inj_on hy ?_
      intro a _ b _ h
      exact Prod.mk.injEq x a x b ▸ h |>.2
    · intro z hz1 hz2
      rcases List.mem_map.mp hz1 with ⟨y, _, rfl⟩
      have hz2' := (mem_listProd.mp hz2).1
      exact hx' hz2'

/-- Product rule for `countWhere` over `listProd`. -/
theorem countWhere_prod {α : Type u} {β : Type v}
    (L₁ : List α) (L₂ : List β) (P₁ : α → Bool) (P₂ : β → Bool) :
    countWhere (listProd L₁ L₂) (fun p => P₁ p.1 && P₂ p.2) =
      countWhere L₁ P₁ * countWhere L₂ P₂ := by
  induction L₁ with
  | nil => simp [listProd, countWhere]
  | cons x xs ih =>
    simp only [countWhere] at ih
    simp only [countWhere, listProd, List.filter_append, List.length_append]
    rw [ih]
    by_cases hPx : P₁ x = true
    · have hmap :
          (L₂.map (fun y => (x, y))).filter (fun p => P₁ p.1 && P₂ p.2) =
          (L₂.filter P₂).map (fun y => (x, y)) := by
        clear ih
        induction L₂ with
        | nil => rfl
        | cons y ys ihy =>
          by_cases hPy : P₂ y = true
          · simp [List.filter, hPx, hPy, ihy]
          · have hPyF : P₂ y = false := Bool.eq_false_iff.mpr hPy
            simp [List.filter, hPx, hPyF, ihy]
      rw [hmap, List.length_map]
      simp only [List.filter, hPx, List.length, Nat.add_one_mul]
      omega
    · have hPxF : P₁ x = false := Bool.eq_false_iff.mpr hPx
      have hmap :
          (L₂.map (fun y => (x, y))).filter (fun p => P₁ p.1 && P₂ p.2) = [] := by
        clear ih
        induction L₂ with
        | nil => rfl
        | cons y ys ihy => simp [List.filter, hPxF, ihy]
      rw [hmap]
      simp [List.filter, hPxF]

/-! ### Complete Duplicate-Free Enumerations of `Fin n`, Subsets, and Finite Maps -/

/-- All elements of `Fin n` in increasing order `0, 1, ..., n-1`. -/
def allFin : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => (0 : Fin (n + 1)) :: (allFin n).map Fin.succ

theorem length_allFin (n : Nat) : (allFin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allFin, ih]

theorem mem_allFin {n : Nat} (i : Fin n) : i ∈ allFin n := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact List.mem_cons_self ..
    | succ j => exact List.mem_cons_of_mem _ (List.mem_map_of_mem (ih j))

theorem nodup_allFin (n : Nat) : Nodup (allFin n) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    refine .cons ?_ ?_
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨j, _, hj⟩
      exact Fin.succ_ne_zero j hj
    · refine nodup_map_of_inj_on ih ?_
      intro a _ b _ h
      exact Fin.succ_inj.mp h

/-- Extend a function `f : Fin k → α` by placing `v₀` at index `0` and `f` on `Fin.succ`. -/
def consFinFn {α : Type u} {k : Nat} (v₀ : α) (f : Fin k → α) (i : Fin (k + 1)) : α :=
  if _ : i.val = 0 then v₀
  else f ⟨i.val - 1, by omega⟩

@[simp] theorem consFinFn_zero {α : Type u} {k : Nat} (v₀ : α) (f : Fin k → α) :
    consFinFn v₀ f (0 : Fin (k + 1)) = v₀ := rfl

@[simp] theorem consFinFn_succ {α : Type u} {k : Nat} (v₀ : α) (f : Fin k → α) (j : Fin k) :
    consFinFn v₀ f j.succ = f j := by
  unfold consFinFn
  have hne : j.succ.val ≠ 0 := by simp
  simp [hne]

theorem funext_fin_succ {α : Type u} {k : Nat} {f g : Fin (k + 1) → α}
    (h0 : f 0 = g 0) (hs : ∀ j : Fin k, f j.succ = g j.succ) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ j => exact hs j

theorem eq_consFinFn {α : Type u} {k : Nat} (f : Fin (k + 1) → α) :
    f = consFinFn (f 0) (fun j => f j.succ) := by
  refine funext_fin_succ ?_ ?_
  · rfl
  · intro j
    simp

/-- Decidable equality for functions `Fin k → α` when `α` has `DecidableEq`. -/
instance instDecidableEqFinFn {α : Type u} [DecidableEq α] :
    {k : Nat} → DecidableEq (Fin k → α)
  | 0, _, _ => isTrue (funext fun i => i.elim0)
  | k + 1, f, g =>
    if h0 : f 0 = g 0 then
      match instDecidableEqFinFn (k := k) (fun j => f j.succ) (fun j => g j.succ) with
      | isTrue hs => isTrue (funext_fin_succ h0 (fun j => congrFun hs j))
      | isFalse hns => isFalse (fun hfg => hns (funext fun j => congrFun hfg j.succ))
    else
      isFalse (fun hfg => h0 (congrFun hfg 0))

/-- Enumerate all functions `Fin k → α` given a duplicate-free list `vals` of `α`. -/
def allFinFns {α : Type u} (vals : List α) : (k : Nat) → List (Fin k → α)
  | 0 => [fun i => i.elim0]
  | k + 1 =>
    (listProd vals (allFinFns vals k)).map (fun p => consFinFn p.1 p.2)

theorem mem_allFinFns {α : Type u} {vals : List α} (hvals : ∀ v : α, v ∈ vals) :
    ∀ {k : Nat} (f : Fin k → α), f ∈ allFinFns vals k
  | 0, f => by
    have : f = (fun i => i.elim0) := funext fun i => i.elim0
    rw [this]
    exact List.mem_singleton_self _
  | k + 1, f => by
    unfold allFinFns
    rw [List.mem_map]
    refine ⟨(f 0, fun j => f j.succ), ?_, (eq_consFinFn f).symm⟩
    exact mem_listProd.mpr ⟨hvals (f 0), mem_allFinFns hvals (fun j => f j.succ)⟩

theorem nodup_allFinFns {α : Type u} {vals : List α} (hnd : Nodup vals) :
    ∀ (k : Nat), Nodup (allFinFns vals k)
  | 0 => .cons (by simp) .nil
  | k + 1 => by
    unfold allFinFns
    refine nodup_map_of_inj_on (nodup_listProd hnd (nodup_allFinFns hnd k)) ?_
    intro p₁ _ p₂ _ heq
    have h1 : p₁.1 = p₂.1 := by
      have := congrFun heq 0
      simpa using this
    have h2 : p₁.2 = p₂.2 := by
      funext j
      have := congrFun heq j.succ
      simpa using this
    cases p₁; cases p₂
    simp_all

/-- All boolean subsets `Fin n → Bool`. -/
def allSubsets (n : Nat) : List (Fin n → Bool) :=
  allFinFns [false, true] n

theorem mem_allSubsets {n : Nat} (S : Fin n → Bool) : S ∈ allSubsets n := by
  refine mem_allFinFns ?_ S
  intro b; cases b <;> simp

theorem nodup_allSubsets (n : Nat) : Nodup (allSubsets n) := by
  refine nodup_allFinFns ?_ n
  exact .cons (by simp) (.cons (by simp) .nil)

/-- All functions `Fin k → Fin n`. -/
def allFinMaps (k n : Nat) : List (Fin k → Fin n) :=
  allFinFns (allFin n) k

theorem mem_allFinMaps {k n : Nat} (f : Fin k → Fin n) : f ∈ allFinMaps k n :=
  mem_allFinFns mem_allFin f

theorem nodup_allFinMaps (k n : Nat) : Nodup (allFinMaps k n) :=
  nodup_allFinFns (nodup_allFin n) k

end Conjecture00000003970
