/-
  SpernerFD/Basic.lean
  Core combinatorics of duplicate-free lists, the Boolean cube {0,1}^n,
  binomial coefficients, fixed-size sublists, and exponential growth bounds
  in pure Core Lean 4.19.0 (zero external dependencies).
-/

namespace SpernerFD

/-! ## 1. Duplicate-Free Lists and Finite Pigeonhole Lemmas -/

/-- Constructive duplicate-free predicate on lists. -/
def NoDup {α : Type u} : List α → Prop
  | [] => True
  | a :: l => a ∉ l ∧ NoDup l

theorem noDup_nil {α : Type u} : NoDup ([] : List α) := trivial

theorem noDup_singleton {α : Type u} (a : α) : NoDup [a] :=
  ⟨(fun h => nomatch h), trivial⟩

theorem noDup_pair {α : Type u} {a b : α} (h : a ≠ b) : NoDup [a, b] :=
  ⟨(fun hm => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact h rfl
    · nomatch hm'),
   noDup_singleton b⟩

theorem noDup_append {α : Type u} {l₁ l₂ : List α}
    (h₁ : NoDup l₁) (h₂ : NoDup l₂) (hdisj : ∀ x, x ∈ l₁ → x ∉ l₂) :
    NoDup (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := h₁
    refine ⟨?_, ih ht (fun x hx => hdisj x (List.mem_cons_of_mem a hx))⟩
    intro hmem
    rcases List.mem_append.mp hmem with hmem₁ | hmem₂
    · exact hat hmem₁
    · exact hdisj a (List.mem_cons_self ..) hmem₂

theorem noDup_map {α : Type u} {β : Type v} {f : α → β} {l : List α}
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (hl : NoDup l) :
    NoDup (l.map f) := by
  induction l with
  | nil => exact trivial
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hl
    refine ⟨?_, ih (fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy) ht⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
    have hab : b = a := hinj b (List.mem_cons_of_mem a hb) a (List.mem_cons_self ..) hfb
    exact hat (hab ▸ hb)

theorem noDup_filter {α : Type u} (p : α → Bool) {l : List α} (hl : NoDup l) :
    NoDup (l.filter p) := by
  induction l with
  | nil => exact trivial
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hl
    simp only [List.filter]
    cases p a with
    | false => exact ih ht
    | true =>
      refine ⟨?_, ih ht⟩
      intro hmem
      exact hat (List.mem_filter.mp hmem).1

instance instDecidableNoDup {α : Type u} [DecidableEq α] : (l : List α) → Decidable (NoDup l)
  | [] => isTrue trivial
  | a :: t =>
    match inferInstanceAs (Decidable (a ∉ t)), instDecidableNoDup t with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ => isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ => isFalse (fun h => h₂ h.2)

/-- Remove the first occurrence of `a` from `l`. -/
def eraseFirst {α : Type u} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: t => if a = b then t else b :: eraseFirst a t

theorem length_eraseFirst_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : (eraseFirst a l).length + 1 = l.length := by
  induction l with
  | nil => nomatch h
  | cons b t ih =>
    simp only [eraseFirst]
    split
    · rfl
    · next hne =>
      rcases List.mem_cons.mp h with rfl | ht
      · exact absurd rfl hne
      · simp only [List.length_cons]
        have hlen := ih ht
        omega

theorem mem_eraseFirst_of_ne {α : Type u} [DecidableEq α] {a x : α} {l : List α}
    (hne : x ≠ a) (hx : x ∈ l) : x ∈ eraseFirst a l := by
  induction l with
  | nil => nomatch hx
  | cons b t ih =>
    simp only [eraseFirst]
    split
    · next hab =>
      rcases List.mem_cons.mp hx with rfl | ht
      · exact absurd hab.symm hne
      · exact ht
    · next _ =>
      rcases List.mem_cons.mp hx with rfl | ht
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem b (ih ht)

/-- Finite pigeonhole principle: a duplicate-free list contained in `B` has length `≤ B.length`. -/
theorem noDup_length_le_of_subset {α : Type u} [DecidableEq α] {A B : List α}
    (hA : NoDup A) (hsub : ∀ x ∈ A, x ∈ B) : A.length ≤ B.length := by
  induction A generalizing B with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hA
    have haB : a ∈ B := hsub a (List.mem_cons_self ..)
    have hlen : (eraseFirst a B).length + 1 = B.length := length_eraseFirst_of_mem haB
    have hsub' : ∀ x ∈ t, x ∈ eraseFirst a B := by
      intro x hx
      have hne : x ≠ a := fun h => hat (h ▸ hx)
      exact mem_eraseFirst_of_ne hne (hsub x (List.mem_cons_of_mem a hx))
    have iht := ih ht hsub'
    simp only [List.length_cons]
    omega

/-- Equal-size subset rigidity: if `NoDup A`, `A ⊆ B`, and `B.length ≤ A.length`, then `B ⊆ A`. -/
theorem subset_symm_of_noDup_length_le {α : Type u} [DecidableEq α] {A B : List α}
    (hA : NoDup A) (hsub : ∀ x ∈ A, x ∈ B) (hlen : B.length ≤ A.length) :
    ∀ y ∈ B, y ∈ A := by
  intro y hyB
  by_cases hyA : y ∈ A
  · exact hyA
  · have hA' : NoDup (y :: A) := ⟨hyA, hA⟩
    have hsub' : ∀ x ∈ y :: A, x ∈ B := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxA
      · exact hyB
      · exact hsub x hxA
    have hbad := noDup_length_le_of_subset hA' hsub'
    simp only [List.length_cons] at hbad
    omega

/-! ## 2. Sublists and Fixed-Size Sublists -/

/-- All sublists of `l`. -/
def allSublists {α : Type u} : List α → List (List α)
  | [] => [[]]
  | a :: l => allSublists l ++ (allSublists l).map (fun s => a :: s)

theorem nil_mem_allSublists {α : Type u} (l : List α) : [] ∈ allSublists l := by
  induction l with
  | nil => exact List.mem_cons_self ..
  | cons _ _ ih => exact List.mem_append_left _ ih

theorem mem_of_mem_allSublists {α : Type u} {l s : List α}
    (hs : s ∈ allSublists l) : ∀ x ∈ s, x ∈ l := by
  induction l generalizing s with
  | nil =>
    rcases List.mem_singleton.mp hs with rfl
    intro _ hx; nomatch hx
  | cons a _ ih =>
    rcases List.mem_append.mp hs with hs₁ | hs₂
    · intro x hx
      exact List.mem_cons_of_mem a (ih hs₁ x hx)
    · rcases List.mem_map.mp hs₂ with ⟨u, hu, rfl⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxu
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem a (ih hu x hxu)

theorem noDup_of_mem_allSublists {α : Type u} {l s : List α}
    (hl : NoDup l) (hs : s ∈ allSublists l) : NoDup s := by
  induction l generalizing s with
  | nil =>
    rcases List.mem_singleton.mp hs with rfl
    exact trivial
  | cons a _ ih =>
    obtain ⟨hat, ht⟩ := hl
    rcases List.mem_append.mp hs with hs₁ | hs₂
    · exact ih ht hs₁
    · rcases List.mem_map.mp hs₂ with ⟨u, hu, rfl⟩
      refine ⟨?_, ih ht hu⟩
      intro hau
      exact hat (mem_of_mem_allSublists hu a hau)

theorem filter_mem_allSublists {α : Type u} (p : α → Bool) (l : List α) :
    l.filter p ∈ allSublists l := by
  induction l with
  | nil => exact List.mem_cons_self ..
  | cons a t ih =>
    simp only [List.filter, allSublists]
    cases p a with
    | false => exact List.mem_append_left _ ih
    | true =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨t.filter p, ih, rfl⟩

/-- Pascal binomial coefficient. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n (k + 1) + binom n k

/-- Central binomial coefficient `binom n (n / 2)`. -/
def centralBinom (n : Nat) : Nat := binom n (n / 2)

/-- All sublists of `l` of exact length `k`. -/
def chooseSublists {α : Type u} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | a :: l, k + 1 => chooseSublists l (k + 1) ++ (chooseSublists l k).map (fun s => a :: s)

theorem length_chooseSublists {α : Type u} (l : List α) (k : Nat) :
    (chooseSublists l k).length = binom l.length k := by
  induction l generalizing k with
  | nil =>
    cases k <;> rfl
  | cons _ t ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [chooseSublists, List.length_append, List.length_map, List.length_cons, binom]
      rw [ih (k' + 1), ih k']

theorem mem_chooseSublists_props {α : Type u} {l s : List α} {k : Nat}
    (hs : s ∈ chooseSublists l k) : s.length = k ∧ (∀ x ∈ s, x ∈ l) := by
  induction l generalizing s k with
  | nil =>
    cases k with
    | zero =>
      rcases List.mem_singleton.mp hs with rfl
      exact ⟨rfl, fun _ hx => nomatch hx⟩
    | succ _ => nomatch hs
  | cons a _ ih =>
    cases k with
    | zero =>
      rcases List.mem_singleton.mp hs with rfl
      exact ⟨rfl, fun _ hx => nomatch hx⟩
    | succ _ =>
      rcases List.mem_append.mp hs with hs₁ | hs₂
      · obtain ⟨hlen, hsub⟩ := ih hs₁
        exact ⟨hlen, fun x hx => List.mem_cons_of_mem a (hsub x hx)⟩
      · rcases List.mem_map.mp hs₂ with ⟨u, hu, rfl⟩
        obtain ⟨hlen, hsub⟩ := ih hu
        refine ⟨by simp [hlen], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxu
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem a (hsub x hxu)

theorem noDup_of_mem_chooseSublists {α : Type u} {l s : List α} {k : Nat}
    (hl : NoDup l) (hs : s ∈ chooseSublists l k) : NoDup s := by
  induction l generalizing s k with
  | nil =>
    cases k with
    | zero =>
      rcases List.mem_singleton.mp hs with rfl
      exact trivial
    | succ _ => nomatch hs
  | cons _ _ ih =>
    obtain ⟨hat, ht⟩ := hl
    cases k with
    | zero =>
      rcases List.mem_singleton.mp hs with rfl
      exact trivial
    | succ _ =>
      rcases List.mem_append.mp hs with hs₁ | hs₂
      · exact ih ht hs₁
      · rcases List.mem_map.mp hs₂ with ⟨u, hu, rfl⟩
        refine ⟨?_, ih ht hu⟩
        intro hau
        exact hat ((mem_chooseSublists_props hu).2 _ hau)

/-- Two elements of `chooseSublists l k` (with `NoDup l`) that have the same membership are equal. -/
theorem eq_of_mem_chooseSublists_ext {α : Type u} {l s₁ s₂ : List α} {k : Nat}
    (hl : NoDup l) (h₁ : s₁ ∈ chooseSublists l k) (h₂ : s₂ ∈ chooseSublists l k)
    (hext : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ := by
  induction l generalizing s₁ s₂ k with
  | nil =>
    cases k with
    | zero =>
      rcases List.mem_singleton.mp h₁ with rfl
      rcases List.mem_singleton.mp h₂ with rfl
      rfl
    | succ _ => nomatch h₁
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hl
    cases k with
    | zero =>
      rcases List.mem_singleton.mp h₁ with rfl
      rcases List.mem_singleton.mp h₂ with rfl
      rfl
    | succ _ =>
      rcases List.mem_append.mp h₁ with h₁L | h₁R <;>
      rcases List.mem_append.mp h₂ with h₂L | h₂R
      · exact ih ht h₁L h₂L hext
      · rcases List.mem_map.mp h₂R with ⟨_, _, rfl⟩
        have ha₁ : a ∈ s₁ := (hext a).mpr (List.mem_cons_self ..)
        exact absurd ((mem_chooseSublists_props h₁L).2 a ha₁) hat
      · rcases List.mem_map.mp h₁R with ⟨_, _, rfl⟩
        have ha₂ : a ∈ s₂ := (hext a).mp (List.mem_cons_self ..)
        exact absurd ((mem_chooseSublists_props h₂L).2 a ha₂) hat
      · rcases List.mem_map.mp h₁R with ⟨u₁, hu₁, rfl⟩
        rcases List.mem_map.mp h₂R with ⟨u₂, hu₂, rfl⟩
        congr 1
        apply ih ht hu₁ hu₂
        intro x
        constructor
        · intro hxu₁
          have hne : x ≠ a := fun h => hat (h ▸ (mem_chooseSublists_props hu₁).2 x hxu₁)
          rcases List.mem_cons.mp ((hext x).mp (List.mem_cons_of_mem a hxu₁)) with rfl | hxu₂
          · exact absurd rfl hne
          · exact hxu₂
        · intro hxu₂
          have hne : x ≠ a := fun h => hat (h ▸ (mem_chooseSublists_props hu₂).2 x hxu₂)
          rcases List.mem_cons.mp ((hext x).mpr (List.mem_cons_of_mem a hxu₂)) with rfl | hxu₁
          · exact absurd rfl hne
          · exact hxu₁

theorem noDup_chooseSublists {α : Type u} {l : List α} (hl : NoDup l) (k : Nat) :
    NoDup (chooseSublists l k) := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => exact noDup_singleton []
    | succ _ => exact trivial
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hl
    cases k with
    | zero => exact noDup_singleton []
    | succ k' =>
      apply noDup_append (ih ht (k' + 1))
      · apply noDup_map _ (ih ht k')
        intro _ _ _ _ hxy
        injection hxy
      · intro s hsL hsR
        rcases List.mem_map.mp hsR with ⟨_, _, rfl⟩
        exact hat ((mem_chooseSublists_props hsL).2 a (List.mem_cons_self ..))

/-! ## 3. Boolean Cube `{0, 1}^n`, Weight, and Cube Layers -/

/-- The `n`-dimensional Boolean cube `{0, 1}^n` represented as `Fin n → Bool`. -/
abbrev Cube (n : Nat) : Type := Fin n → Bool

/-- Pointwise partial order on `Cube n` (`false ≤ true`). -/
def CubeLe {n : Nat} (x y : Cube n) : Prop :=
  ∀ i : Fin n, x i = true → y i = true

theorem cubeLe_refl {n : Nat} (x : Cube n) : CubeLe x x :=
  fun _ h => h

theorem cubeLe_trans {n : Nat} {x y z : Cube n}
    (hxy : CubeLe x y) (hyz : CubeLe y z) : CubeLe x z :=
  fun i hx => hyz i (hxy i hx)

theorem cubeLe_antisymm {n : Nat} {x y : Cube n}
    (hxy : CubeLe x y) (hyx : CubeLe y x) : x = y := by
  funext i
  cases hx : x i <;> cases hy : y i
  · rfl
  · have := hyx i hy; rw [hx] at this; nomatch this
  · have := hxy i hx; rw [hy] at this; nomatch this
  · rfl

/-- All-false (`0...0`) and all-true (`1...1`) vertices of `Cube n`. -/
def botCube (n : Nat) : Cube n := fun _ => false
def topCube (n : Nat) : Cube n := fun _ => true

theorem botCube_le {n : Nat} (x : Cube n) : CubeLe (botCube n) x :=
  fun _ h => nomatch h

theorem le_topCube {n : Nat} (x : Cube n) : CubeLe x (topCube n) :=
  fun _ _ => rfl

/-- First coordinate of a non-empty cube vector. -/
def headCube {n : Nat} (x : Cube (n + 1)) : Bool :=
  x ⟨0, Nat.zero_lt_succ n⟩

/-- Remaining `n` coordinates of a `(n + 1)`-cube vector. -/
def tailCube {n : Nat} (x : Cube (n + 1)) : Cube n :=
  fun i => x i.succ

/-- Prepend a Boolean coordinate to `Cube n`. -/
def consCube {n : Nat} (b : Bool) (x : Cube n) : Cube (n + 1) :=
  fun i => if h : i.val = 0 then b else x ⟨i.val - 1, by omega⟩

@[simp] theorem headCube_cons {n : Nat} (b : Bool) (x : Cube n) :
    headCube (consCube b x) = b := rfl

@[simp] theorem tailCube_cons {n : Nat} (b : Bool) (x : Cube n) :
    tailCube (consCube b x) = x := by
  funext i
  simp only [tailCube, consCube, Fin.val_succ]
  have hne : i.val + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceDIte]
  congr 1

theorem consCube_head_tail {n : Nat} (x : Cube (n + 1)) :
    consCube (headCube x) (tailCube x) = x := by
  funext i
  simp only [consCube, headCube, tailCube]
  split
  · next h0 =>
    congr 1
    exact Fin.ext h0.symm
  · next _ =>
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem consCube_inj {n : Nat} {b₁ b₂ : Bool} {x₁ x₂ : Cube n}
    (h : consCube b₁ x₁ = consCube b₂ x₂) : b₁ = b₂ ∧ x₁ = x₂ := by
  have hb : headCube (consCube b₁ x₁) = headCube (consCube b₂ x₂) := by rw [h]
  have hx : tailCube (consCube b₁ x₁) = tailCube (consCube b₂ x₂) := by rw [h]
  simp only [headCube_cons, tailCube_cons] at hb hx
  exact ⟨hb, hx⟩

theorem cubeLe_succ_iff {n : Nat} {x y : Cube (n + 1)} :
    CubeLe x y ↔ (headCube x = true → headCube y = true) ∧ CubeLe (tailCube x) (tailCube y) := by
  constructor
  · intro h
    exact ⟨h ⟨0, Nat.zero_lt_succ n⟩, fun i hi => h i.succ hi⟩
  · rintro ⟨h0, ht⟩ i hi
    by_cases hiz : i.val = 0
    · have hi' : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hiz
      rw [hi'] at hi ⊢
      exact h0 hi
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := by
        apply Fin.ext
        simp only [Fin.val_succ, j]
        omega
      rw [← hj] at hi ⊢
      exact ht j hi

instance instDecidableEqCube : {n : Nat} → DecidableEq (Cube n)
  | 0, _, _ => isTrue (funext fun i => Fin.elim0 i)
  | _ + 1, x, y =>
    match inferInstanceAs (Decidable (headCube x = headCube y)),
          instDecidableEqCube (tailCube x) (tailCube y) with
    | isTrue hh, isTrue ht =>
      isTrue (by rw [← consCube_head_tail x, ← consCube_head_tail y, hh, ht])
    | isFalse hh, _ => isFalse (fun h => hh (by rw [h]))
    | _, isFalse ht => isFalse (fun h => ht (by rw [h]))

instance instDecidableCubeLe : {n : Nat} → (x y : Cube n) → Decidable (CubeLe x y)
  | 0, _, _ => isTrue (fun i => Fin.elim0 i)
  | _ + 1, x, y =>
    match inferInstanceAs (Decidable (headCube x = true → headCube y = true)),
          instDecidableCubeLe (tailCube x) (tailCube y) with
    | isTrue hh, isTrue ht => isTrue (cubeLe_succ_iff.mpr ⟨hh, ht⟩)
    | isFalse hh, _ => isFalse (fun h => hh (cubeLe_succ_iff.mp h).1)
    | _, isFalse ht => isFalse (fun h => ht (cubeLe_succ_iff.mp h).2)

/-- Hamming weight (number of `true` coordinates) of a vertex `x : Cube n`. -/
def weight : {n : Nat} → Cube n → Nat
  | 0, _ => 0
  | _ + 1, x => (if headCube x then 1 else 0) + weight (tailCube x)

@[simp] theorem weight_cons_false {n : Nat} (x : Cube n) :
    weight (consCube false x) = weight x := by
  simp [weight]

@[simp] theorem weight_cons_true {n : Nat} (x : Cube n) :
    weight (consCube true x) = 1 + weight x := by
  simp [weight]

theorem weight_botCube (n : Nat) : weight (botCube n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have htail : tailCube (botCube (n + 1)) = botCube n := rfl
    have hhead : headCube (botCube (n + 1)) = false := rfl
    simp [weight, hhead, htail, ih]

theorem weight_topCube (n : Nat) : weight (topCube n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have htail : tailCube (topCube (n + 1)) = topCube n := rfl
    have hhead : headCube (topCube (n + 1)) = true := rfl
    simp only [weight, hhead, ↓reduceIte, htail, ih]
    omega

theorem weight_le_dim : {n : Nat} → (x : Cube n) → weight x ≤ n
  | 0, _ => Nat.le_refl 0
  | _ + 1, x => by
    simp only [weight]
    have ht := weight_le_dim (tailCube x)
    cases headCube x <;> simp <;> omega

theorem cubeLe_weight_le : {n : Nat} → {x y : Cube n} → CubeLe x y → weight x ≤ weight y
  | 0, _, _, _ => Nat.le_refl 0
  | _ + 1, x, y, h => by
    obtain ⟨h0, ht⟩ := cubeLe_succ_iff.mp h
    have iht := cubeLe_weight_le ht
    simp only [weight]
    cases hx : headCube x <;> cases hy : headCube y
    · simp; exact iht
    · simp; omega
    · rw [hx] at h0; have := h0 rfl; rw [hy] at this; nomatch this
    · simp; omega

theorem cubeLe_eq_of_weight_eq : {n : Nat} → {x y : Cube n} →
    CubeLe x y → weight x = weight y → x = y
  | 0, _, _, _, _ => funext fun i => Fin.elim0 i
  | _ + 1, x, y, hle, hw => by
    obtain ⟨h0, ht⟩ := cubeLe_succ_iff.mp hle
    have _ := cubeLe_weight_le ht
    simp only [weight] at hw
    have hhb : headCube x = headCube y ∧ weight (tailCube x) = weight (tailCube y) := by
      cases hx : headCube x <;> cases hy : headCube y
      · simp [hx, hy] at hw; exact ⟨rfl, hw⟩
      · simp [hx, hy] at hw; omega
      · rw [hx] at h0; have := h0 rfl; rw [hy] at this; nomatch this
      · simp [hx, hy] at hw; exact ⟨rfl, by omega⟩
    have hteq : tailCube x = tailCube y := cubeLe_eq_of_weight_eq ht hhb.2
    rw [← consCube_head_tail x, ← consCube_head_tail y, hhb.1, hteq]

/-- Complete duplicate-free enumeration of `Cube n`. -/
def allCubes : (n : Nat) → List (Cube n)
  | 0 => [botCube 0]
  | n + 1 => (allCubes n).map (consCube false) ++ (allCubes n).map (consCube true)

theorem length_allCubes (n : Nat) : (allCubes n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allCubes, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem mem_allCubes : {n : Nat} → (x : Cube n) → x ∈ allCubes n
  | 0, x => by
    have hx : x = botCube 0 := funext fun i => Fin.elim0 i
    rw [hx]
    exact List.mem_cons_self ..
  | _ + 1, x => by
    rw [← consCube_head_tail x]
    simp only [allCubes]
    cases headCube x with
    | false =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨tailCube x, mem_allCubes (tailCube x), rfl⟩
    | true =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨tailCube x, mem_allCubes (tailCube x), rfl⟩

theorem noDup_allCubes : (n : Nat) → NoDup (allCubes n)
  | 0 => noDup_singleton (botCube 0)
  | n + 1 => by
    simp only [allCubes]
    apply noDup_append
    · exact noDup_map (fun _ _ _ _ h => (consCube_inj h).2) (noDup_allCubes n)
    · exact noDup_map (fun _ _ _ _ h => (consCube_inj h).2) (noDup_allCubes n)
    · intro _ hzL hzR
      rcases List.mem_map.mp hzL with ⟨_, _, rfl⟩
      rcases List.mem_map.mp hzR with ⟨_, _, heq⟩
      have hb := (consCube_inj heq).1
      nomatch hb

/-- Complete duplicate-free enumeration of the `k`-th weight layer `{x : Cube n | weight x = k}`. -/
def layerCubes : (n : Nat) → Nat → List (Cube n)
  | 0, 0 => [botCube 0]
  | 0, _ + 1 => []
  | n + 1, 0 => (layerCubes n 0).map (consCube false)
  | n + 1, k + 1 =>
    (layerCubes n (k + 1)).map (consCube false) ++ (layerCubes n k).map (consCube true)

theorem length_layerCubes (n k : Nat) : (layerCubes n k).length = binom n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero =>
      simp only [layerCubes, List.length_map, ih 0]
      cases n <;> rfl
    | succ k' =>
      simp only [layerCubes, List.length_append, List.length_map, binom]
      rw [ih (k' + 1), ih k']

theorem mem_layerCubes_iff : {n k : Nat} → (x : Cube n) → (x ∈ layerCubes n k ↔ weight x = k)
  | 0, 0, x => by
    have hx : x = botCube 0 := funext fun i => Fin.elim0 i
    rw [hx]
    simp [layerCubes, weight]
  | 0, _ + 1, _ => by
    simp [layerCubes, weight]
  | n + 1, 0, x => by
    simp only [layerCubes, List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp [(mem_layerCubes_iff u).mp hu]
    · intro hw
      simp only [weight] at hw
      cases hx : headCube x with
      | true => simp [hx] at hw
      | false =>
        simp only [hx, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hw
        exact ⟨tailCube x, (mem_layerCubes_iff (tailCube x)).mpr hw,
          by rw [← hx, consCube_head_tail]⟩
  | n + 1, k + 1, x => by
    simp only [layerCubes, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · simp [(mem_layerCubes_iff u).mp hu]
      · have hwu := (mem_layerCubes_iff u).mp hu
        simp only [weight_cons_true, hwu]
        omega
    · intro hw
      simp only [weight] at hw
      cases hx : headCube x with
      | false =>
        simp only [hx, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hw
        left
        exact ⟨tailCube x, (mem_layerCubes_iff (tailCube x)).mpr hw,
          by rw [← hx, consCube_head_tail]⟩
      | true =>
        simp only [hx, ↓reduceIte] at hw
        have hwt : weight (tailCube x) = k := by omega
        right
        exact ⟨tailCube x, (mem_layerCubes_iff (tailCube x)).mpr hwt,
          by rw [← hx, consCube_head_tail]⟩

theorem noDup_layerCubes : (n k : Nat) → NoDup (layerCubes n k)
  | 0, 0 => noDup_singleton (botCube 0)
  | 0, _ + 1 => noDup_nil
  | n + 1, 0 => noDup_map (fun _ _ _ _ h => (consCube_inj h).2) (noDup_layerCubes n 0)
  | n + 1, k + 1 => by
    simp only [layerCubes]
    apply noDup_append
    · exact noDup_map (fun _ _ _ _ h => (consCube_inj h).2) (noDup_layerCubes n (k + 1))
    · exact noDup_map (fun _ _ _ _ h => (consCube_inj h).2) (noDup_layerCubes n k)
    · intro _ hzL hzR
      rcases List.mem_map.mp hzL with ⟨_, _, rfl⟩
      rcases List.mem_map.mp hzR with ⟨_, _, heq⟩
      have hb := (consCube_inj heq).1
      nomatch hb

/-! ## 4. Binomial Identities and Exponential Growth Bounds -/

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ _ => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [binom]
      have h1 : binom n (k' + 1) = 0 := ih (by omega)
      have h2 : binom n k' = 0 := ih (by omega)
      omega

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [binom, ih, binom_eq_zero_of_lt (Nat.lt_succ_self n)]

theorem binom_one_right (n : Nat) : binom n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [binom, ih, binom_zero_right]

theorem binom_two_right (n : Nat) : 2 * binom n 2 = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      have h1 : binom (m + 1 + 1) 2 = binom (m + 1) 2 + binom (m + 1) 1 := rfl
      rw [h1, binom_one_right, Nat.left_distrib, ih]
      simp only [Nat.add_sub_cancel]
      have hlin : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by
        have hstep : m + 1 + 1 = (m + 1) + 1 := rfl
        rw [hstep, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
        omega
      omega

theorem binom_le_two_pow (n k : Nat) : binom n k ≤ 2 ^ n := by
  rw [← length_layerCubes n k, ← length_allCubes n]
  exact noDup_length_le_of_subset (noDup_layerCubes n k) (fun x _ => mem_allCubes x)

/-- Absorption law `(k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k`. -/
theorem succ_mul_binom_succ (n k : Nat) :
    (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k' =>
      have h1 : binom 1 (k' + 2) = 0 := binom_eq_zero_of_lt (by omega)
      have h2 : binom 0 (k' + 1) = 0 := rfl
      rw [h1, h2]
      omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [Nat.zero_add, Nat.one_mul, binom_one_right, binom_zero_right, Nat.mul_one]
    | succ j =>
      have hp : binom (n + 2) (j + 2) = binom (n + 1) (j + 2) + binom (n + 1) (j + 1) := rfl
      rw [hp, Nat.left_distrib, ih (j + 1)]
      have hsplit : (j + 2) * binom (n + 1) (j + 1) =
          (j + 1) * binom (n + 1) (j + 1) + binom (n + 1) (j + 1) := by
        have hj2 : j + 2 = (j + 1) + 1 := rfl
        rw [hj2, Nat.add_mul, Nat.one_mul]
      rw [hsplit, ih j]
      have h1 : (n + 1) * binom n (j + 1) + (n + 1) * binom n j =
          (n + 1) * binom (n + 1) (j + 1) := by
        rw [← Nat.left_distrib]
        rfl
      have h2 : (n + 1 + 1) * binom (n + 1) (j + 1) =
          (n + 1) * binom (n + 1) (j + 1) + binom (n + 1) (j + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

theorem succ_mul_binom_eq {n k : Nat} (hk : k ≤ n) :
    (k + 1) * binom n (k + 1) = (n - k) * binom n k := by
  have habs := succ_mul_binom_succ n k
  have hp : binom (n + 1) (k + 1) = binom n (k + 1) + binom n k := rfl
  rw [hp, Nat.left_distrib] at habs
  have hsub : (n + 1) * binom n k - (k + 1) * binom n k = (n - k) * binom n k := by
    rw [← Nat.sub_mul]
    congr 1
    omega
  omega

theorem binom_symm {n k : Nat} (hk : k ≤ n) : binom n (n - k) = binom n k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst hkn
      simp [binom_zero_right, binom_self]
    · cases k with
      | zero =>
        simp [binom_self, binom_zero_right]
      | succ j =>
        have hsub : n + 1 - (j + 1) = n - j := by omega
        rw [hsub]
        have hpos : n - j = (n - (j + 1)) + 1 := by omega
        rw [hpos]
        simp only [binom]
        have ih1 : binom n (n - (j + 1) + 1) = binom n j := by
          have : n - (j + 1) + 1 = n - j := by omega
          rw [this]
          exact ih (by omega)
        have ih2 : binom n (n - (j + 1)) = binom n (j + 1) := ih (by omega)
        omega

theorem binom_mono_left_half {n k : Nat} (hk : k + 1 ≤ n / 2) :
    binom n k ≤ binom n (k + 1) := by
  have hrel := succ_mul_binom_eq (n := n) (k := k) (by omega)
  have hle : k + 1 ≤ n - k := by omega
  have hmul : (k + 1) * binom n k ≤ (k + 1) * binom n (k + 1) := by
    rw [hrel]
    exact Nat.mul_le_mul_right (binom n k) hle
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

theorem binom_le_central_of_le_half {n k : Nat} (hk : k ≤ n / 2) :
    binom n k ≤ centralBinom n := by
  unfold centralBinom
  have haux : ∀ d, ∀ j, j + d = n / 2 → binom n j ≤ binom n (n / 2) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have : j = n / 2 := by omega
      rw [this]
      exact Nat.le_refl _
    | succ d ih =>
      intro j hj
      exact Nat.le_trans (binom_mono_left_half (by omega)) (ih (j + 1) (by omega))
  exact haux (n / 2 - k) k (by omega)

/-- Every binomial coefficient `binom n k` is bounded above by `centralBinom n`. -/
theorem binom_le_central (n k : Nat) : binom n k ≤ centralBinom n := by
  by_cases hkn : n < k
  · rw [binom_eq_zero_of_lt hkn]
    exact Nat.zero_le _
  · by_cases hhalf : k ≤ n / 2
    · exact binom_le_central_of_le_half hhalf
    · rw [← binom_symm (by omega)]
      exact binom_le_central_of_le_half (by omega)

/-- Concatenation of the first `j` weight layers of `Cube n`. -/
def concatLayers (n : Nat) : Nat → List (Cube n)
  | 0 => []
  | j + 1 => concatLayers n j ++ layerCubes n j

theorem mem_concatLayers_of_weight_lt {n j : Nat} {x : Cube n}
    (hw : weight x < j) : x ∈ concatLayers n j := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [concatLayers]
    by_cases hxj : weight x = j
    · exact List.mem_append_right _ ((mem_layerCubes_iff x).mpr hxj)
    · exact List.mem_append_left _ (ih (by omega))

theorem length_concatLayers_le (n j : Nat) :
    (concatLayers n j).length ≤ j * centralBinom n := by
  induction j with
  | zero => simp [concatLayers]
  | succ j ih =>
    simp only [concatLayers, List.length_append, length_layerCubes]
    have hb := binom_le_central n j
    have hmul : (j + 1) * centralBinom n = j * centralBinom n + centralBinom n := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Fundamental central binomial lower bound: `(M + 1) * binom M (M / 2) ≥ 2 ^ M`. -/
theorem centralBinom_mul_succ_ge_two_pow (M : Nat) :
    2 ^ M ≤ (M + 1) * centralBinom M := by
  rw [← length_allCubes M]
  apply Nat.le_trans _ (length_concatLayers_le M (M + 1))
  apply noDup_length_le_of_subset (noDup_allCubes M)
  intro x _
  apply mem_concatLayers_of_weight_lt
  have hw := weight_le_dim x
  omega

/-- Clean exponential lower bound without denominators: `centralBinom M ≥ 2 ^ (M / 2)`. -/
theorem centralBinom_ge_two_pow_half (M : Nat) :
    2 ^ (M / 2) ≤ centralBinom M := by
  have hstep : ∀ m, 2 ≤ m → 2 * centralBinom m ≤ centralBinom (m + 2) := by
    intro m hm
    unfold centralBinom
    have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
    rw [hdiv]
    have hkpos : 1 ≤ m / 2 := by omega
    cases hk : m / 2 with
    | zero => omega
    | succ j =>
      have hp1 : binom (m + 2) (j + 2) = binom (m + 1) (j + 2) + binom (m + 1) (j + 1) := rfl
      have hp2 : binom (m + 1) (j + 2) = binom m (j + 2) + binom m (j + 1) := rfl
      have hp3 : binom (m + 1) (j + 1) = binom m (j + 1) + binom m j := rfl
      rw [hp1, hp2, hp3]
      omega
  have hind : ∀ q, 2 ^ (q / 2) ≤ centralBinom q ∧ 2 ^ ((q + 1) / 2) ≤ centralBinom (q + 1) := by
    intro q
    induction q with
    | zero => decide
    | succ q ih =>
      refine ⟨ih.2, ?_⟩
      cases q with
      | zero => decide
      | succ r =>
        cases r with
        | zero => decide
        | succ s =>
          have hs : 2 * centralBinom (s + 2) ≤ centralBinom (s + 2 + 2) :=
            hstep (s + 2) (by omega)
          have hdiv : (s + 2 + 2) / 2 = (s + 2) / 2 + 1 := by omega
          have hpow : 2 ^ ((s + 2 + 2) / 2) = 2 * 2 ^ ((s + 2) / 2) := by
            rw [hdiv, Nat.pow_succ]
            omega
          have ih_s2 : 2 ^ ((s + 2) / 2) ≤ centralBinom (s + 2) := ih.1
          exact Nat.le_trans (by rw [hpow]; exact Nat.mul_le_mul_left 2 ih_s2) hs
  exact (hind M).1

/-- For every `M ≥ 4`, `centralBinom M > M`. -/
theorem centralBinom_gt_self {M : Nat} (hM : 4 ≤ M) : M < centralBinom M := by
  have hle : binom M 2 ≤ centralBinom M := binom_le_central M 2
  have htwo := binom_two_right M
  have hgt : 2 * M < M * (M - 1) := by
    have hm1 : 3 ≤ M - 1 := by omega
    have : 2 * M < 3 * M := by omega
    have : 3 * M ≤ (M - 1) * M := Nat.mul_le_mul_right M hm1
    rw [Nat.mul_comm M (M - 1)]
    omega
  omega

theorem lt_two_pow_self (m : Nat) : m < 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.pow_succ]
    omega

theorem sq_le_two_pow {m : Nat} (hm : 4 ≤ m) : m * m ≤ 2 ^ m := by
  have haux : ∀ k, (k + 4) * (k + 4) ≤ 2 ^ (k + 4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hexp : 2 ^ (k + 1 + 4) = 2 * 2 ^ (k + 4) := by
        have : k + 1 + 4 = (k + 4) + 1 := by omega
        rw [this, Nat.pow_succ]
        omega
      rw [hexp]
      have hlin : 2 * (k + 4) + 1 ≤ (k + 4) * (k + 4) := by
        have : 3 * (k + 4) ≤ (k + 4) * (k + 4) := Nat.mul_le_mul_right (k + 4) (by omega)
        omega
      have hsq : (k + 1 + 4) * (k + 1 + 4) = (k + 4) * (k + 4) + (2 * (k + 4) + 1) := by
        have h1 : k + 1 + 4 = (k + 4) + 1 := by omega
        rw [h1, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      omega
  have hk : (m - 4) + 4 = m := by omega
  have hres := haux (m - 4)
  rwa [hk] at hres

theorem pow_le_exp_base (n d : Nat) : n ^ d ≤ (2 ^ d) ^ n := by
  have hn : n ≤ 2 ^ n := Nat.le_of_lt (lt_two_pow_self n)
  have hpow : ∀ (a b k : Nat), a ≤ b → a ^ k ≤ b ^ k := by
    intro a b k hab
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hab
  have h1 : n ^ d ≤ (2 ^ n) ^ d := hpow n (2 ^ n) d hn
  have h2 : (2 ^ n) ^ d = (2 ^ d) ^ n := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  omega

end SpernerFD
