/-
  SpernerFD/Antichain.lean
  General theory of antichains, chains, and the Sperner number (width) of a
  finite poset, specialized to both `FD n` and `FD0 n`:
    * Exact characterization of `spernerNumber` as the maximum size of an antichain;
    * Constructive chain-cover upper bound (easy direction of Dilworth's theorem);
    * Equality `spernerFD0 n = spernerFD n` for all `n ≥ 1`;
    * Classic Sperner embedding of elementary conjunctions giving
      `spernerFD n ≥ centralBinom n` for all `n` (so `spernerCorrectionFD n ≥ 0`).
-/

import SpernerFD.Lattice

namespace SpernerFD

/-! ## 1. Antichains, Chains, and Constructive Sperner Number -/

/-- A duplicate-free list `A` in `(α, le)` is an antichain if no two distinct elements
    of `A` are comparable (`le x y → x = y`). -/
def IsAntichain {α : Type u} (le : α → α → Prop) (A : List α) : Prop :=
  NoDup A ∧ ∀ x ∈ A, ∀ y ∈ A, le x y → x = y

/-- A list `C` in `(α, le)` is a chain if any two elements in `C` are comparable. -/
def IsChain {α : Type u} (le : α → α → Prop) (C : List α) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x

instance instDecidableIsAntichain {α : Type u} (le : α → α → Prop)
    [DecidableEq α] [DecidableRel le] (A : List α) : Decidable (IsAntichain le A) :=
  inferInstanceAs (Decidable (NoDup A ∧ ∀ x ∈ A, ∀ y ∈ A, le x y → x = y))

instance instDecidableIsChain {α : Type u} (le : α → α → Prop)
    [DecidableRel le] (C : List α) : Decidable (IsChain le C) :=
  inferInstanceAs (Decidable (∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x))

theorem isAntichain_nil {α : Type u} (le : α → α → Prop) : IsAntichain le [] :=
  ⟨noDup_nil, fun _ hx => nomatch hx⟩

theorem isAntichain_singleton {α : Type u} {le : α → α → Prop} (a : α) :
    IsAntichain le [a] :=
  ⟨noDup_singleton a, fun _ hx _ hy _ => by
    rcases List.mem_singleton.mp hx with rfl
    rcases List.mem_singleton.mp hy with rfl
    rfl⟩

/-- Maximum length of a pairwise-incomparable list in `candidates`. -/
def maxIncompLength {α : Type u} (le : α → α → Prop) [DecidableEq α] [DecidableRel le] :
    List (List α) → Nat
  | [] => 0
  | B :: rest =>
    let r := maxIncompLength le rest
    if decide (∀ x ∈ B, ∀ y ∈ B, le x y → x = y) then
      if B.length ≤ r then r else B.length
    else r

/-- Constructive Sperner number (width) of a finite poset enumerated by `univ`. -/
def spernerNumber {α : Type u} (le : α → α → Prop) [DecidableEq α] [DecidableRel le]
    (univ : List α) : Nat :=
  maxIncompLength le (allSublists univ)

theorem le_maxIncompLength_of_mem {α : Type u} {le : α → α → Prop}
    [DecidableEq α] [DecidableRel le] {candidates : List (List α)} {B : List α}
    (hmem : B ∈ candidates) (hincomp : ∀ x ∈ B, ∀ y ∈ B, le x y → x = y) :
    B.length ≤ maxIncompLength le candidates := by
  induction candidates with
  | nil => nomatch hmem
  | cons C rest ih =>
    simp only [maxIncompLength]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp only [decide_eq_true hincomp, ↓reduceIte]
      split <;> omega
    · have ihr := ih hrest
      split
      · split <;> omega
      · exact ihr

theorem maxIncompLength_achieved_aux {α : Type u} {le : α → α → Prop}
    [DecidableEq α] [DecidableRel le] (candidates : List (List α)) :
    maxIncompLength le candidates = 0 ∨
      ∃ B ∈ candidates, (∀ x ∈ B, ∀ y ∈ B, le x y → x = y) ∧
        B.length = maxIncompLength le candidates := by
  induction candidates with
  | nil => exact Or.inl rfl
  | cons D rest ih =>
    simp only [maxIncompLength]
    split
    · next hD =>
      have hDincomp : ∀ x ∈ D, ∀ y ∈ D, le x y → x = y := of_decide_eq_true hD
      rcases ih with hz | ⟨B, hBm, hBi, hBl⟩
      · right
        refine ⟨D, List.mem_cons_self .., hDincomp, ?_⟩
        rw [hz]
        split <;> omega
      · right
        split
        · exact ⟨B, List.mem_cons_of_mem D hBm, hBi, hBl⟩
        · exact ⟨D, List.mem_cons_self .., hDincomp, rfl⟩
    · rcases ih with hz | ⟨B, hBm, hBi, hBl⟩
      · exact Or.inl hz
      · exact Or.inr ⟨B, List.mem_cons_of_mem D hBm, hBi, hBl⟩

/-- **Attainability:** `spernerNumber le univ` is achieved by an actual antichain. -/
theorem spernerNumber_achieved {α : Type u} {le : α → α → Prop}
    [DecidableEq α] [DecidableRel le] {univ : List α} (hnd : NoDup univ) :
    ∃ A : List α, IsAntichain le A ∧ A.length = spernerNumber le univ := by
  unfold spernerNumber
  rcases maxIncompLength_achieved_aux (le := le) (allSublists univ) with hz | ⟨B, hBm, hBi, hBl⟩
  · exact ⟨[], isAntichain_nil le, hz.symm⟩
  · exact ⟨B, ⟨noDup_of_mem_allSublists hnd hBm, hBi⟩, hBl⟩

/-- **Maximality:** Every antichain in `(α, le)` has length at most `spernerNumber le univ`. -/
theorem antichain_length_le_spernerNumber {α : Type u} {le : α → α → Prop}
    [DecidableEq α] [DecidableRel le] {univ : List α}
    (huniv : ∀ x : α, x ∈ univ) {A : List α} (hA : IsAntichain le A) :
    A.length ≤ spernerNumber le univ := by
  let B := univ.filter (fun x => decide (x ∈ A))
  have hBm : B ∈ allSublists univ := filter_mem_allSublists _ univ
  have hBsub : ∀ x ∈ B, x ∈ A := by
    intro x hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  have hBincomp : ∀ x ∈ B, ∀ y ∈ B, le x y → x = y :=
    fun x hx y hy hxy => hA.2 x (hBsub x hx) y (hBsub y hy) hxy
  have hBle : B.length ≤ spernerNumber le univ :=
    le_maxIncompLength_of_mem hBm hBincomp
  have hAsubB : ∀ x ∈ A, x ∈ B := by
    intro x hxA
    exact List.mem_filter.mpr ⟨huniv x, decide_eq_true hxA⟩
  exact Nat.le_trans (noDup_length_le_of_subset hA.1 hAsubB) hBle

/-- **Exact Characterization of `spernerNumber`.** -/
theorem spernerNumber_eq_iff {α : Type u} {le : α → α → Prop}
    [DecidableEq α] [DecidableRel le] {univ : List α}
    (hnd : NoDup univ) (huniv : ∀ x : α, x ∈ univ) (w : Nat) :
    spernerNumber le univ = w ↔
      (∃ A : List α, IsAntichain le A ∧ A.length = w) ∧
      (∀ A : List α, IsAntichain le A → A.length ≤ w) := by
  constructor
  · rintro rfl
    exact ⟨spernerNumber_achieved hnd, fun _ hA => antichain_length_le_spernerNumber huniv hA⟩
  · rintro ⟨⟨A₀, hA₀, rfl⟩, hmax⟩
    have h₁ : A₀.length ≤ spernerNumber le univ := antichain_length_le_spernerNumber huniv hA₀
    obtain ⟨A₁, hA₁, hlen₁⟩ := spernerNumber_achieved (le := le) hnd
    have h₂ : spernerNumber le univ ≤ A₀.length := hlen₁ ▸ hmax A₁ hA₁
    omega

/-! ## 2. Constructive Chain-Cover Upper Bound (Easy Direction of Dilworth) -/

theorem length_le_filter_neg_add_one {α : Type u} (p : α → Bool) {A : List α}
    (hnd : NoDup A) (huniq : ∀ x ∈ A, ∀ y ∈ A, p x = true → p y = true → x = y) :
    A.length ≤ (A.filter (fun x => !p x)).length + 1 := by
  induction A with
  | nil => simp
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hnd
    simp only [List.filter]
    cases hpa : p a with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, List.length_cons]
      have iht := ih ht (fun x hx y hy hpx hpy =>
        huniq x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hpx hpy)
      omega
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hfilter_id : ∀ (L : List α), (∀ x ∈ L, (!p x) = true) → L.filter (fun x => !p x) = L := by
        intro L hallL
        induction L with
        | nil => rfl
        | cons y ys ihL =>
          simp only [List.filter, hallL y (List.mem_cons_self ..), ↓reduceIte]
          rw [ihL (fun z hz => hallL z (List.mem_cons_of_mem y hz))]
      have hall : t.filter (fun x => !p x) = t := by
        apply hfilter_id
        intro x hxt
        cases hpx : p x with
        | false => rfl
        | true =>
          have hxa : x = a :=
            huniq x (List.mem_cons_of_mem a hxt) a (List.mem_cons_self ..) hpx hpa
          exact absurd (hxa ▸ hxt) hat
      rw [hall]
      exact Nat.le_refl _

/-- Every antichain covered by `chains` has length at most `chains.length`. -/
theorem antichain_le_chain_cover {α : Type u} [DecidableEq α] {le : α → α → Prop}
    {A : List α} (hA : IsAntichain le A) {chains : List (List α)}
    (hchains : ∀ C ∈ chains, IsChain le C)
    (hcover : ∀ x ∈ A, ∃ C ∈ chains, x ∈ C) :
    A.length ≤ chains.length := by
  induction chains generalizing A with
  | nil =>
    cases A with
    | nil => exact Nat.le_refl 0
    | cons a _ =>
      rcases hcover a (List.mem_cons_self ..) with ⟨_, hm, _⟩
      nomatch hm
  | cons C rest ih =>
    have hCchain : IsChain le C := hchains C (List.mem_cons_self ..)
    let p : α → Bool := fun x => decide (x ∈ C)
    let A' := A.filter (fun x => !p x)
    have hA'nd : NoDup A' := noDup_filter _ hA.1
    have hA'sub : ∀ x ∈ A', x ∈ A := fun _ hx => (List.mem_filter.mp hx).1
    have hA' : IsAntichain le A' :=
      ⟨hA'nd, fun x hx y hy hxy => hA.2 x (hA'sub x hx) y (hA'sub y hy) hxy⟩
    have hcover' : ∀ x ∈ A', ∃ D ∈ rest, x ∈ D := by
      intro x hxA'
      have hxA : x ∈ A := hA'sub x hxA'
      have hnp : (!p x) = true := (List.mem_filter.mp hxA').2
      have hxnotC : x ∉ C := by
        intro hxC
        have hp : p x = true := decide_eq_true hxC
        rw [hp] at hnp
        nomatch hnp
      rcases hcover x hxA with ⟨D, hDm, hxD⟩
      rcases List.mem_cons.mp hDm with rfl | hDrest
      · exact absurd hxD hxnotC
      · exact ⟨D, hDrest, hxD⟩
    have ihA' := ih hA' (fun D hD => hchains D (List.mem_cons_of_mem C hD)) hcover'
    have hstep : A.length ≤ A'.length + 1 := by
      apply length_le_filter_neg_add_one p hA.1
      intro x hxA y hyA hpx hpy
      have hxC : x ∈ C := of_decide_eq_true hpx
      have hyC : y ∈ C := of_decide_eq_true hpy
      rcases hCchain x hxC y hyC with hxy | hyx
      · exact hA.2 x hxA y hyA hxy
      · exact (hA.2 y hyA x hxA hyx).symm
    simp only [List.length_cons]
    omega

/-- Certificate theorem: if `A` is an antichain of length `w` and `chains` is a list of
    `w` chains covering `univ`, then `spernerNumber le univ = w`. -/
theorem spernerNumber_eq_of_antichain_and_chains {α : Type u}
    [DecidableEq α] {le : α → α → Prop} [DecidableRel le]
    {univ : List α} (hnd : NoDup univ) (huniv : ∀ x : α, x ∈ univ)
    {A : List α} (hA : IsAntichain le A)
    {chains : List (List α)} (hchains : ∀ C ∈ chains, IsChain le C)
    (hcover : ∀ x ∈ univ, ∃ C ∈ chains, x ∈ C)
    (hlen : A.length = chains.length) :
    spernerNumber le univ = A.length := by
  rw [spernerNumber_eq_iff hnd huniv]
  refine ⟨⟨A, hA, rfl⟩, fun B hB => ?_⟩
  rw [hlen]
  exact antichain_le_chain_cover hB hchains (fun x _ => hcover x (huniv x))

/-! ## 3. Sperner Numbers of `FD n` and `FD0 n` and Signed Central Corrections -/

/-- The Sperner number (maximum antichain size) of the bounded free distributive lattice `FD(n)`. -/
def spernerFD (n : Nat) : Nat :=
  spernerNumber FDLe (allFD n)

/-- The Sperner number (maximum antichain size) of the unbounded free distributive lattice `FD_0(n)`. -/
def spernerFD0 (n : Nat) : Nat :=
  spernerNumber FD0Le (allFD0 n)

/-- Signed central correction `Δ(n) = w(FD(n)) - binom(n, ⌊n/2⌋)` in `ℤ`. -/
def spernerCorrectionFD (n : Nat) : Int :=
  (spernerFD n : Int) - (centralBinom n : Int)

/-- Signed central correction `Δ_0(n) = w(FD_0(n)) - binom(n, ⌊n/2⌋)` in `ℤ`. -/
def spernerCorrectionFD0 (n : Nat) : Int :=
  (spernerFD0 n : Int) - (centralBinom n : Int)

theorem spernerFD_achieved (n : Nat) :
    ∃ A : List (FD n), IsAntichain FDLe A ∧ A.length = spernerFD n :=
  spernerNumber_achieved (noDup_allFD n)

theorem antichain_le_spernerFD {n : Nat} {A : List (FD n)} (hA : IsAntichain FDLe A) :
    A.length ≤ spernerFD n :=
  antichain_length_le_spernerNumber mem_allFD hA

theorem spernerFD0_achieved (n : Nat) :
    ∃ A : List (FD0 n), IsAntichain FD0Le A ∧ A.length = spernerFD0 n :=
  spernerNumber_achieved (noDup_allFD0 n)

theorem antichain_le_spernerFD0 {n : Nat} {A : List (FD0 n)} (hA : IsAntichain FD0Le A) :
    A.length ≤ spernerFD0 n :=
  antichain_length_le_spernerNumber mem_allFD0 hA

/-! ## 4. Equality `spernerFD0 n = spernerFD n` for All `n ≥ 1` -/

/-- Helper lifting a list of elements of `FD n` that avoid `botFD` and `topFD` into `FD0 n`. -/
def liftListToFD0 {n : Nat} : (A : List (FD n)) →
    (∀ f ∈ A, f.val (botCube n) = false ∧ f.val (topCube n) = true) → List (FD0 n)
  | [], _ => []
  | f :: t, h =>
    ⟨f, h f (List.mem_cons_self ..)⟩ ::
      liftListToFD0 t (fun g hg => h g (List.mem_cons_of_mem f hg))

theorem map_val_liftListToFD0 {n : Nat} (A : List (FD n))
    (h : ∀ f ∈ A, f.val (botCube n) = false ∧ f.val (topCube n) = true) :
    (liftListToFD0 A h).map Subtype.val = A := by
  induction A with
  | nil => rfl
  | cons f t ih =>
    simp only [liftListToFD0, List.map_cons]
    rw [ih]

/-- **Structural Invariance Theorem:** Adjoining `⊥` and `⊤` to the non-empty lattice
    `FD_0(n)` (`n ≥ 1`) preserves maximum antichain size: `spernerFD0 n = spernerFD n`. -/
theorem spernerFD0_eq_spernerFD {n : Nat} (hn : 1 ≤ n) :
    spernerFD0 n = spernerFD n := by
  -- 1. `spernerFD0 n ≤ spernerFD n`
  obtain ⟨A₀, hA₀, hlen₀⟩ := spernerFD0_achieved n
  have hmap : IsAntichain FDLe (A₀.map Subtype.val) := by
    refine ⟨noDup_map (fun _ _ _ _ h => fd0_ext h) hA₀.1, ?_⟩
    intro x hx y hy hxy
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hA₀.2 a ha b hb hxy)
  have hle₁ : spernerFD0 n ≤ spernerFD n := by
    have := antichain_le_spernerFD hmap
    rw [List.length_map, hlen₀] at this
    exact this
  -- 2. `spernerFD n ≤ spernerFD0 n`
  have hposFD0 : 1 ≤ spernerFD0 n := by
    cases n with
    | zero => omega
    | succ m =>
      have hsing := isAntichain_singleton (le := FD0Le) (genFD0 ⟨0, Nat.zero_lt_succ m⟩)
      exact antichain_le_spernerFD0 hsing
  obtain ⟨A, hA, hlen⟩ := spernerFD_achieved n
  by_cases hA1 : A.length ≤ 1
  · omega
  · have hnoBot : botFD n ∉ A := by
      intro hbot
      cases A with
      | nil => simp at hA1
      | cons a₁ rest =>
        cases rest with
        | nil => simp at hA1
        | cons a₂ rest' =>
          obtain ⟨ha₁_not, ha₂_not, _⟩ := hA.1
          have ha₁_ne_a₂ : a₁ ≠ a₂ := fun h => ha₁_not (h ▸ List.mem_cons_self ..)
          by_cases hb1 : a₁ = botFD n
          · subst hb1
            have := hA.2 (botFD n) (List.mem_cons_self ..) a₂
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (botFD_le a₂)
            exact ha₁_ne_a₂ this
          · have hb := hA.2 (botFD n) hbot a₁ (List.mem_cons_self ..) (botFD_le a₁)
            exact hb1 hb.symm
    have hnoTop : topFD n ∉ A := by
      intro htop
      cases A with
      | nil => simp at hA1
      | cons a₁ rest =>
        cases rest with
        | nil => simp at hA1
        | cons a₂ rest' =>
          obtain ⟨ha₁_not, _⟩ := hA.1
          have ha₁_ne_a₂ : a₁ ≠ a₂ := fun h => ha₁_not (h ▸ List.mem_cons_self ..)
          by_cases ht1 : a₁ = topFD n
          · subst ht1
            have := hA.2 a₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
              (topFD n) (List.mem_cons_self ..) (le_topFD a₂)
            exact ha₁_ne_a₂ this.symm
          · have ht := hA.2 a₁ (List.mem_cons_self ..) (topFD n) htop (le_topFD a₁)
            exact ht1 ht
    have hmem0 : ∀ f ∈ A, f.val (botCube n) = false ∧ f.val (topCube n) = true := by
      intro f hfA
      rcases fd_trichotomy f with rfl | rfl | h01
      · exact absurd hfA hnoBot
      · exact absurd hfA hnoTop
      · exact h01
    let B₀ := liftListToFD0 A hmem0
    have hB₀val : B₀.map Subtype.val = A := map_val_liftListToFD0 A hmem0
    have hB₀len : B₀.length = A.length := by
      have := congrArg List.length hB₀val
      simpa using this
    have hB₀ : IsAntichain FD0Le B₀ := by
      refine ⟨?_, ?_⟩
      · have hnd_aux : ∀ (L : List (FD0 n)), NoDup (L.map Subtype.val) → NoDup L := by
          intro L hndL
          induction L with
          | nil => exact trivial
          | cons x xs ih =>
            obtain ⟨hx, hxs⟩ := hndL
            exact ⟨fun hmem => hx (List.mem_map.mpr ⟨x, hmem, rfl⟩), ih hxs⟩
        exact hnd_aux B₀ (hB₀val.symm ▸ hA.1)
      · intro x hx y hy hxy
        apply fd0_ext
        have hxA : x.val ∈ A := hB₀val ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
        have hyA : y.val ∈ A := hB₀val ▸ List.mem_map.mpr ⟨y, hy, rfl⟩
        exact hA.2 x.val hxA y.val hyA hxy
    have hle₂ : spernerFD n ≤ spernerFD0 n := by
      have := antichain_le_spernerFD0 hB₀
      omega
    omega

theorem spernerCorrectionFD0_eq_spernerCorrectionFD {n : Nat} (hn : 1 ≤ n) :
    spernerCorrectionFD0 n = spernerCorrectionFD n := by
  simp [spernerCorrectionFD0, spernerCorrectionFD, spernerFD0_eq_spernerFD hn]

/-! ## 5. Classic Sperner Embedding of Elementary Conjunctions -/

/-- Principal upset / elementary conjunction `⋀_{u_i = true} x_i` in `FD n`. -/
def conjFD {n : Nat} (u : Cube n) : FD n :=
  ⟨fun x => decide (CubeLe u x),
   fun _ _ hxy hux => decide_eq_true (cubeLe_trans (of_decide_eq_true hux) hxy)⟩

theorem conjFD_le_iff {n : Nat} {u v : Cube n} :
    FDLe (conjFD u) (conjFD v) ↔ CubeLe v u := by
  constructor
  · intro h
    have hu : (conjFD u).val u = true := decide_eq_true (cubeLe_refl u)
    exact of_decide_eq_true (h u hu)
  · intro hvu _ hux
    exact decide_eq_true (cubeLe_trans hvu (of_decide_eq_true hux))

/-- For every `n` and `k`, the elementary conjunctions of weight `k` form an antichain
    of size `binom n k` in `FD n`. -/
theorem binom_le_spernerFD (n k : Nat) : binom n k ≤ spernerFD n := by
  let L := layerCubes n k
  let A := L.map conjFD
  have hA : IsAntichain FDLe A := by
    refine ⟨?_, ?_⟩
    · apply noDup_map _ (noDup_layerCubes n k)
      intro u _ v _ huv
      have hle : FDLe (conjFD u) (conjFD v) := by rw [huv]; exact fdLe_refl _
      have hge : FDLe (conjFD v) (conjFD u) := by rw [huv]; exact fdLe_refl _
      exact cubeLe_antisymm (conjFD_le_iff.mp hge) (conjFD_le_iff.mp hle)
    · intro f hf g hg hfg
      rcases List.mem_map.mp hf with ⟨u, huL, rfl⟩
      rcases List.mem_map.mp hg with ⟨v, hvL, rfl⟩
      have hvu : CubeLe v u := conjFD_le_iff.mp hfg
      have hwu : weight u = k := (mem_layerCubes_iff u).mp huL
      have hwv : weight v = k := (mem_layerCubes_iff v).mp hvL
      have heq : v = u := cubeLe_eq_of_weight_eq hvu (by omega)
      rw [heq]
  have hle := antichain_le_spernerFD hA
  simp only [A, L, List.length_map, length_layerCubes] at hle
  exact hle

/-- **Classic Sperner Lower Bound:** `w(FD(n)) ≥ binom(n, ⌊n/2⌋)` for all `n`,
    so the central correction `Δ(n)` is always non-negative (`Δ(n) ≥ 0`). -/
theorem centralBinom_le_spernerFD (n : Nat) : centralBinom n ≤ spernerFD n :=
  binom_le_spernerFD n (n / 2)

theorem spernerCorrectionFD_nonneg (n : Nat) : 0 ≤ spernerCorrectionFD n := by
  unfold spernerCorrectionFD
  have := centralBinom_le_spernerFD n
  omega

theorem spernerCorrectionFD0_nonneg {n : Nat} (hn : 1 ≤ n) : 0 ≤ spernerCorrectionFD0 n := by
  rw [spernerCorrectionFD0_eq_spernerCorrectionFD hn]
  exact spernerCorrectionFD_nonneg n

end SpernerFD
