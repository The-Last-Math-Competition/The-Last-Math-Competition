/-
  Conjecture 00000001290 — Combinatorial Game Theory Foundations
  Core Lean 4.19.0 (zero external dependencies)
-/

namespace Conjecture00000001290

/-- An impartial game under normal play with positions indexed by `Nat`,
    specified by its legal move relation `move n m` ("from `n` move to `m`"). -/
structure ImpartialGame where
  move : Nat → Nat → Prop

namespace ImpartialGame

/-- Every position has only finitely many legal options. -/
def FinitelyBranching (G : ImpartialGame) : Prop :=
  ∀ n : Nat, ∃ L : List Nat, ∀ m : Nat, G.move n m ↔ m ∈ L

/-- There is no infinite sequence of legal moves (well-foundedness of options). -/
def NoInfinitePlay (G : ImpartialGame) : Prop :=
  WellFounded (fun m n => G.move n m)

/-- A game is short iff it is finitely branching and has no infinite plays. -/
def IsShort (G : ImpartialGame) : Prop :=
  G.FinitelyBranching ∧ G.NoInfinitePlay

/-- Absolute step distance `|a - b|` on `Nat`. -/
def natDist (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Bounded-step (metric) locality: legal moves change the position index by at most `K`. -/
def IsBoundedStepLocal (G : ImpartialGame) : Prop :=
  ∃ K : Nat, ∀ n m : Nat, G.move n m → natDist n m ≤ K

/-- Bounded out-degree locality: every position has at most `B` legal options. -/
def IsBoundedOutDegree (G : ImpartialGame) : Prop :=
  ∃ B : Nat, ∀ n : Nat, ∃ L : List Nat, L.length ≤ B ∧ ∀ m : Nat, G.move n m ↔ m ∈ L

/-- Translation-invariant finite subtraction game locality: moves subtract `s ∈ S`
    for a finite list `S` of positive integers. -/
def IsFiniteSubtractionGame (G : ImpartialGame) : Prop :=
  ∃ S : List Nat, (∀ s : Nat, s ∈ S → 0 < s) ∧
    ∀ n m : Nat, G.move n m ↔ ∃ s : Nat, s ∈ S ∧ s ≤ n ∧ m = n - s

/-- `g : Nat → Nat` satisfies the Sprague–Grundy minimum-excludant (`mex`) equation
    at every position of `G`. -/
def IsGrundySeq (G : ImpartialGame) (g : Nat → Nat) : Prop :=
  (∀ n m : Nat, G.move n m → g m ≠ g n) ∧
  (∀ n v : Nat, v < g n → ∃ m : Nat, G.move n m ∧ g m = v)

end ImpartialGame

/-! ### Well-foundedness and finite-branching helpers -/

theorem no_infinite_seq_of_noInfinitePlay {G : ImpartialGame}
    (hwf : G.NoInfinitePlay) :
    ¬ ∃ f : Nat → Nat, ∀ k : Nat, G.move (f k) (f (k + 1)) := by
  intro ⟨f, hf⟩
  have hacc : ∀ x : Nat, Acc (fun m n => G.move n m) x → (∃ k : Nat, f k = x) → False := by
    intro x hx
    induction hx with
    | intro y _ ih =>
      intro ⟨k, hk⟩
      subst hk
      exact ih (f (k + 1)) (hf k) ⟨k + 1, rfl⟩
  exact hacc (f 0) (hwf.apply (f 0)) ⟨0, rfl⟩

private theorem acc_of_lt_aux {G : ImpartialGame}
    (hprog : ∀ n m : Nat, G.move n m → m < n) :
    ∀ bound n : Nat, n < bound → Acc (fun m k => G.move k m) n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | bound + 1, n, h =>
    Acc.intro n (fun m hm =>
      acc_of_lt_aux hprog bound m (Nat.lt_of_lt_of_le (hprog n m hm) (Nat.le_of_lt_succ h)))

theorem noInfinitePlay_of_lt {G : ImpartialGame}
    (hprog : ∀ n m : Nat, G.move n m → m < n) : G.NoInfinitePlay :=
  ⟨fun n => acc_of_lt_aux hprog (n + 1) n (Nat.lt_succ_self n)⟩

/-- Descending list `[n - 1, ..., 0]` of all natural numbers `< n`. -/
def rangeList : Nat → List Nat
  | 0 => []
  | n + 1 => n :: rangeList n

theorem length_rangeList : (n : Nat) → (rangeList n).length = n
  | 0 => rfl
  | n + 1 => by simp [rangeList, length_rangeList n]

theorem mem_rangeList {m : Nat} : {n : Nat} → (m ∈ rangeList n ↔ m < n)
  | 0 => by simp [rangeList]
  | n + 1 => by
    simp only [rangeList, List.mem_cons]
    rw [mem_rangeList (n := n)]
    omega

/-- Any game whose options from `n` lie below `bound n` with a Boolean test is finitely branching. -/
theorem finitelyBranching_of_boolBound {G : ImpartialGame}
    (bound : Nat → Nat) (test : Nat → Nat → Bool)
    (hspec : ∀ n m : Nat, G.move n m ↔ (m < bound n ∧ test n m = true)) :
    G.FinitelyBranching := by
  intro n
  refine ⟨(rangeList (bound n)).filter (test n), ?_⟩
  intro m
  rw [hspec n m, List.mem_filter, mem_rangeList]

theorem finitelyBranching_of_boundedOutDegree {G : ImpartialGame}
    (hdeg : G.IsBoundedOutDegree) : G.FinitelyBranching := by
  rcases hdeg with ⟨_, hB⟩
  intro n
  rcases hB n with ⟨L, _, hL⟩
  exact ⟨L, hL⟩

/-! ### Constructive minimum excludant (`listMex`) on `List Nat` -/

/-- Decidable membership test on `List Nat`. -/
def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => (x == y) || memNat x ys

theorem memNat_iff (x : Nat) : (L : List Nat) → (memNat x L = true ↔ x ∈ L)
  | [] => by
    simp [memNat]
  | y :: ys => by
    simp only [memNat, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h
      cases h with
      | inl hxy =>
        subst hxy
        exact List.Mem.head ys
      | inr hmem =>
        exact List.Mem.tail y ((memNat_iff x ys).mp hmem)
    · intro h
      cases h with
      | head _ =>
        exact Or.inl rfl
      | tail _ hmem =>
        exact Or.inr ((memNat_iff x ys).mpr hmem)

/-- Strict upper bound for all elements of `L`. -/
def listBound : List Nat → Nat
  | [] => 0
  | x :: xs => x + 1 + listBound xs

theorem lt_listBound {x : Nat} : {L : List Nat} → x ∈ L → x < listBound L
  | _ :: _, List.Mem.head _ => by
    simp [listBound]
    omega
  | _ :: xs, List.Mem.tail _ h => by
    have ih := lt_listBound h
    simp [listBound]
    omega

theorem listBound_not_mem (L : List Nat) : listBound L ∉ L := by
  intro h
  have hlt := lt_listBound h
  omega

/-- Upward search for the smallest natural number `≥ start` not in `L`. -/
def findFrom (L : List Nat) (start fuel : Nat) : Nat :=
  if memNat start L then
    match fuel with
    | 0 => start
    | fuel' + 1 => findFrom L (start + 1) fuel'
  else
    start

/-- Constructive minimum excludant of a finite list of natural numbers. -/
def listMex (L : List Nat) : Nat :=
  findFrom L 0 (listBound L)

private theorem findFrom_spec (L : List Nat) :
    ∀ (fuel start : Nat),
      start + fuel = listBound L →
      findFrom L start fuel ∉ L ∧
      start ≤ findFrom L start fuel ∧
      (∀ v : Nat, start ≤ v → v < findFrom L start fuel → v ∈ L)
  | 0, start, hsum => by
    have hst : start = listBound L := by omega
    subst hst
    have hnot : listBound L ∉ L := listBound_not_mem L
    have hmemf : memNat (listBound L) L = false := by
      cases hm : memNat (listBound L) L with
      | false => rfl
      | true => exact absurd ((memNat_iff _ L).mp hm) hnot
    have hval : findFrom L (listBound L) 0 = listBound L := by
      simp [findFrom, hmemf]
    rw [hval]
    exact ⟨hnot, Nat.le_refl _, fun _ h1 h2 => by omega⟩
  | fuel' + 1, start, hsum => by
    unfold findFrom
    cases hm : memNat start L with
    | false =>
      dsimp
      refine ⟨?_, Nat.le_refl _, fun _ h1 h2 => by omega⟩
      intro hmem
      have ht := (memNat_iff start L).mpr hmem
      rw [hm] at ht
      contradiction
    | true =>
      dsimp
      have hmem_start : start ∈ L := (memNat_iff start L).mp hm
      have ih := findFrom_spec L fuel' (start + 1) (by omega)
      rcases ih with ⟨hnot, hle, hall⟩
      refine ⟨hnot, by omega, ?_⟩
      intro v hv1 hv2
      by_cases hvs : v = start
      · subst hvs
        exact hmem_start
      · exact hall v (by omega) hv2

theorem listMex_not_mem (L : List Nat) : listMex L ∉ L :=
  (findFrom_spec L (listBound L) 0 (by omega)).1

theorem lt_listMex_mem {L : List Nat} {v : Nat} (hv : v < listMex L) : v ∈ L :=
  (findFrom_spec L (listBound L) 0 (by omega)).2.2 v (Nat.zero_le v) hv

/-- Remove only the first occurrence of `x` from `L`. -/
def eraseOne (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseOne x ys

theorem eraseOne_length_lt (x : Nat) : {L : List Nat} → x ∈ L → (eraseOne x L).length < L.length
  | _ :: ys, List.Mem.head _ => by
    simp [eraseOne]
  | y :: ys, List.Mem.tail _ h => by
    unfold eraseOne
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy]
      have ih := eraseOne_length_lt x h
      omega

theorem mem_eraseOne_of_ne {x z : Nat} (hxz : z ≠ x) :
    {L : List Nat} → z ∈ L → z ∈ eraseOne x L
  | _ :: _, List.Mem.head _ => by
    unfold eraseOne
    have hzx : ¬ (x = z) := fun h => hxz h.symm
    simp [hzx]
  | y :: ys, List.Mem.tail _ h => by
    unfold eraseOne
    by_cases hxy : x = y
    · simp only [hxy, ↓reduceIte]
      exact h
    · simp only [hxy, ↓reduceIte, List.mem_cons]
      exact Or.inr (mem_eraseOne_of_ne hxz h)

theorem length_gt_of_all_le_mem :
    ∀ (k : Nat) (L : List Nat), (∀ v : Nat, v ≤ k → v ∈ L) → k < L.length
  | 0, L, h => by
    have h0 : 0 ∈ L := h 0 (Nat.le_refl 0)
    cases L with
    | nil => cases h0
    | cons _ _ => simp
  | k + 1, L, h => by
    have hk1 : k + 1 ∈ L := h (k + 1) (Nat.le_refl _)
    have hlen : (eraseOne (k + 1) L).length < L.length := eraseOne_length_lt (k + 1) hk1
    have ih : k < (eraseOne (k + 1) L).length := by
      apply length_gt_of_all_le_mem k (eraseOne (k + 1) L)
      intro v hv
      exact mem_eraseOne_of_ne (by omega) (h v (by omega))
    omega

/-- Pigeonhole upper bound: `listMex L ≤ L.length`. -/
theorem listMex_le_length (L : List Nat) : listMex L ≤ L.length := by
  by_cases hle : listMex L ≤ L.length
  · exact hle
  · have hall : ∀ v : Nat, v ≤ L.length → v ∈ L := fun _ _ =>
      lt_listMex_mem (by omega)
    have hbad := length_gt_of_all_le_mem L.length L hall
    omega

/-! ### Existence, uniqueness, and degree bound for Sprague–Grundy sequences -/

theorem grundy_unique {G : ImpartialGame} (hwf : G.NoInfinitePlay)
    {g₁ g₂ : Nat → Nat} (hg₁ : G.IsGrundySeq g₁) (hg₂ : G.IsGrundySeq g₂) :
    ∀ n : Nat, g₁ n = g₂ n := by
  intro n
  induction (hwf.apply n) with
  | intro x _ ih =>
    by_cases hlt : g₁ x < g₂ x
    · rcases hg₂.2 x (g₁ x) hlt with ⟨m, hm, hgm⟩
      have heq : g₁ m = g₂ m := ih m hm
      exact absurd (heq.trans hgm) (hg₁.1 x m hm)
    · by_cases hgt : g₂ x < g₁ x
      · rcases hg₁.2 x (g₂ x) hgt with ⟨m, hm, hgm⟩
        have heq : g₁ m = g₂ m := ih m hm
        exact absurd (heq.symm.trans hgm) (hg₂.1 x m hm)
      · omega

private def mapOpts {G : ImpartialGame} {n : Nat} :
    (L : List Nat) → (∀ m : Nat, m ∈ L → G.move n m) →
    ((m : Nat) → G.move n m → Nat) → List Nat
  | [], _, _ => []
  | m :: ms, hL, recFn =>
    recFn m (hL m (List.Mem.head ms)) ::
      mapOpts ms (fun y hy => hL y (List.Mem.tail m hy)) recFn

private theorem mapOpts_eq_map {G : ImpartialGame} {n : Nat} (g : Nat → Nat) :
    (L : List Nat) → (hL : ∀ m : Nat, m ∈ L → G.move n m) →
    mapOpts L hL (fun m _ => g m) = L.map g
  | [], _ => rfl
  | _ :: ms, hL => by
    simp [mapOpts, mapOpts_eq_map g ms]

/-- Every short impartial game possesses a Sprague–Grundy sequence. -/
theorem short_has_grundy {G : ImpartialGame} (hshort : G.IsShort) :
    ∃ g : Nat → Nat, G.IsGrundySeq g := by
  rcases hshort with ⟨hfb, hwf⟩
  let opts : Nat → List Nat := fun n => Classical.choose (hfb n)
  have opts_spec : ∀ n m : Nat, G.move n m ↔ m ∈ opts n :=
    fun n => Classical.choose_spec (hfb n)
  let step : (n : Nat) → ((m : Nat) → G.move n m → Nat) → Nat :=
    fun n recFn => listMex (mapOpts (opts n) (fun m hm => (opts_spec n m).mpr hm) recFn)
  let g : Nat → Nat := WellFounded.fix hwf step
  have hg_eq : ∀ n : Nat, g n = listMex ((opts n).map g) := by
    intro n
    have hfix := WellFounded.fix_eq hwf step n
    dsimp [g, step] at hfix ⊢
    rw [hfix, mapOpts_eq_map g (opts n)]
  refine ⟨g, ?_, ?_⟩
  · intro n m hmove heq
    have hm_mem : m ∈ opts n := (opts_spec n m).mp hmove
    have hgm_mem : g m ∈ (opts n).map g := List.mem_map_of_mem hm_mem
    have hgn_mem : g n ∈ (opts n).map g := heq ▸ hgm_mem
    have hnot : g n ∉ (opts n).map g := by
      rw [hg_eq n]
      exact listMex_not_mem ((opts n).map g)
    exact hnot hgn_mem
  · intro n v hv
    rw [hg_eq n] at hv
    have hv_mem : v ∈ (opts n).map g := lt_listMex_mem hv
    rcases List.mem_map.mp hv_mem with ⟨m, hm_mem, hgm⟩
    exact ⟨m, (opts_spec n m).mpr hm_mem, hgm⟩

/-- Any Sprague–Grundy sequence of a bounded-outdegree game is uniformly bounded. -/
theorem grundy_le_outdegree {G : ImpartialGame} {B : Nat}
    (hdeg : ∀ n : Nat, ∃ L : List Nat, L.length ≤ B ∧ ∀ m : Nat, G.move n m ↔ m ∈ L)
    {g : Nat → Nat} (hg : G.IsGrundySeq g) :
    ∀ n : Nat, g n ≤ B := by
  intro n
  rcases hdeg n with ⟨L, hlen, hL⟩
  by_cases hle : g n ≤ L.length
  · omega
  · have hall : ∀ v : Nat, v ≤ L.length → v ∈ L.map g := by
      intro v hv
      rcases hg.2 n v (by omega) with ⟨m, hm, hgm⟩
      rw [← hgm]
      exact List.mem_map_of_mem ((hL m).mp hm)
    have hbad := length_gt_of_all_le_mem L.length (L.map g) hall
    simp at hbad

end Conjecture00000001290
