/-
  Conjecture 00000001242 — Complete Core Lean 4.19.0 Formalization and Disproof

  Official Conjecture:
  "Definition: The lamp lighting game (lit-only sigma-game).
   Conjecture: The graphs with min-lit number at most ⌈n/2⌉ are exactly those
   with an odd bipartition (a lit-only extremal characterization)."

  Summary of Formalized Results:
  1. Full definitions of finite simple undirected graphs, walks, connectivity,
     cycles, trees, bipartitions, and all four interpretations of "odd bipartition"
     (`existsSomeOdd`, `existsBothOdd`, `everySomeOdd`, `everyBothOdd`).
  2. Full definitions of the lit-only σ-game under both move rules in the literature:
     - `MoveRule.openNbr` (σ⁻: pressing a lit vertex v toggles N(v), keeping v lit),
     - `MoveRule.closedNbr` (σ⁺: pressing a lit vertex v toggles N[v] = {v} ∪ N(v)),
     together with exact `Nat`-valued extremal invariants `minLit` across all three
     standard objective conventions (`fromAllLit`, `worstAll`, `worstNonempty`)
     over the unbounded reflexive-transitive closure `Reach`.
  3. Positive non-vacuity and non-triviality witnesses:
     - `K_2` (`completeGraph 2`) is connected, satisfies `HasOddBipartition`
       under all four modes, and satisfies `minLit ≤ ⌈2/2⌉ = 1` under all six game conventions.
     - `emptyGraph 2` satisfies `minLit .openNbr .fromAllLit = 2 > 1 = ⌈2/2⌉`.
     - `octahedronGraph` (`K_{2,2,2}` on n = 6) is connected and satisfies
       `minLit .openNbr .worstAll > 3 = ⌈6/2⌉`.
  4. Infinite counterexample families refuting necessity (⟹):
     - Non-bipartite connected family: for ALL `n ≥ 3`, `completeGraph n` (`K_n`) is
       connected and non-bipartite (hence has no odd bipartition under any mode), yet
       `minLit rule mlMode (completeGraph n) ≤ ceilHalf n` under all 6 conventions.
       Minimal connected instance: `K_3` (`n = 3`).
     - Connected bipartite even-parts family: for ALL `k ≥ 1`, `evenCompleteBipartite k`
       (`K_{2k,2k}` on `n = 4k`) is connected and bipartite, has no odd bipartition
       under any mode, yet satisfies `minLit ≤ 2k = ceilHalf (4k)` under all 6 conventions.
     - Tree counterexample: `p4Graph` (`P_4` on `n = 4`) is a tree whose unique
       bipartition has even parts `(2, 2)`, yet satisfies `minLit ≤ ceilHalf 4 = 2`
       under all 6 conventions.
  5. Infinite counterexample families refuting sufficiency (⟸) under σ⁻:
     - For ALL `m ≥ 1`, both `emptyGraph (2 * m)` and `k2PlusEmpty m` (`K_2 ⊔ E_{2m}`,
       which has edges) possess odd-odd bipartitions yet have `minLit .openNbr > ⌈n/2⌉`.
  6. Master refutation theorems establishing `¬ Conjecture00000001242` across all 24
     convention combinations, as well as for connected graphs, connected bipartite
     graphs, and trees.
-/

namespace Conjecture00000001242

/-! ## 1. Ceiling Division and Finite Boolean Counting -/

/-- Exact natural-number ceiling `⌈n / 2⌉ = ⌊(n + 1) / 2⌋`. -/
def ceilHalf (n : Nat) : Nat := (n + 1) / 2

theorem ceilHalf_le_iff (n k : Nat) : ceilHalf n ≤ k ↔ n ≤ 2 * k := by
  unfold ceilHalf
  omega

theorem le_two_mul_ceilHalf (n : Nat) : n ≤ 2 * ceilHalf n := by
  unfold ceilHalf
  omega

theorem two_mul_ceilHalf_le (n : Nat) : 2 * ceilHalf n ≤ n + 1 := by
  unfold ceilHalf
  omega

/-- Restrict a predicate on `Fin (m + 1)` to `Fin m` by inclusion `0 .. m-1`. -/
def initPred {m : Nat} (f : Fin (m + 1) → Bool) : Fin m → Bool :=
  fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- Count the number of indices `i : Fin n` with `f i = true`. -/
def countFin : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | m + 1, f =>
    countFin m (initPred f) + (if f ⟨m, Nat.lt_succ_self m⟩ then 1 else 0)

theorem countFin_congr {n : Nat} {f g : Fin n → Bool} (h : ∀ i, f i = g i) :
    countFin n f = countFin n g := by
  have hfg : f = g := funext h
  subst hfg
  rfl

theorem countFin_le (n : Nat) (f : Fin n → Bool) : countFin n f ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold countFin
    have hm := ih (initPred f)
    cases f ⟨m, Nat.lt_succ_self m⟩ <;> simp at * <;> omega

theorem countFin_true (n : Nat) : countFin n (fun _ => true) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold countFin initPred
    rw [ih]
    simp

theorem countFin_false (n : Nat) : countFin n (fun _ => false) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold countFin initPred
    rw [ih]
    simp

theorem countFin_mono {n : Nat} {f g : Fin n → Bool}
    (h : ∀ i, f i = true → g i = true) : countFin n f ≤ countFin n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold countFin
    have hm : countFin m (initPred f) ≤ countFin m (initPred g) :=
      ih (fun i hi => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ hi)
    have hlast := h ⟨m, Nat.lt_succ_self m⟩
    cases hf : f ⟨m, Nat.lt_succ_self m⟩ <;> cases hg : g ⟨m, Nat.lt_succ_self m⟩
    · simp; exact hm
    · simp; omega
    · exfalso; have := hlast hf; rw [hg] at this; contradiction
    · simp; omega

theorem countFin_not (n : Nat) (f : Fin n → Bool) :
    countFin n f + countFin n (fun i => !(f i)) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold countFin initPred
    have hm := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    dsimp
    cases f ⟨m, Nat.lt_succ_self m⟩
    · have ht : (!false) = true := rfl
      rw [ht]
      simp
      omega
    · have hf : (!true) = false := rfl
      rw [hf]
      simp
      omega

theorem countFin_sum_le_of_disjoint {n : Nat} (f g : Fin n → Bool)
    (h : ∀ i, ¬(f i = true ∧ g i = true)) :
    countFin n f + countFin n g ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold countFin
    have hm := ih (initPred f) (initPred g) (fun i hi => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ hi)
    have hlast := h ⟨m, Nat.lt_succ_self m⟩
    cases hf : f ⟨m, Nat.lt_succ_self m⟩ <;> cases hg : g ⟨m, Nat.lt_succ_self m⟩
    · simp; omega
    · simp; omega
    · simp; omega
    · exfalso; exact hlast ⟨hf, hg⟩

theorem countFin_sum_eq_succ_of_single {n : Nat} (f g : Fin n → Bool) (v : Fin n)
    (hv : f v = true ∧ g v = true)
    (hother : ∀ i : Fin n, i ≠ v → g i = !(f i)) :
    countFin n f + countFin n g = n + 1 := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ m ih =>
    unfold countFin
    by_cases hvm : v.val = m
    · have hv_eq : v = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hvm
      rw [← hv_eq]
      rw [hv.1, hv.2]
      have hcomp : initPred g = (fun i => !(initPred f i)) := by
        funext i
        apply hother ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        intro heq
        have : i.val = v.val := congrArg Fin.val heq
        omega
      rw [hcomp]
      have hnot := countFin_not m (initPred f)
      simp
      omega
    · have hlt : v.val < m := by omega
      let v' : Fin m := ⟨v.val, hlt⟩
      have hv' : initPred f v' = true ∧ initPred g v' = true := by
        have hveq : (⟨v'.val, Nat.lt_succ_of_lt v'.isLt⟩ : Fin (m + 1)) = v := Fin.ext rfl
        unfold initPred
        rw [hveq]
        exact hv
      have hother' : ∀ i : Fin m, i ≠ v' → initPred g i = !(initPred f i) := by
        intro i hne
        apply hother ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        intro heq
        apply hne
        have hval : i.val = v.val := congrArg Fin.val heq
        exact Fin.ext hval
      have hm := ih (initPred f) (initPred g) v' hv' hother'
      have hlast_ne : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ v := by
        intro heq
        apply hvm
        exact (congrArg Fin.val heq).symm
      have hlast := hother ⟨m, Nat.lt_succ_self m⟩ hlast_ne
      rw [hlast]
      cases f ⟨m, Nat.lt_succ_self m⟩ <;> simp <;> omega

theorem countFin_le_one_of_at_most_one {n : Nat} (f : Fin n → Bool) (v : Fin n)
    (hother : ∀ i : Fin n, i ≠ v → f i = false) :
    countFin n f ≤ 1 := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ m ih =>
    unfold countFin
    by_cases hvm : v.val = m
    · have hzero : initPred f = (fun _ => false) := by
        funext i
        apply hother ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        intro heq
        have : i.val = v.val := congrArg Fin.val heq
        omega
      rw [hzero, countFin_false]
      cases f ⟨m, Nat.lt_succ_self m⟩ <;> simp
    · have hlt : v.val < m := by omega
      let v' : Fin m := ⟨v.val, hlt⟩
      have hm : countFin m (initPred f) ≤ 1 := by
        apply ih (initPred f) v'
        intro i hne
        apply hother ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        intro heq
        apply hne
        have hval : i.val = v.val := congrArg Fin.val heq
        exact Fin.ext hval
      have hlast : f ⟨m, Nat.lt_succ_self m⟩ = false := by
        apply hother ⟨m, Nat.lt_succ_self m⟩
        intro heq
        apply hvm
        exact (congrArg Fin.val heq).symm
      rw [hlast]
      simp
      exact hm

theorem countFin_pos_iff {n : Nat} {f : Fin n → Bool} :
    0 < countFin n f ↔ ∃ v : Fin n, f v = true := by
  induction n with
  | zero =>
    unfold countFin
    constructor
    · intro h; omega
    · rintro ⟨v, _⟩; exact Fin.elim0 v
  | succ m ih =>
    unfold countFin
    constructor
    · intro hpos
      cases hlast : f ⟨m, Nat.lt_succ_self m⟩
      · rw [hlast] at hpos
        simp at hpos
        obtain ⟨v', hv'⟩ := ih.mp hpos
        exact ⟨⟨v'.val, Nat.lt_succ_of_lt v'.isLt⟩, hv'⟩
      · exact ⟨⟨m, Nat.lt_succ_self m⟩, hlast⟩
    · rintro ⟨v, hv⟩
      by_cases hvm : v.val = m
      · have hveq : v = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hvm
        rw [← hveq, hv]
        simp
      · have hlt : v.val < m := by omega
        have hv' : initPred f ⟨v.val, hlt⟩ = true := hv
        have hpos' : 0 < countFin m (initPred f) := ih.mpr ⟨⟨v.val, hlt⟩, hv'⟩
        cases f ⟨m, Nat.lt_succ_self m⟩ <;> simp <;> omega

theorem countFin_lt (n a : Nat) (ha : a ≤ n) :
    countFin n (fun i => decide (i.val < a)) = a := by
  induction n with
  | zero =>
    have : a = 0 := by omega
    subst this
    rfl
  | succ m ih =>
    by_cases ham : a ≤ m
    · unfold countFin initPred
      dsimp
      have hlast : decide (m < a) = false := decide_eq_false (by omega)
      rw [hlast, ih ham]
      simp
    · have haeq : a = m + 1 := by omega
      subst haeq
      have hall : (fun i : Fin (m + 1) => decide (i.val < m + 1)) = (fun _ => true) := by
        funext i
        exact decide_eq_true i.isLt
      rw [hall, countFin_true]

/-! ## 2. Finite Simple Undirected Graphs, Connectivity, Trees, and Odd Bipartitions -/

/-- A finite simple undirected graph on `n` vertices `Fin n`. -/
structure SimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

/-- Finite walks in `G`. -/
inductive Walk {n : Nat} (G : SimpleGraph n) : Fin n → Fin n → Prop where
  | nil (u : Fin n) : Walk G u u
  | cons {u v w : Fin n} : G.adj u v = true → Walk G v w → Walk G u w

theorem Walk.trans {n : Nat} {G : SimpleGraph n} {u v w : Fin n}
    (h₁ : Walk G u v) (h₂ : Walk G v w) : Walk G u w := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hadj _ ih => exact Walk.cons hadj (ih h₂)

theorem Walk.single {n : Nat} {G : SimpleGraph n} {u v : Fin n}
    (h : G.adj u v = true) : Walk G u v :=
  Walk.cons h (Walk.nil v)

/-- Standard graph connectivity: non-empty vertex set with walks between all pairs. -/
def SimpleGraph.IsConnected {n : Nat} (G : SimpleGraph n) : Prop :=
  n ≥ 1 ∧ ∀ u v : Fin n, Walk G u v

/-- Existence of at least one edge in `G`. -/
def SimpleGraph.HasEdge {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ u v : Fin n, G.adj u v = true

/-- Existence of a simple cycle of length `k ≥ 3` in `G`. -/
def SimpleGraph.HasCycle {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ (k : Nat) (hk : k ≥ 3) (f : Fin k → Fin n),
    (∀ i j : Fin k, f i = f j → i = j) ∧
    (∀ i : Fin k, G.adj (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) = true)

/-- A tree is a connected acyclic simple graph. -/
def SimpleGraph.IsTree {n : Nat} (G : SimpleGraph n) : Prop :=
  G.IsConnected ∧ ¬ G.HasCycle

/-- A bipartition of `G` encoded by `χ : Fin n → Bool` (`A = χ⁻¹(true)`, `B = χ⁻¹(false)`). -/
def SimpleGraph.IsBipartition {n : Nat} (G : SimpleGraph n) (χ : Fin n → Bool) : Prop :=
  ∀ u v : Fin n, G.adj u v = true → χ u ≠ χ v

/-- `G` is bipartite if it possesses at least one bipartition. -/
def SimpleGraph.IsBipartite {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ χ : Fin n → Bool, G.IsBipartition χ

/-- Sizes of the two parts `A = {v | χ v = true}` and `B = {v | χ v = false}`. -/
def partTrueSize {n : Nat} (χ : Fin n → Bool) : Nat := countFin n χ
def partFalseSize {n : Nat} (χ : Fin n → Bool) : Nat := countFin n (fun i => !(χ i))

theorem partSizes_sum {n : Nat} (χ : Fin n → Bool) :
    partTrueSize χ + partFalseSize χ = n :=
  countFin_not n χ

def isOddNat (k : Nat) : Prop := k % 2 = 1

/-- All four interpretations of "has an odd bipartition" (`奇部二分`). -/
inductive OddBipMode where
  | existsSomeOdd
  | existsBothOdd
  | everySomeOdd
  | everyBothOdd
  deriving DecidableEq, Repr

def HasOddBipartition {n : Nat} (mode : OddBipMode) (G : SimpleGraph n) : Prop :=
  match mode with
  | .existsSomeOdd =>
    ∃ χ, G.IsBipartition χ ∧ (isOddNat (partTrueSize χ) ∨ isOddNat (partFalseSize χ))
  | .existsBothOdd =>
    ∃ χ, G.IsBipartition χ ∧ (isOddNat (partTrueSize χ) ∧ isOddNat (partFalseSize χ))
  | .everySomeOdd =>
    G.IsBipartite ∧ ∀ χ, G.IsBipartition χ → (isOddNat (partTrueSize χ) ∨ isOddNat (partFalseSize χ))
  | .everyBothOdd =>
    G.IsBipartite ∧ ∀ χ, G.IsBipartition χ → (isOddNat (partTrueSize χ) ∧ isOddNat (partFalseSize χ))

theorem hasOddBipartition_imp_bipartite {n : Nat} (mode : OddBipMode) (G : SimpleGraph n) :
    HasOddBipartition mode G → G.IsBipartite := by
  intro h
  cases mode with
  | existsSomeOdd => obtain ⟨χ, hχ, _⟩ := h; exact ⟨χ, hχ⟩
  | existsBothOdd => obtain ⟨χ, hχ, _⟩ := h; exact ⟨χ, hχ⟩
  | everySomeOdd => exact h.1
  | everyBothOdd => exact h.1

private theorem bool_eq_step {b₁ c₁ b₂ c₂ : Bool}
    (h₁ : b₁ ≠ c₁) (h₂ : b₂ ≠ c₂) : (b₁ == b₂) = (c₁ == c₂) := by
  cases b₁ <;> cases c₁ <;> cases b₂ <;> cases c₂ <;> simp at *

private theorem bipartition_walk_const {n : Nat} {G : SimpleGraph n} {χ₁ χ₂ : Fin n → Bool}
    (h₁ : G.IsBipartition χ₁) (h₂ : G.IsBipartition χ₂) {u v : Fin n} (hw : Walk G u v) :
    (χ₁ u == χ₂ u) = (χ₁ v == χ₂ v) := by
  induction hw with
  | nil _ => rfl
  | cons hadj _ ih =>
    rw [← ih]
    exact bool_eq_step (h₁ _ _ hadj) (h₂ _ _ hadj)

/-- On any connected graph, a bipartition is unique up to swapping the two parts. -/
theorem connected_bipartition_unique {n : Nat} {G : SimpleGraph n}
    (hconn : G.IsConnected) {χ₁ χ₂ : Fin n → Bool}
    (h₁ : G.IsBipartition χ₁) (h₂ : G.IsBipartition χ₂) :
    (χ₂ = χ₁) ∨ (χ₂ = fun i => !(χ₁ i)) := by
  obtain ⟨hn, hwalk⟩ := hconn
  let u₀ : Fin n := ⟨0, hn⟩
  cases heq : (χ₁ u₀ == χ₂ u₀)
  · right
    funext v
    have hv := bipartition_walk_const h₁ h₂ (hwalk u₀ v)
    rw [heq] at hv
    cases h1v : χ₁ v <;> cases h2v : χ₂ v <;> rw [h1v, h2v] at hv <;> simp at hv ⊢
  · left
    funext v
    have hv := bipartition_walk_const h₁ h₂ (hwalk u₀ v)
    rw [heq] at hv
    cases h1v : χ₁ v <;> cases h2v : χ₂ v <;> rw [h1v, h2v] at hv <;> simp at hv ⊢

/-- If a connected graph has a bipartition with both part sizes even, it has no odd
    bipartition under any of the four modes. -/
theorem not_hasOddBipartition_of_connected_even_parts {n : Nat} {G : SimpleGraph n}
    (hconn : G.IsConnected) {χ₀ : Fin n → Bool} (hχ₀ : G.IsBipartition χ₀)
    (hevenT : partTrueSize χ₀ % 2 = 0) (hevenF : partFalseSize χ₀ % 2 = 0)
    (mode : OddBipMode) : ¬ HasOddBipartition mode G := by
  have hno : ∀ χ, G.IsBipartition χ → ¬isOddNat (partTrueSize χ) ∧ ¬isOddNat (partFalseSize χ) := by
    intro χ hχ
    unfold isOddNat
    rcases connected_bipartition_unique hconn hχ₀ hχ with rfl | rfl
    · omega
    · have hT : partTrueSize (fun i => !(χ₀ i)) = partFalseSize χ₀ := rfl
      have hF : partFalseSize (fun i => !(χ₀ i)) = partTrueSize χ₀ := by
        unfold partFalseSize partTrueSize
        apply countFin_congr
        intro i
        dsimp
        cases χ₀ i <;> rfl
      rw [hT, hF]
      omega
  intro hodd
  cases mode with
  | existsSomeOdd =>
    obtain ⟨χ, hχ, hp⟩ := hodd
    have hboth := hno χ hχ
    rcases hp with h1 | h2
    · exact hboth.1 h1
    · exact hboth.2 h2
  | existsBothOdd =>
    obtain ⟨χ, hχ, hp⟩ := hodd
    exact (hno χ hχ).1 hp.1
  | everySomeOdd =>
    have hp := hodd.2 χ₀ hχ₀
    have hboth := hno χ₀ hχ₀
    rcases hp with h1 | h2
    · exact hboth.1 h1
    · exact hboth.2 h2
  | everyBothOdd =>
    exact (hno χ₀ hχ₀).1 (hodd.2 χ₀ hχ₀).1

/-! ## 3. The Lamp Lighting Game (Lit-Only σ-Game) and Extremal `minLit` -/

abbrev Config (n : Nat) := Fin n → Bool

def litCount {n : Nat} (c : Config n) : Nat := countFin n c

def allLit (n : Nat) : Config n := fun _ => true
def allUnlit (n : Nat) : Config n := fun _ => false

theorem litCount_le {n : Nat} (c : Config n) : litCount c ≤ n :=
  countFin_le n c

theorem litCount_allLit (n : Nat) : litCount (allLit n) = n :=
  countFin_true n

theorem litCount_allUnlit (n : Nat) : litCount (allUnlit n) = 0 :=
  countFin_false n

/-- Move rules in the lit-only σ-game literature:
    - `openNbr` (`σ⁻`): pressing a lit vertex `v` toggles `N(v)` while `v` remains lit.
    - `closedNbr` (`σ⁺`): pressing a lit vertex `v` toggles `N[v] = {v} ∪ N(v)`. -/
inductive MoveRule where
  | openNbr
  | closedNbr
  deriving DecidableEq, Repr

def toggleAt {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (c : Config n) (v : Fin n) : Config n :=
  fun u =>
    match rule with
    | .openNbr   => if G.adj v u then !(c u) else c u
    | .closedNbr => if decide (u = v) || G.adj v u then !(c u) else c u

theorem toggleAt_openNbr_self {n : Nat} (G : SimpleGraph n) (c : Config n) (v : Fin n) :
    toggleAt .openNbr G c v v = c v := by
  unfold toggleAt
  rw [G.loopless v]
  rfl

/-- A single legal lit-only move: vertex `v` must currently be lit (`c v = true`). -/
inductive Step {n : Nat} (rule : MoveRule) (G : SimpleGraph n) : Config n → Config n → Prop where
  | press (c : Config n) (v : Fin n) (hlit : c v = true) :
      Step rule G c (toggleAt rule G c v)

/-- Unbounded finite-sequence reachability (reflexive-transitive closure of `Step`). -/
inductive Reach {n : Nat} (rule : MoveRule) (G : SimpleGraph n) : Config n → Config n → Prop where
  | refl (c : Config n) : Reach rule G c c
  | step {c₁ c₂ c₃ : Config n} : Step rule G c₁ c₂ → Reach rule G c₂ c₃ → Reach rule G c₁ c₃

theorem Reach.single {n : Nat} {rule : MoveRule} {G : SimpleGraph n} {c₁ c₂ : Config n}
    (h : Step rule G c₁ c₂) : Reach rule G c₁ c₂ :=
  Reach.step h (Reach.refl c₂)

section ExtremalDefinitions
open Classical

/-- Smallest `k ≤ bound` satisfying `P k` (defaults to `bound` if none). -/
noncomputable def leastUpTo (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    let r := leastUpTo P m
    if P r then r else m + 1

theorem leastUpTo_le (P : Nat → Prop) (b : Nat) : leastUpTo P b ≤ b := by
  induction b with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold leastUpTo
    by_cases h : P (leastUpTo P m) <;> simp [h] <;> omega

theorem leastUpTo_spec (P : Nat → Prop) (b k : Nat) (hk : k ≤ b) (hP : P k) :
    P (leastUpTo P b) ∧ leastUpTo P b ≤ k := by
  induction b with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨hP, Nat.le_refl 0⟩
  | succ m ih =>
    unfold leastUpTo
    by_cases hkm : k ≤ m
    · obtain ⟨hPr, hrle⟩ := ih hkm
      simp [hPr]
      exact hrle
    · have hkeq : k = m + 1 := by omega
      subst hkeq
      by_cases hPr : P (leastUpTo P m)
      · simp [hPr]
        have := leastUpTo_le P m
        omega
      · simp [hPr]
        exact hP

/-- Largest `k ≤ bound` satisfying `P k` (defaults to `0` if none). -/
noncomputable def greatestUpTo (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | m + 1 => if P (m + 1) then m + 1 else greatestUpTo P m

theorem greatestUpTo_le (P : Nat → Prop) (b : Nat) : greatestUpTo P b ≤ b := by
  induction b with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold greatestUpTo
    by_cases h : P (m + 1) <;> simp [h] <;> omega

theorem greatestUpTo_spec (P : Nat → Prop) (b k : Nat) (hk : k ≤ b) (hP : P k) :
    P (greatestUpTo P b) ∧ k ≤ greatestUpTo P b := by
  induction b with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨hP, Nat.le_refl 0⟩
  | succ m ih =>
    unfold greatestUpTo
    by_cases hm : P (m + 1)
    · simp [hm]
      exact hk
    · simp [hm]
      have hkm : k ≤ m := by
        by_cases hkeq : k = m + 1
        · subst hkeq; exact False.elim (hm hP)
        · omega
      exact ih hkm

/-- Minimum lit count reachable from a specific initial configuration `c₀`. -/
noncomputable def minLitFrom {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (c₀ : Config n) : Nat :=
  leastUpTo (fun m => ∃ c : Config n, Reach rule G c₀ c ∧ litCount c = m) n

theorem minLitFrom_attained {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (c₀ : Config n) :
    ∃ c : Config n, Reach rule G c₀ c ∧ litCount c = minLitFrom rule G c₀ :=
  (leastUpTo_spec (fun m => ∃ c : Config n, Reach rule G c₀ c ∧ litCount c = m)
    n (litCount c₀) (litCount_le c₀) ⟨c₀, Reach.refl c₀, rfl⟩).1

theorem minLitFrom_le_of_reach {n : Nat} {rule : MoveRule} {G : SimpleGraph n}
    {c₀ c : Config n} (hr : Reach rule G c₀ c) :
    minLitFrom rule G c₀ ≤ litCount c :=
  (leastUpTo_spec (fun m => ∃ c' : Config n, Reach rule G c₀ c' ∧ litCount c' = m)
    n (litCount c) (litCount_le c) ⟨c, hr, rfl⟩).2

theorem minLitFrom_le_n {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (c₀ : Config n) :
    minLitFrom rule G c₀ ≤ n :=
  Nat.le_trans (minLitFrom_le_of_reach (Reach.refl c₀)) (litCount_le c₀)

theorem minLitFrom_le_iff {n : Nat} (rule : MoveRule) (G : SimpleGraph n)
    (c₀ : Config n) (k : Nat) :
    minLitFrom rule G c₀ ≤ k ↔ ∃ c : Config n, Reach rule G c₀ c ∧ litCount c ≤ k := by
  constructor
  · intro hle
    obtain ⟨c, hr, hlc⟩ := minLitFrom_attained rule G c₀
    exact ⟨c, hr, by omega⟩
  · rintro ⟨c, hr, hlc⟩
    have := minLitFrom_le_of_reach hr
    omega

/-- Standard Convention 1: Minimum lit count starting from the all-lit configuration `V`. -/
noncomputable def minLitAllLit {n : Nat} (rule : MoveRule) (G : SimpleGraph n) : Nat :=
  minLitFrom rule G (allLit n)

/-- Standard Convention 2: Worst-case minimum lit count over ALL initial `S₀ ⊆ V`. -/
noncomputable def minLitWorst {n : Nat} (rule : MoveRule) (G : SimpleGraph n) : Nat :=
  greatestUpTo (fun m => ∃ c₀ : Config n, minLitFrom rule G c₀ = m) n

/-- Standard Convention 3: Worst-case minimum lit count over all NON-EMPTY `S₀ ⊆ V`. -/
noncomputable def minLitWorstNonempty {n : Nat} (rule : MoveRule) (G : SimpleGraph n) : Nat :=
  greatestUpTo (fun m => ∃ c₀ : Config n, 0 < litCount c₀ ∧ minLitFrom rule G c₀ = m) n

theorem minLitWorst_attained {n : Nat} (rule : MoveRule) (G : SimpleGraph n) :
    ∃ c₀ : Config n, minLitFrom rule G c₀ = minLitWorst rule G :=
  (greatestUpTo_spec (fun m => ∃ c₀ : Config n, minLitFrom rule G c₀ = m)
    n (minLitFrom rule G (allLit n)) (minLitFrom_le_n rule G (allLit n)) ⟨allLit n, rfl⟩).1

theorem le_minLitWorst {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (c₀ : Config n) :
    minLitFrom rule G c₀ ≤ minLitWorst rule G :=
  (greatestUpTo_spec (fun m => ∃ c₀' : Config n, minLitFrom rule G c₀' = m)
    n (minLitFrom rule G c₀) (minLitFrom_le_n rule G c₀) ⟨c₀, rfl⟩).2

theorem minLitWorst_le_iff {n : Nat} (rule : MoveRule) (G : SimpleGraph n) (k : Nat) :
    minLitWorst rule G ≤ k ↔
      ∀ c₀ : Config n, ∃ c : Config n, Reach rule G c₀ c ∧ litCount c ≤ k := by
  constructor
  · intro hle c₀
    have hc₀ := Nat.le_trans (le_minLitWorst rule G c₀) hle
    exact (minLitFrom_le_iff rule G c₀ k).mp hc₀
  · intro hall
    obtain ⟨c₀, hc₀⟩ := minLitWorst_attained rule G
    rw [← hc₀]
    exact (minLitFrom_le_iff rule G c₀ k).mpr (hall c₀)

theorem minLitWorstNonempty_attained {n : Nat} (hn : n ≥ 1)
    (rule : MoveRule) (G : SimpleGraph n) :
    ∃ c₀ : Config n, 0 < litCount c₀ ∧ minLitFrom rule G c₀ = minLitWorstNonempty rule G := by
  have hpos : 0 < litCount (allLit n) := by rw [litCount_allLit]; omega
  exact (greatestUpTo_spec (fun m => ∃ c₀ : Config n, 0 < litCount c₀ ∧ minLitFrom rule G c₀ = m)
    n (minLitFrom rule G (allLit n)) (minLitFrom_le_n rule G (allLit n)) ⟨allLit n, hpos, rfl⟩).1

theorem le_minLitWorstNonempty {n : Nat} (rule : MoveRule) (G : SimpleGraph n)
    {c₀ : Config n} (hpos : 0 < litCount c₀) :
    minLitFrom rule G c₀ ≤ minLitWorstNonempty rule G :=
  (greatestUpTo_spec (fun m => ∃ c₀' : Config n, 0 < litCount c₀' ∧ minLitFrom rule G c₀' = m)
    n (minLitFrom rule G c₀) (minLitFrom_le_n rule G c₀) ⟨c₀, hpos, rfl⟩).2

theorem minLitWorstNonempty_le_iff {n : Nat} (hn : n ≥ 1)
    (rule : MoveRule) (G : SimpleGraph n) (k : Nat) :
    minLitWorstNonempty rule G ≤ k ↔
      ∀ c₀ : Config n, 0 < litCount c₀ → ∃ c : Config n, Reach rule G c₀ c ∧ litCount c ≤ k := by
  constructor
  · intro hle c₀ hpos
    have hc₀ := Nat.le_trans (le_minLitWorstNonempty rule G hpos) hle
    exact (minLitFrom_le_iff rule G c₀ k).mp hc₀
  · intro hall
    obtain ⟨c₀, hpos, hc₀⟩ := minLitWorstNonempty_attained hn rule G
    rw [← hc₀]
    exact (minLitFrom_le_iff rule G c₀ k).mpr (hall c₀ hpos)

/-- Three standard `min-lit` objective conventions. -/
inductive MinLitMode where
  | fromAllLit
  | worstAll
  | worstNonempty
  deriving DecidableEq, Repr

noncomputable def minLit {n : Nat} (rule : MoveRule) (mlMode : MinLitMode) (G : SimpleGraph n) : Nat :=
  match mlMode with
  | .fromAllLit    => minLitAllLit rule G
  | .worstAll      => minLitWorst rule G
  | .worstNonempty => minLitWorstNonempty rule G

/-- Sufficient condition bounding `minLit` simultaneously across all 3 objective modes. -/
theorem minLit_le_of_universal {n : Nat} (hn : n ≥ 1) (rule : MoveRule)
    (mlMode : MinLitMode) (G : SimpleGraph n) (k : Nat)
    (h : ∀ c₀ : Config n, ∃ c : Config n, Reach rule G c₀ c ∧ litCount c ≤ k) :
    minLit rule mlMode G ≤ k := by
  cases mlMode with
  | fromAllLit => exact (minLitFrom_le_iff rule G (allLit n) k).mpr (h (allLit n))
  | worstAll => exact (minLitWorst_le_iff rule G k).mpr h
  | worstNonempty => exact (minLitWorstNonempty_le_iff hn rule G k).mpr (fun c₀ _ => h c₀)

/-- Lower bound from `allLit` transfers to all 3 objective modes when `n ≥ 1`. -/
theorem minLit_gt_of_allLit_gt {n : Nat} (hn : n ≥ 1) (rule : MoveRule)
    (mlMode : MinLitMode) (G : SimpleGraph n) (k : Nat)
    (h : ∀ c : Config n, Reach rule G (allLit n) c → k < litCount c) :
    k < minLit rule mlMode G := by
  have hall : k < minLitFrom rule G (allLit n) := by
    obtain ⟨c, hr, hlc⟩ := minLitFrom_attained rule G (allLit n)
    have := h c hr
    omega
  unfold minLit minLitAllLit
  cases mlMode with
  | fromAllLit => exact hall
  | worstAll =>
    dsimp
    have := le_minLitWorst rule G (allLit n)
    omega
  | worstNonempty =>
    dsimp
    have hpos : 0 < litCount (allLit n) := by rw [litCount_allLit]; omega
    have := le_minLitWorstNonempty rule G hpos
    omega

end ExtremalDefinitions

/-! ## 4. Formal Statements of Conjecture 00000001242 (General and Restricted Scopes) -/

/-- Official Conjecture 00000001242 parameterized over all `(rule, mlMode, bipMode)`. -/
def Conjecture00000001242 (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) : Prop :=
  ∀ (n : Nat), n ≥ 1 → ∀ (G : SimpleGraph n),
    (minLit rule mlMode G ≤ ceilHalf n ↔ HasOddBipartition bipMode G)

/-- Restricted version assuming `G` is connected. -/
def ConjectureConnected (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) : Prop :=
  ∀ (n : Nat), n ≥ 1 → ∀ (G : SimpleGraph n), G.IsConnected →
    (minLit rule mlMode G ≤ ceilHalf n ↔ HasOddBipartition bipMode G)

/-- Restricted version assuming `G` is connected AND bipartite. -/
def ConjectureConnectedBipartite (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) : Prop :=
  ∀ (n : Nat), n ≥ 1 → ∀ (G : SimpleGraph n), G.IsConnected → G.IsBipartite →
    (minLit rule mlMode G ≤ ceilHalf n ↔ HasOddBipartition bipMode G)

/-- Restricted version assuming `G` is a tree. -/
def ConjectureTrees (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) : Prop :=
  ∀ (n : Nat), n ≥ 1 → ∀ (G : SimpleGraph n), G.IsTree →
    (minLit rule mlMode G ≤ ceilHalf n ↔ HasOddBipartition bipMode G)

/-! ## 5. Family 1: Complete Graphs `K_n` (`n ≥ 3` Non-Bipartite; `n = 2` Positive Witness) -/

/-- The complete graph `K_n` on `n` vertices. -/
def completeGraph (n : Nat) : SimpleGraph n where
  adj := fun u v => decide (u ≠ v)
  symm := by
    intro u v
    by_cases h : u = v
    · subst h; rfl
    · have h' : v ≠ u := Ne.symm h
      simp [h, h']
  loopless := by
    intro u
    simp

theorem completeGraph_isConnected {n : Nat} (hn : n ≥ 1) : (completeGraph n).IsConnected := by
  refine ⟨hn, fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv; exact Walk.nil u
  · exact Walk.single (decide_eq_true huv)

/-- For every `n ≥ 3`, `K_n` contains a triangle `{0, 1, 2}` and is not bipartite. -/
theorem completeGraph_not_bipartite {n : Nat} (hn : n ≥ 3) : ¬ (completeGraph n).IsBipartite := by
  rintro ⟨χ, hχ⟩
  let v₀ : Fin n := ⟨0, by omega⟩
  let v₁ : Fin n := ⟨1, by omega⟩
  let v₂ : Fin n := ⟨2, by omega⟩
  have hadj01 : (completeGraph n).adj v₀ v₁ = true := by
    dsimp [completeGraph]
    exact decide_eq_true (fun h => by have := congrArg Fin.val h; simp [v₀, v₁] at this)
  have hadj12 : (completeGraph n).adj v₁ v₂ = true := by
    dsimp [completeGraph]
    exact decide_eq_true (fun h => by have := congrArg Fin.val h; simp [v₁, v₂] at this)
  have hadj02 : (completeGraph n).adj v₀ v₂ = true := by
    dsimp [completeGraph]
    exact decide_eq_true (fun h => by have := congrArg Fin.val h; simp [v₀, v₂] at this)
  have h01 : χ v₀ ≠ χ v₁ := hχ v₀ v₁ hadj01
  have h12 : χ v₁ ≠ χ v₂ := hχ v₁ v₂ hadj12
  have h02 : χ v₀ ≠ χ v₂ := hχ v₀ v₂ hadj02
  cases h0 : χ v₀ <;> cases h1 : χ v₁ <;> cases h2 : χ v₂ <;> simp_all

theorem completeGraph_not_hasOddBipartition {n : Nat} (hn : n ≥ 3) (mode : OddBipMode) :
    ¬ HasOddBipartition mode (completeGraph n) :=
  fun h => completeGraph_not_bipartite hn (hasOddBipartition_imp_bipartite mode (completeGraph n) h)

/-- Universal 1-move bound on `K_n`: from ANY configuration `c₀`, at most one move
    reaches `litCount ≤ ceilHalf n` under BOTH `openNbr` (`σ⁻`) and `closedNbr` (`σ⁺`). -/
theorem completeGraph_reach_le_ceilHalf {n : Nat} (rule : MoveRule) (c₀ : Config n) :
    ∃ c : Config n, Reach rule (completeGraph n) c₀ c ∧ litCount c ≤ ceilHalf n := by
  by_cases hle : litCount c₀ ≤ ceilHalf n
  · exact ⟨c₀, Reach.refl c₀, hle⟩
  · have hpos : 0 < litCount c₀ := by omega
    obtain ⟨v, hv⟩ := countFin_pos_iff.mp hpos
    let c₁ := toggleAt rule (completeGraph n) c₀ v
    have hstep : Reach rule (completeGraph n) c₀ c₁ := Reach.single (Step.press c₀ v hv)
    refine ⟨c₁, hstep, ?_⟩
    cases rule with
    | openNbr =>
      have hsum : litCount c₀ + litCount c₁ = n + 1 := by
        apply countFin_sum_eq_succ_of_single c₀ c₁ v
        · refine ⟨hv, ?_⟩
          dsimp [c₁]
          rw [toggleAt_openNbr_self]
          exact hv
        · intro i hne
          dsimp [c₁, toggleAt, completeGraph]
          have hvi : v ≠ i := Ne.symm hne
          simp [hvi]
      have hceil := le_two_mul_ceilHalf n
      omega
    | closedNbr =>
      have hc₁ : c₁ = (fun i => !(c₀ i)) := by
        funext i
        dsimp [c₁, toggleAt, completeGraph]
        by_cases hiv : i = v
        · subst hiv; simp
        · have hvi : v ≠ i := Ne.symm hiv
          simp [hiv, hvi]
      have hsum : litCount c₀ + litCount c₁ = n := by
        rw [hc₁]
        exact countFin_not n c₀
      have hceil := le_two_mul_ceilHalf n
      omega

/-- Theorem 1: For EVERY `n ≥ 1`, `minLit rule mlMode (completeGraph n) ≤ ceilHalf n`
    under all 6 game conventions. -/
theorem completeGraph_minLit_le_ceilHalf {n : Nat} (hn : n ≥ 1)
    (rule : MoveRule) (mlMode : MinLitMode) :
    minLit rule mlMode (completeGraph n) ≤ ceilHalf n :=
  minLit_le_of_universal hn rule mlMode (completeGraph n) (ceilHalf n)
    (completeGraph_reach_le_ceilHalf rule)

/-- Positive Non-Vacuity Witness (`K_2`, `n = 2`):
    `completeGraph 2` is connected, satisfies `HasOddBipartition` under ALL FOUR modes,
    and satisfies `minLit ≤ ceilHalf 2 = 1` under ALL SIX game conventions. -/
theorem k2_positive_witness (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    (completeGraph 2).IsConnected ∧
    HasOddBipartition bipMode (completeGraph 2) ∧
    minLit rule mlMode (completeGraph 2) ≤ ceilHalf 2 := by
  refine ⟨completeGraph_isConnected (by omega), ?_, completeGraph_minLit_le_ceilHalf (by omega) rule mlMode⟩
  let χ₀ : Fin 2 → Bool := fun i => decide (i.val < 1)
  have hχ₀ : (completeGraph 2).IsBipartition χ₀ := by
    intro u v hadj
    revert u v hadj
    decide
  have hT0 : partTrueSize χ₀ = 1 := by decide
  have hF0 : partFalseSize χ₀ = 1 := by decide
  have hboth0 : isOddNat (partTrueSize χ₀) ∧ isOddNat (partFalseSize χ₀) := by
    unfold isOddNat; omega
  have hallBoth : ∀ χ, (completeGraph 2).IsBipartition χ →
      isOddNat (partTrueSize χ) ∧ isOddNat (partFalseSize χ) := by
    intro χ hχ
    rcases connected_bipartition_unique (completeGraph_isConnected (by omega)) hχ₀ hχ with rfl | rfl
    · exact hboth0
    · have hT : partTrueSize (fun i => !(χ₀ i)) = partFalseSize χ₀ := rfl
      have hF : partFalseSize (fun i => !(χ₀ i)) = partTrueSize χ₀ := by
        unfold partFalseSize partTrueSize
        apply countFin_congr
        intro i
        dsimp
        cases χ₀ i <;> rfl
      unfold isOddNat at *
      omega
  cases bipMode with
  | existsSomeOdd => exact ⟨χ₀, hχ₀, Or.inl hboth0.1⟩
  | existsBothOdd => exact ⟨χ₀, hχ₀, hboth0⟩
  | everySomeOdd => exact ⟨⟨χ₀, hχ₀⟩, fun χ hχ => Or.inl (hallBoth χ hχ).1⟩
  | everyBothOdd => exact ⟨⟨χ₀, hχ₀⟩, hallBoth⟩

/-! ## 6. Family 2: Balanced Even Complete Bipartite Graphs `K_{2k, 2k}` (`k ≥ 1`, `n = 4k`) -/

/-- `K_{2k, 2k}` on `4k` vertices: left part `{0 .. 2k-1}`, right part `{2k .. 4k-1}`. -/
def evenCompleteBipartite (k : Nat) : SimpleGraph (4 * k) where
  adj := fun u v => decide (u.val < 2 * k) != decide (v.val < 2 * k)
  symm := by
    intro u v
    cases decide (u.val < 2 * k) <;> cases decide (v.val < 2 * k) <;> rfl
  loopless := by
    intro u
    cases decide (u.val < 2 * k) <;> rfl

theorem evenCompleteBipartite_isConnected {k : Nat} (hk : k ≥ 1) :
    (evenCompleteBipartite k).IsConnected := by
  refine ⟨by omega, fun u v => ?_⟩
  let u₀ : Fin (4 * k) := ⟨0, by omega⟩
  let v₀ : Fin (4 * k) := ⟨2 * k, by omega⟩
  have hadj0 : (evenCompleteBipartite k).adj u₀ v₀ = true := by
    dsimp [evenCompleteBipartite, u₀, v₀]
    have h1 : decide (0 < 2 * k) = true := decide_eq_true (by omega)
    have h2 : decide (2 * k < 2 * k) = false := decide_eq_false (by omega)
    rw [h1, h2]
    rfl
  have to_u₀ : ∀ x : Fin (4 * k), Walk (evenCompleteBipartite k) u₀ x := by
    intro x
    by_cases hx : x.val < 2 * k
    · have hxv : (evenCompleteBipartite k).adj v₀ x = true := by
        dsimp [evenCompleteBipartite, v₀]
        have h1 : decide (2 * k < 2 * k) = false := decide_eq_false (by omega)
        have h2 : decide (x.val < 2 * k) = true := decide_eq_true hx
        rw [h1, h2]
        rfl
      exact Walk.cons hadj0 (Walk.single hxv)
    · have hux : (evenCompleteBipartite k).adj u₀ x = true := by
        dsimp [evenCompleteBipartite, u₀]
        have h1 : decide (0 < 2 * k) = true := decide_eq_true (by omega)
        have h2 : decide (x.val < 2 * k) = false := decide_eq_false hx
        rw [h1, h2]
        rfl
      exact Walk.single hux
  have walk_symm : ∀ {a b : Fin (4 * k)},
      Walk (evenCompleteBipartite k) a b → Walk (evenCompleteBipartite k) b a := by
    intro a b hw
    induction hw with
    | nil _ => exact Walk.nil _
    | @cons x y _ hxy _ ih =>
      exact Walk.trans ih (Walk.single ((evenCompleteBipartite k).symm x y ▸ hxy))
  exact Walk.trans (walk_symm (to_u₀ u)) (to_u₀ v)

def k2kCanonicalBip (k : Nat) : Fin (4 * k) → Bool :=
  fun i => decide (i.val < 2 * k)

theorem evenCompleteBipartite_canonicalBip (k : Nat) :
    (evenCompleteBipartite k).IsBipartition (k2kCanonicalBip k) := by
  intro u v hadj
  dsimp [evenCompleteBipartite] at hadj
  unfold k2kCanonicalBip
  cases h1 : decide (u.val < 2 * k) <;> cases h2 : decide (v.val < 2 * k) <;>
    rw [h1, h2] at hadj <;> simp at hadj ⊢

theorem evenCompleteBipartite_isBipartite (k : Nat) :
    (evenCompleteBipartite k).IsBipartite :=
  ⟨k2kCanonicalBip k, evenCompleteBipartite_canonicalBip k⟩

theorem evenCompleteBipartite_not_hasOddBipartition {k : Nat} (hk : k ≥ 1) (mode : OddBipMode) :
    ¬ HasOddBipartition mode (evenCompleteBipartite k) := by
  have hT : partTrueSize (k2kCanonicalBip k) = 2 * k :=
    countFin_lt (4 * k) (2 * k) (by omega)
  have hF : partFalseSize (k2kCanonicalBip k) = 2 * k := by
    have := partSizes_sum (k2kCanonicalBip k)
    omega
  exact not_hasOddBipartition_of_connected_even_parts
    (evenCompleteBipartite_isConnected hk)
    (evenCompleteBipartite_canonicalBip k)
    (by omega) (by omega) mode

/-- Universal 1-move bound on `K_{2k, 2k}`: from ANY configuration `c₀`, at most one move
    reaches `litCount ≤ 2k = ceilHalf (4k)` under BOTH `openNbr` and `closedNbr`. -/
theorem evenCompleteBipartite_reach_le_ceilHalf (k : Nat) (rule : MoveRule) (c₀ : Config (4 * k)) :
    ∃ c : Config (4 * k), Reach rule (evenCompleteBipartite k) c₀ c ∧ litCount c ≤ ceilHalf (4 * k) := by
  have hceil : ceilHalf (4 * k) = 2 * k := by unfold ceilHalf; omega
  rw [hceil]
  by_cases hle : litCount c₀ ≤ 2 * k
  · exact ⟨c₀, Reach.refl c₀, hle⟩
  · -- Since `litCount c₀ > 2k` and each part has size `2k`, BOTH parts contain a lit vertex!
    have hexL : ∃ u : Fin (4 * k), k2kCanonicalBip k u = true ∧ c₀ u = true := by
      let fL : Fin (4 * k) → Bool := fun i => k2kCanonicalBip k i && c₀ i
      have hposL : 0 < countFin (4 * k) fL := by
        by_cases h0 : 0 < countFin (4 * k) fL
        · exact h0
        · exfalso
          have hallF : ∀ i : Fin (4 * k), c₀ i = true → (fun j => !(k2kCanonicalBip k j)) i = true := by
            intro i hci
            dsimp
            cases hbi : k2kCanonicalBip k i
            · rfl
            · exfalso
              have hwitness : fL i = true := by dsimp [fL]; simp [hbi, hci]
              have := (countFin_pos_iff (f := fL)).mpr ⟨i, hwitness⟩
              omega
          have hleR : countFin (4 * k) c₀ ≤ countFin (4 * k) (fun j => !(k2kCanonicalBip k j)) :=
            countFin_mono hallF
          have hT : countFin (4 * k) (k2kCanonicalBip k) = 2 * k :=
            countFin_lt (4 * k) (2 * k) (by omega)
          have hsum := countFin_not (4 * k) (k2kCanonicalBip k)
          unfold litCount at hle
          omega
      obtain ⟨u, hu⟩ := (countFin_pos_iff (f := fL)).mp hposL
      dsimp [fL] at hu
      cases hb : k2kCanonicalBip k u <;> cases hc : c₀ u <;> simp [hb, hc] at hu
      exact ⟨u, hb, hc⟩
    have hexR : ∃ w : Fin (4 * k), k2kCanonicalBip k w = false ∧ c₀ w = true := by
      let fR : Fin (4 * k) → Bool := fun i => !(k2kCanonicalBip k i) && c₀ i
      have hposR : 0 < countFin (4 * k) fR := by
        by_cases h0 : 0 < countFin (4 * k) fR
        · exact h0
        · exfalso
          have hallL : ∀ i : Fin (4 * k), c₀ i = true → k2kCanonicalBip k i = true := by
            intro i hci
            cases hbi : k2kCanonicalBip k i
            · exfalso
              have hwitness : fR i = true := by dsimp [fR]; simp [hbi, hci]
              have := (countFin_pos_iff (f := fR)).mpr ⟨i, hwitness⟩
              omega
            · rfl
          have hleL : countFin (4 * k) c₀ ≤ countFin (4 * k) (k2kCanonicalBip k) :=
            countFin_mono hallL
          have hT : countFin (4 * k) (k2kCanonicalBip k) = 2 * k :=
            countFin_lt (4 * k) (2 * k) (by omega)
          unfold litCount at hle
          omega
      obtain ⟨w, hw⟩ := (countFin_pos_iff (f := fR)).mp hposR
      dsimp [fR] at hw
      cases hb : k2kCanonicalBip k w <;> cases hc : c₀ w <;> simp [hb, hc] at hw
      exact ⟨w, hb, hc⟩
    obtain ⟨u, huL, huC⟩ := hexL
    obtain ⟨w, hwR, hwC⟩ := hexR
    let c₁ := toggleAt rule (evenCompleteBipartite k) c₀ u
    let c₂ := toggleAt rule (evenCompleteBipartite k) c₀ w
    have hsum_le : litCount c₁ + litCount c₂ ≤ 4 * k := by
      apply countFin_sum_le_of_disjoint c₁ c₂
      intro i ⟨h1, h2⟩
      unfold k2kCanonicalBip at huL hwR
      cases rule with
      | openNbr =>
        dsimp [c₁, c₂, toggleAt, evenCompleteBipartite] at h1 h2
        rw [huL] at h1
        rw [hwR] at h2
        cases hbi : decide (i.val < 2 * k) <;> cases hci : c₀ i <;>
          rw [hbi, hci] at h1 h2 <;> simp at h1 h2
      | closedNbr =>
        dsimp [c₁, c₂, toggleAt, evenCompleteBipartite] at h1 h2
        rw [huL] at h1
        rw [hwR] at h2
        by_cases hiu : i = u
        · subst hiu; simp [huC] at h1
        · by_cases hiw : i = w
          · subst hiw; simp [hwC] at h2
          · rw [decide_eq_false hiu] at h1
            rw [decide_eq_false hiw] at h2
            cases hbi : decide (i.val < 2 * k) <;> cases hci : c₀ i <;>
              rw [hbi, hci] at h1 h2 <;> simp at h1 h2
    by_cases hc1 : litCount c₁ ≤ 2 * k
    · exact ⟨c₁, Reach.single (Step.press c₀ u huC), hc1⟩
    · have hc2 : litCount c₂ ≤ 2 * k := by omega
      exact ⟨c₂, Reach.single (Step.press c₀ w hwC), hc2⟩

theorem evenCompleteBipartite_minLit_le_ceilHalf {k : Nat} (hk : k ≥ 1)
    (rule : MoveRule) (mlMode : MinLitMode) :
    minLit rule mlMode (evenCompleteBipartite k) ≤ ceilHalf (4 * k) :=
  minLit_le_of_universal (by omega) rule mlMode (evenCompleteBipartite k) (ceilHalf (4 * k))
    (evenCompleteBipartite_reach_le_ceilHalf k rule)

/-! ## 7. Tree Counterexample: The 4-Vertex Path `P_4` (`0 - 1 - 2 - 3`) -/

/-- The 4-vertex path `P_4` with edges `{0,1}`, `{1,2}`, `{2,3}`. -/
def p4Graph : SimpleGraph 4 where
  adj := fun u v => decide ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val))
  symm := by intro u v; revert u v; decide
  loopless := by intro u; revert u; decide

theorem p4Graph_isConnected : p4Graph.IsConnected := by
  refine ⟨by omega, fun u v => ?_⟩
  let v0 : Fin 4 := ⟨0, by omega⟩
  let v1 : Fin 4 := ⟨1, by omega⟩
  let v2 : Fin 4 := ⟨2, by omega⟩
  let v3 : Fin 4 := ⟨3, by omega⟩
  have e01 : p4Graph.adj v0 v1 = true := by decide
  have e10 : p4Graph.adj v1 v0 = true := by decide
  have e12 : p4Graph.adj v1 v2 = true := by decide
  have e21 : p4Graph.adj v2 v1 = true := by decide
  have e23 : p4Graph.adj v2 v3 = true := by decide
  have e32 : p4Graph.adj v3 v2 = true := by decide
  have from0 : ∀ x : Fin 4, Walk p4Graph v0 x := by
    intro ⟨x, hx⟩
    match x with
    | 0 => exact Walk.nil v0
    | 1 => exact Walk.single e01
    | 2 => exact Walk.cons e01 (Walk.single e12)
    | 3 => exact Walk.cons e01 (Walk.cons e12 (Walk.single e23))
    | n + 4 => omega
  have to0 : ∀ x : Fin 4, Walk p4Graph x v0 := by
    intro ⟨x, hx⟩
    match x with
    | 0 => exact Walk.nil v0
    | 1 => exact Walk.single e10
    | 2 => exact Walk.cons e21 (Walk.single e10)
    | 3 => exact Walk.cons e32 (Walk.cons e21 (Walk.single e10))
    | n + 4 => omega
  exact Walk.trans (to0 u) (from0 v)

theorem p4Graph_isTree : p4Graph.IsTree := by
  refine ⟨p4Graph_isConnected, ?_⟩
  rintro ⟨k, hk, f, hinj, hadj⟩
  have hmid : ∀ i : Fin k, (f i).val = 1 ∨ (f i).val = 2 := by
    intro i
    let inext : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩
    let iprev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
    have hprev_succ : (iprev.val + 1) % k = i.val := by
      dsimp [iprev]
      have hlt := i.isLt
      by_cases hi0 : i.val = 0
      · rw [hi0]
        have hsub : 0 + k - 1 = k - 1 := by omega
        have hmod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
        have hadd : k - 1 + 1 = k := by omega
        rw [hsub, hmod, hadd, Nat.mod_self]
      · have h1 : i.val + k - 1 = (i.val - 1) + k := by omega
        have hmod1 : (i.val - 1) % k = i.val - 1 := Nat.mod_eq_of_lt (by omega)
        have hadd : i.val - 1 + 1 = i.val := by omega
        have hmod2 : i.val % k = i.val := Nat.mod_eq_of_lt hlt
        rw [h1, Nat.add_mod_right, hmod1, hadd, hmod2]
    have hadj_next : p4Graph.adj (f i) (f inext) = true := hadj i
    have hadj_prev : p4Graph.adj (f i) (f iprev) = true := by
      have hp := hadj iprev
      have heq : (⟨(iprev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i := Fin.ext hprev_succ
      rw [heq] at hp
      rw [p4Graph.symm]
      exact hp
    have hne_idx : inext ≠ iprev := by
      intro heq
      have hval : (i.val + 1) % k = (i.val + k - 1) % k := congrArg Fin.val heq
      have hlt := i.isLt
      by_cases hi0 : i.val = 0
      · rw [hi0] at hval
        have hs1 : (0 + 1) % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hs2 : (0 + k - 1) % k = k - 1 := by
          have : 0 + k - 1 = k - 1 := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        omega
      · by_cases hi1 : i.val + 1 = k
        · have hk1 : (i.val + 1) % k = 0 := by rw [hi1, Nat.mod_self]
          have hk2 : (i.val + k - 1) % k = k - 2 := by
            have : i.val + k - 1 = (k - 2) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · have hs1 : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          have hs2 : (i.val + k - 1) % k = i.val - 1 := by
            have : i.val + k - 1 = (i.val - 1) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
    have hne_f : f inext ≠ f iprev := fun heq => hne_idx (hinj inext iprev heq)
    have hn1 : ((f i).val + 1 = (f inext).val) ∨ ((f inext).val + 1 = (f i).val) :=
      of_decide_eq_true hadj_next
    have hn2 : ((f i).val + 1 = (f iprev).val) ∨ ((f iprev).val + 1 = (f i).val) :=
      of_decide_eq_true hadj_prev
    have hfi := (f i).isLt
    have hfn := (f inext).isLt
    have hfp := (f iprev).isLt
    have hne_val : (f inext).val ≠ (f iprev).val := fun hv => hne_f (Fin.ext hv)
    omega
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  have hm0 := hmid i0
  have hm1 := hmid i1
  have hm2 := hmid i2
  have h01 : (f i0).val ≠ (f i1).val := fun h => by
    have := congrArg Fin.val (hinj i0 i1 (Fin.ext h)); simp [i0, i1] at this
  have h02 : (f i0).val ≠ (f i2).val := fun h => by
    have := congrArg Fin.val (hinj i0 i2 (Fin.ext h)); simp [i0, i2] at this
  have h12 : (f i1).val ≠ (f i2).val := fun h => by
    have := congrArg Fin.val (hinj i1 i2 (Fin.ext h)); simp [i1, i2] at this
  omega

def p4CanonicalBip : Fin 4 → Bool := fun i => decide (i.val % 2 = 0)

theorem p4Graph_canonicalBip : p4Graph.IsBipartition p4CanonicalBip := by
  intro u v hadj
  revert u v hadj
  decide

theorem p4Graph_not_hasOddBipartition (mode : OddBipMode) :
    ¬ HasOddBipartition mode p4Graph := by
  have hT : partTrueSize p4CanonicalBip = 2 := by decide
  have hF : partFalseSize p4CanonicalBip = 2 := by decide
  exact not_hasOddBipartition_of_connected_even_parts
    p4Graph_isConnected p4Graph_canonicalBip (by omega) (by omega) mode

/-- On `P_4`, every initial configuration reaches `litCount ≤ 2 = ceilHalf 4` in ≤ 1 move. -/
theorem p4Graph_reach_le_ceilHalf (rule : MoveRule) (c₀ : Config 4) :
    ∃ c : Config 4, Reach rule p4Graph c₀ c ∧ litCount c ≤ ceilHalf 4 := by
  let v0 : Fin 4 := ⟨0, by omega⟩
  let v1 : Fin 4 := ⟨1, by omega⟩
  let v2 : Fin 4 := ⟨2, by omega⟩
  let v3 : Fin 4 := ⟨3, by omega⟩
  have hcexp : c₀ = fun i : Fin 4 =>
      match i.val with
      | 0 => c₀ v0
      | 1 => c₀ v1
      | 2 => c₀ v2
      | _ => c₀ v3 := by
    funext ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => rfl
    | n + 4 => omega
  rw [hcexp]
  cases c₀ v0 <;> cases c₀ v1 <;> cases c₀ v2 <;> cases c₀ v3
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · refine ⟨_, Reach.single (Step.press _ v2 rfl), ?_⟩
    cases rule <;> decide
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · exact ⟨_, Reach.refl _, by decide⟩
  · refine ⟨_, Reach.single (Step.press _ v3 rfl), ?_⟩
    cases rule <;> decide
  · exact ⟨_, Reach.refl _, by decide⟩
  · refine ⟨_, Reach.single (Step.press _ v0 rfl), ?_⟩
    cases rule <;> decide
  · refine ⟨_, Reach.single (Step.press _ v1 rfl), ?_⟩
    cases rule <;> decide
  · refine ⟨_, Reach.single (Step.press _ v1 rfl), ?_⟩
    cases rule <;> decide

theorem p4Graph_minLit_le_ceilHalf (rule : MoveRule) (mlMode : MinLitMode) :
    minLit rule mlMode p4Graph ≤ ceilHalf 4 :=
  minLit_le_of_universal (by omega) rule mlMode p4Graph (ceilHalf 4)
    (p4Graph_reach_le_ceilHalf rule)

/-! ## 8. Converse Failure Under `σ⁻`: `Empty_{2m}` and `K_2 ⊔ Empty_{2m}` (`m ≥ 1`) -/

/-- The edgeless graph on `n` vertices. -/
def emptyGraph (n : Nat) : SimpleGraph n where
  adj := fun _ _ => false
  symm := fun _ _ => rfl
  loopless := fun _ => rfl

theorem emptyGraph_openNbr_invariant {n : Nat} {c₀ c : Config n}
    (hr : Reach .openNbr (emptyGraph n) c₀ c) : c = c₀ := by
  induction hr with
  | refl _ => rfl
  | @step c₁ _ _ hs _ ih =>
    rw [ih]
    cases hs with
    | press v _ =>
      funext u
      rfl

/-- Non-triviality witness on `n = 2`: `minLit .openNbr .fromAllLit (emptyGraph 2) = 2 > 1`. -/
theorem emptyGraph2_minLit_eq_two :
    minLit .openNbr .fromAllLit (emptyGraph 2) = 2 := by
  unfold minLit minLitAllLit
  obtain ⟨c, hr, hlc⟩ := minLitFrom_attained .openNbr (emptyGraph 2) (allLit 2)
  have hceq := emptyGraph_openNbr_invariant hr
  rw [hceq, litCount_allLit] at hlc
  exact hlc.symm

theorem emptyGraph_even_converse_counterexample {m : Nat} (hm : m ≥ 1) (mlMode : MinLitMode) :
    HasOddBipartition .existsSomeOdd (emptyGraph (2 * m)) ∧
    HasOddBipartition .existsBothOdd (emptyGraph (2 * m)) ∧
    ceilHalf (2 * m) < minLit .openNbr mlMode (emptyGraph (2 * m)) := by
  let χ : Fin (2 * m) → Bool := fun i => decide (i.val < 1)
  have hχ : (emptyGraph (2 * m)).IsBipartition χ := fun _ _ h => Bool.noConfusion h
  have hT : partTrueSize χ = 1 := countFin_lt (2 * m) 1 (by omega)
  have hF : partFalseSize χ = 2 * m - 1 := by
    have := partSizes_sum χ
    omega
  have hboth : isOddNat (partTrueSize χ) ∧ isOddNat (partFalseSize χ) := by
    unfold isOddNat; omega
  refine ⟨⟨χ, hχ, Or.inl hboth.1⟩, ⟨χ, hχ, hboth⟩, ?_⟩
  apply minLit_gt_of_allLit_gt (by omega) .openNbr mlMode (emptyGraph (2 * m)) (ceilHalf (2 * m))
  intro c hr
  rw [emptyGraph_openNbr_invariant hr, litCount_allLit]
  unfold ceilHalf
  omega

/-- `K_2 ⊔ Empty_{2m}` on `2m + 2` vertices: single edge `{0, 1}` plus `2m` isolated vertices. -/
def k2PlusEmpty (m : Nat) : SimpleGraph (2 * m + 2) where
  adj := fun u v => decide ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0))
  symm := by
    intro u v
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  loopless := by
    intro u
    exact decide_eq_false (by omega)

theorem k2PlusEmpty_hasEdge (m : Nat) : (k2PlusEmpty m).HasEdge := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  dsimp [k2PlusEmpty]
  decide

/-- Invariant on `K_2 ⊔ Empty_{2m}` under `σ⁻` from `allLit`:
    at least one of `{0, 1}` is lit AND all vertices `2 .. 2m+1` stay lit. -/
private def k2PlusEmptyInv (m : Nat) (c : Config (2 * m + 2)) : Prop :=
  (c ⟨0, by omega⟩ = true ∨ c ⟨1, by omega⟩ = true) ∧
  (∀ i : Fin (2 * m + 2), i.val ≥ 2 → c i = true)

private theorem k2PlusEmpty_inv_preserved (m : Nat) {c₁ c₂ : Config (2 * m + 2)}
    (hr : Reach .openNbr (k2PlusEmpty m) c₁ c₂) (hinv : k2PlusEmptyInv m c₁) :
    k2PlusEmptyInv m c₂ := by
  induction hr with
  | refl _ => exact hinv
  | @step ca _ _ hs _ ih =>
    apply ih
    cases hs with
    | press v hlit =>
      refine ⟨?_, ?_⟩
      · by_cases hv0 : v.val = 0
        · left
          have hveq : v = ⟨0, by omega⟩ := Fin.ext hv0
          rw [← hveq, toggleAt_openNbr_self]
          exact hlit
        · by_cases hv1 : v.val = 1
          · right
            have hveq : v = ⟨1, by omega⟩ := Fin.ext hv1
            rw [← hveq, toggleAt_openNbr_self]
            exact hlit
          · rcases hinv.1 with h0 | h1
            · left
              dsimp [toggleAt, k2PlusEmpty]
              have hfalse : decide ((v.val = 0 ∧ 0 = 1) ∨ (v.val = 1 ∧ 0 = 0)) = false :=
                decide_eq_false (by omega)
              rw [hfalse]
              exact h0
            · right
              dsimp [toggleAt, k2PlusEmpty]
              have hfalse : decide ((v.val = 0 ∧ 1 = 1) ∨ (v.val = 1 ∧ 1 = 0)) = false :=
                decide_eq_false (by omega)
              rw [hfalse]
              exact h1
      · intro i hi2
        dsimp [toggleAt, k2PlusEmpty]
        have hfalse : decide ((v.val = 0 ∧ i.val = 1) ∨ (v.val = 1 ∧ i.val = 0)) = false :=
          decide_eq_false (by omega)
        rw [hfalse]
        exact hinv.2 i hi2

/-- Converse Counterexample Family WITH Edges (`K_2 ⊔ Empty_{2m}`, `m ≥ 1`):
    Has edges, possesses an odd-odd bipartition `(1, 2m + 1)`, yet `minLit .openNbr > ⌈n/2⌉`. -/
theorem k2PlusEmpty_converse_counterexample {m : Nat} (hm : m ≥ 1) (mlMode : MinLitMode) :
    (k2PlusEmpty m).HasEdge ∧
    HasOddBipartition .existsSomeOdd (k2PlusEmpty m) ∧
    HasOddBipartition .existsBothOdd (k2PlusEmpty m) ∧
    ceilHalf (2 * m + 2) < minLit .openNbr mlMode (k2PlusEmpty m) := by
  let χ : Fin (2 * m + 2) → Bool := fun i => decide (i.val < 1)
  have hχ : (k2PlusEmpty m).IsBipartition χ := by
    intro u v hadj
    have h : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) := of_decide_eq_true hadj
    unfold χ
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [hu, hv]
  have hT : partTrueSize χ = 1 := countFin_lt (2 * m + 2) 1 (by omega)
  have hF : partFalseSize χ = 2 * m + 1 := by
    have := partSizes_sum χ
    omega
  have hboth : isOddNat (partTrueSize χ) ∧ isOddNat (partFalseSize χ) := by
    unfold isOddNat; omega
  refine ⟨k2PlusEmpty_hasEdge m, ⟨χ, hχ, Or.inl hboth.1⟩, ⟨χ, hχ, hboth⟩, ?_⟩
  apply minLit_gt_of_allLit_gt (by omega) .openNbr mlMode (k2PlusEmpty m) (ceilHalf (2 * m + 2))
  intro c hr
  have hinv0 : k2PlusEmptyInv m (allLit (2 * m + 2)) := ⟨Or.inl rfl, fun _ _ => rfl⟩
  have hinv := k2PlusEmpty_inv_preserved m hr hinv0
  have hunlit_le : countFin (2 * m + 2) (fun i => !(c i)) ≤ 1 := by
    rcases hinv.1 with h0 | h1
    · apply countFin_le_one_of_at_most_one (fun i => !(c i)) ⟨1, by omega⟩
      intro i hne
      have hival : i.val ≠ 1 := fun hv => hne (Fin.ext hv)
      by_cases hi0 : i.val = 0
      · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [hieq, h0]; rfl
      · have hi2 : i.val ≥ 2 := by omega
        rw [hinv.2 i hi2]; rfl
    · apply countFin_le_one_of_at_most_one (fun i => !(c i)) ⟨0, by omega⟩
      intro i hne
      have hival : i.val ≠ 0 := fun hv => hne (Fin.ext hv)
      by_cases hi1 : i.val = 1
      · have hieq : i = ⟨1, by omega⟩ := Fin.ext hi1
        rw [hieq, h1]; rfl
      · have hi2 : i.val ≥ 2 := by omega
        rw [hinv.2 i hi2]; rfl
  have hc_sum := countFin_not (2 * m + 2) c
  unfold litCount ceilHalf
  omega

/-! ## 9. Connected Non-Triviality Witness for `σ⁻` Worst-Case: Octahedron `K_{2,2,2}` (`n = 6`) -/

/-- `K_{2,2,2}` on 6 vertices with antipodal pairs `{0,1}`, `{2,3}`, `{4,5}`. -/
def octahedronGraph : SimpleGraph 6 where
  adj := fun u v => decide (u.val / 2 ≠ v.val / 2)
  symm := by intro u v; revert u v; decide
  loopless := by intro u; revert u; decide

theorem octahedronGraph_isConnected : octahedronGraph.IsConnected := by
  refine ⟨by omega, fun u v => ?_⟩
  let v0 : Fin 6 := ⟨0, by omega⟩
  let v2 : Fin 6 := ⟨2, by omega⟩
  have e02 : octahedronGraph.adj v0 v2 = true := by decide
  have to0 : ∀ x : Fin 6, Walk octahedronGraph x v0 := by
    intro ⟨x, hx⟩
    match x with
    | 0 => exact Walk.nil v0
    | 1 => exact Walk.cons (show octahedronGraph.adj ⟨1, by omega⟩ v2 = true by decide)
                           (Walk.single (show octahedronGraph.adj v2 v0 = true by decide))
    | 2 => exact Walk.single (show octahedronGraph.adj ⟨2, by omega⟩ v0 = true by decide)
    | 3 => exact Walk.single (show octahedronGraph.adj ⟨3, by omega⟩ v0 = true by decide)
    | 4 => exact Walk.single (show octahedronGraph.adj ⟨4, by omega⟩ v0 = true by decide)
    | 5 => exact Walk.single (show octahedronGraph.adj ⟨5, by omega⟩ v0 = true by decide)
    | n + 6 => omega
  have from0 : ∀ x : Fin 6, Walk octahedronGraph v0 x := by
    intro ⟨x, hx⟩
    match x with
    | 0 => exact Walk.nil v0
    | 1 => exact Walk.cons e02 (Walk.single (show octahedronGraph.adj v2 ⟨1, by omega⟩ = true by decide))
    | 2 => exact Walk.single e02
    | 3 => exact Walk.single (show octahedronGraph.adj v0 ⟨3, by omega⟩ = true by decide)
    | 4 => exact Walk.single (show octahedronGraph.adj v0 ⟨4, by omega⟩ = true by decide)
    | 5 => exact Walk.single (show octahedronGraph.adj v0 ⟨5, by omega⟩ = true by decide)
    | n + 6 => omega
  exact Walk.trans (to0 u) (from0 v)

private def octInvBool (c : Config 6) : Bool :=
  (c ⟨0, by omega⟩ == c ⟨1, by omega⟩) &&
  (c ⟨2, by omega⟩ == c ⟨3, by omega⟩) &&
  (c ⟨4, by omega⟩ == c ⟨5, by omega⟩) &&
  decide (litCount c = 4)

private theorem octInvBool_step (x : Config 6) (v : Fin 6) :
    octInvBool x = true → x v = true →
    octInvBool (toggleAt .openNbr octahedronGraph x v) = true := by
  have hxexp : x = fun i : Fin 6 =>
      match i.val with
      | 0 => x ⟨0, by omega⟩
      | 1 => x ⟨1, by omega⟩
      | 2 => x ⟨2, by omega⟩
      | 3 => x ⟨3, by omega⟩
      | 4 => x ⟨4, by omega⟩
      | _ => x ⟨5, by omega⟩ := by
    funext ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 => rfl
    | n + 6 => omega
  rw [hxexp]
  revert v
  cases x ⟨0, by omega⟩ <;> cases x ⟨1, by omega⟩ <;>
  cases x ⟨2, by omega⟩ <;> cases x ⟨3, by omega⟩ <;>
  cases x ⟨4, by omega⟩ <;> cases x ⟨5, by omega⟩ <;> decide

theorem octahedronGraph_worstAll_gt_ceilHalf :
    octahedronGraph.IsConnected ∧
    ceilHalf 6 < minLit .openNbr .worstAll octahedronGraph := by
  refine ⟨octahedronGraph_isConnected, ?_⟩
  let c₀ : Config 6 := fun i => decide (i.val < 4)
  have hinv0 : octInvBool c₀ = true := by decide
  have hpres : ∀ {ca cb : Config 6},
      Reach .openNbr octahedronGraph ca cb → octInvBool ca = true → octInvBool cb = true := by
    intro ca cb hr
    induction hr with
    | refl _ => exact id
    | @step x _ _ hs _ ih =>
      intro hx
      apply ih
      cases hs with
      | press v hlit => exact octInvBool_step x v hx hlit
  have hge4 : 4 ≤ minLitFrom .openNbr octahedronGraph c₀ := by
    obtain ⟨c, hr, hlc⟩ := minLitFrom_attained .openNbr octahedronGraph c₀
    have hcb : octInvBool c = true := hpres hr hinv0
    unfold octInvBool at hcb
    cases h4 : decide (litCount c = 4)
    · rw [h4] at hcb; simp at hcb
    · have hc4 : litCount c = 4 := of_decide_eq_true h4
      omega
  have hleW := le_minLitWorst .openNbr octahedronGraph c₀
  unfold minLit ceilHalf
  dsimp
  omega

/-! ## 10. Master Disproof Theorems Across All Conventions and Graph Classes -/

/-- Minimal Connected Non-Bipartite Counterexample (`K_3` on `n = 3`):
    `K_3` is connected, has NO odd bipartition under ANY of the 4 modes, yet satisfies
    `minLit rule mlMode K_3 ≤ ceilHalf 3 = 2` under ALL 6 game conventions. -/
theorem k3_counterexample_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    (completeGraph 3).IsConnected ∧
    minLit rule mlMode (completeGraph 3) ≤ ceilHalf 3 ∧
    ¬ HasOddBipartition bipMode (completeGraph 3) :=
  ⟨completeGraph_isConnected (by omega),
   completeGraph_minLit_le_ceilHalf (by omega) rule mlMode,
   completeGraph_not_hasOddBipartition (by omega) bipMode⟩

/-- Infinite Family of Connected Non-Bipartite Counterexamples (`K_n` for all `n ≥ 3`). -/
theorem kn_infinite_counterexample_family
    {n : Nat} (hn : n ≥ 3) (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    (completeGraph n).IsConnected ∧
    minLit rule mlMode (completeGraph n) ≤ ceilHalf n ∧
    ¬ HasOddBipartition bipMode (completeGraph n) :=
  ⟨completeGraph_isConnected (by omega),
   completeGraph_minLit_le_ceilHalf (by omega) rule mlMode,
   completeGraph_not_hasOddBipartition hn bipMode⟩

/-- Infinite Family of Connected Bipartite Counterexamples (`K_{2k, 2k}` for all `k ≥ 1`). -/
theorem k2k_bipartite_infinite_counterexample_family
    {k : Nat} (hk : k ≥ 1) (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    (evenCompleteBipartite k).IsConnected ∧
    (evenCompleteBipartite k).IsBipartite ∧
    minLit rule mlMode (evenCompleteBipartite k) ≤ ceilHalf (4 * k) ∧
    ¬ HasOddBipartition bipMode (evenCompleteBipartite k) :=
  ⟨evenCompleteBipartite_isConnected hk,
   evenCompleteBipartite_isBipartite k,
   evenCompleteBipartite_minLit_le_ceilHalf hk rule mlMode,
   evenCompleteBipartite_not_hasOddBipartition hk bipMode⟩

/-- Tree Counterexample (`P_4` on `n = 4`) across ALL 24 conventions. -/
theorem p4_tree_counterexample_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    p4Graph.IsTree ∧
    minLit rule mlMode p4Graph ≤ ceilHalf 4 ∧
    ¬ HasOddBipartition bipMode p4Graph :=
  ⟨p4Graph_isTree,
   p4Graph_minLit_le_ceilHalf rule mlMode,
   p4Graph_not_hasOddBipartition bipMode⟩

/-- MASTER REFUTATION 1: Official Conjecture 00000001242 is FALSE across all 24
    combinations of `(MoveRule, MinLitMode, OddBipMode)`. -/
theorem conjecture_00000001242_false_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    ¬ Conjecture00000001242 rule mlMode bipMode := by
  intro hconj
  have hiff := hconj 3 (by omega) (completeGraph 3)
  obtain ⟨_, hle, hnot⟩ := k3_counterexample_all_conventions rule mlMode bipMode
  exact hnot (hiff.mp hle)

/-- MASTER REFUTATION 2: Conjecture 00000001242 remains FALSE when restricted to
    CONNECTED graphs across all 24 convention combinations. -/
theorem conjecture_00000001242_false_connected_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    ¬ ConjectureConnected rule mlMode bipMode := by
  intro hconj
  obtain ⟨hconn, hle, hnot⟩ := k3_counterexample_all_conventions rule mlMode bipMode
  exact hnot ((hconj 3 (by omega) (completeGraph 3) hconn).mp hle)

/-- MASTER REFUTATION 3: Conjecture 00000001242 remains FALSE even when restricted to
    CONNECTED BIPARTITE graphs across all 24 convention combinations. -/
theorem conjecture_00000001242_false_connected_bipartite_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    ¬ ConjectureConnectedBipartite rule mlMode bipMode := by
  intro hconj
  obtain ⟨hconn, hbip, hle, hnot⟩ := k2k_bipartite_infinite_counterexample_family (k := 1) (by omega) rule mlMode bipMode
  exact hnot ((hconj 4 (by omega) (evenCompleteBipartite 1) hconn hbip).mp hle)

/-- MASTER REFUTATION 4: Conjecture 00000001242 remains FALSE even when restricted to
    TREES across all 24 convention combinations. -/
theorem conjecture_00000001242_false_trees_all_conventions
    (rule : MoveRule) (mlMode : MinLitMode) (bipMode : OddBipMode) :
    ¬ ConjectureTrees rule mlMode bipMode := by
  intro hconj
  obtain ⟨htree, hle, hnot⟩ := p4_tree_counterexample_all_conventions rule mlMode bipMode
  exact hnot ((hconj 4 (by omega) p4Graph htree).mp hle)

end Conjecture00000001242

/-! ## 11. Axiom Audit on All Main Theorems -/

#print axioms Conjecture00000001242.k2_positive_witness
#print axioms Conjecture00000001242.emptyGraph2_minLit_eq_two
#print axioms Conjecture00000001242.octahedronGraph_worstAll_gt_ceilHalf
#print axioms Conjecture00000001242.k3_counterexample_all_conventions
#print axioms Conjecture00000001242.kn_infinite_counterexample_family
#print axioms Conjecture00000001242.k2k_bipartite_infinite_counterexample_family
#print axioms Conjecture00000001242.p4_tree_counterexample_all_conventions
#print axioms Conjecture00000001242.emptyGraph_even_converse_counterexample
#print axioms Conjecture00000001242.k2PlusEmpty_converse_counterexample
#print axioms Conjecture00000001242.conjecture_00000001242_false_all_conventions
#print axioms Conjecture00000001242.conjecture_00000001242_false_connected_all_conventions
#print axioms Conjecture00000001242.conjecture_00000001242_false_connected_bipartite_all_conventions
#print axioms Conjecture00000001242.conjecture_00000001242_false_trees_all_conventions
