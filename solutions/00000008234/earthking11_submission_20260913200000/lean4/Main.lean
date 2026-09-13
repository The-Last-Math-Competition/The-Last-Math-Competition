/-
  Disproof of conjecture `00000008234`.

  Conjecture (as filed). For `swap_graph`, the exchange graph whose vertices are
  the envy-free-up-to-one-good (EF1) allocations of `m` indivisible goods to `n`
  agents and whose edges are single-good transfers:

      Under arbitrary monotone valuations swap_graph is connected with diameter
      at most `m (n-1)`; an allocation that is simultaneously EF1 and Pareto
      optimal always exists and is reachable by a polynomial-time item-moving
      algorithm; and EFX allocations always exist for three agents, while a
      minimal counterexample, if one exists, must have exactly 4 agents and
      require a non-bimodal valuation profile.

  WE REFUTE THE FIRST CONJUNCT, hence the conjunction.

  Counterexample. Take `n = 2` agents, `m = 2` goods, and the unit additive
  valuation `v_i(g_j) = 1` for every agent `i` and good `j`. Unit additive
  valuations are monotone. With unit valuations the value of a bundle is its
  cardinality, and EF1 is equivalent to: every ordered pair `(i, j)` satisfies
  `|A_j| <= |A_i| + 1`, i.e. the bundle sizes differ by at most one.

    * allocation `A` = both goods to agent 0  : sizes (2, 0), gap 2, NOT EF1;
    * allocation `alloc01` = good `g` to agent `g` : sizes (1, 1), EF1;
    * allocation `alloc10` = good `g` to agent `1 - g` : sizes (1, 1), EF1;
    * allocation `B` = both goods to agent 1  : sizes (0, 2), gap 2, NOT EF1.

  So there are exactly two EF1 allocations, `alloc01` and `alloc10`, and they
  differ in both coordinates. Every single-good transfer out of an EF1
  allocation produces the bundle-size pattern (2, 0) or (0, 2), which is not
  EF1; therefore swap_graph has NO edges. A graph with two vertices and no edge
  is disconnected, so its diameter is infinite and the claimed bound
  `m (n-1) = 2` fails. This is formalised below in core Lean.

  The file uses CORE LEAN ONLY (`import Std`); it does not use Mathlib,
  `Finset`, `Matrix`, `ZMod`, `SimpleGraph`, `norm_num`, `linarith`, `omega`,
  or `sorry`. All numerical facts are proved by `decide`, and function equality
  is handled pointwise via `funext`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc8234

/-! ## Allocations, unit valuations, and the EF1 predicate -/

/-- An allocation of `m` indivisible goods to `n` agents, represented as the map
sending each good to its owner. This is the `Fin 2 → Fin 2` representation for
the counterexample `n = m = 2`, generalised to `Fin m → Fin n`. -/
abbrev Alloc (n m : Nat) := Fin m → Fin n

/-- The bundle of agent `i` is the list of goods `g` with `a g = i`, and its
cardinality is `bsize a i`. Under unit additive valuations `v_i(g) = 1` the
value of agent `i`'s bundle is exactly this cardinality. -/
def bsize {n m : Nat} (a : Alloc n m) (i : Fin n) : Nat :=
  ((List.finRange m).filter (fun g => decide (a g = i))).length

/-- The unit additive valuation of the bundle of agent `i`: every good is worth
`1`, so the bundle value is its cardinality. -/
abbrev value {n m : Nat} (a : Alloc n m) (i : Fin n) : Nat := bsize a i

/-- Agent `i` envies agent `j` when `j`'s bundle is worth strictly more than
`i`'s own bundle. -/
abbrev envy {n m : Nat} (a : Alloc n m) (i j : Fin n) : Prop := value a i < value a j

/-- **EF1, exactly as defined.** For every ordered pair of agents `(i, j)`
either `i` does not envy `j`, or there is a good `g` in `j`'s bundle whose
removal removes the envy, i.e. `v_i(A_j \ {g}) <= v_i(A_i)`. Under unit
valuations `v_i(A_j \ {g}) = value a j - 1`, which is what the last conjunct
expresses. -/
def ef1 {n m : Nat} (a : Alloc n m) : Prop :=
  ∀ i j : Fin n, ¬ envy a i j ∨ ∃ g : Fin m, a g = j ∧ value a j - 1 ≤ value a i

/-- Computable (Boolean) form of EF1 for unit valuations: the bundle sizes differ
by at most `1`. This is the form fed to `decide`; `ef1_iff_bool` below proves it
equivalent to the literal predicate `ef1` on the `2 × 2` counterexample. -/
def isEF1 {n m : Nat} (a : Alloc n m) : Bool :=
  (List.finRange n).all (fun i =>
    (List.finRange n).all (fun j => decide (bsize a j ≤ bsize a i + 1)))

/-! ## The four allocations of the `2 × 2` instance -/

/-- Both goods go to agent `0`: bundle sizes `(2, 0)`. -/
def alloc00 : Alloc 2 2 := fun _ => 0

/-- Good `g` goes to agent `g`: the diagonal allocation with sizes `(1, 1)`. -/
def alloc01 : Alloc 2 2 := fun g => g

/-- Good `g` goes to agent `1 - g`: the other diagonal allocation, sizes `(1, 1)`. -/
def alloc10 : Alloc 2 2 := fun g => if g = 0 then 1 else 0

/-- Both goods go to agent `1`: bundle sizes `(0, 2)`. -/
def alloc11 : Alloc 2 2 := fun _ => 1

/-- The list of all four allocations; `alloc_cases22` shows it is exhaustive. -/
def allAllocs22 : List (Alloc 2 2) := [alloc00, alloc01, alloc10, alloc11]

/-! ## Case analysis on `Fin 2` and on allocations -/

/-- Induction principle for `Fin 2`: to prove `C g` for all `g` it suffices to
prove `C 0` and `C 1`. Built from `Fin.cases` so that no Mathlib is needed. -/
theorem fin2_forall {C : Fin 2 → Prop} (h0 : C 0) (h1 : C 1) : ∀ g, C g :=
  Fin.cases (motive := fun g => C g) h0
    (fun i => Fin.cases (motive := fun k => C (Fin.succ k)) h1
      (fun j => Fin.elim0 j) i)

/-- Every element of `Fin 2` is `0` or `1`. -/
theorem fin2_val_cases (x : Fin 2) : x = 0 ∨ x = 1 :=
  fin2_forall (C := fun y => y = 0 ∨ y = 1) (Or.inl rfl) (Or.inr rfl) x

/-- **Exhaustiveness.** Every allocation of two goods to two agents is one of the
four listed ones. Proved pointwise with `funext` on the two values `a 0`, `a 1`,
since function equality is not decidable in core Lean. -/
theorem alloc_cases22 (a : Alloc 2 2) :
    a = alloc00 ∨ a = alloc01 ∨ a = alloc10 ∨ a = alloc11 := by
  rcases fin2_val_cases (a 0) with h0 | h0 <;>
  rcases fin2_val_cases (a 1) with h1 | h1
  · left;      funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc00, h0, h1]
  · right; left; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc01, h0, h1]
  · right; right; left; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc10, h0, h1]
  · right; right; right; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc11, h0, h1]

/-! ## Exactly two allocations are EF1 -/

/-- The unit valuation of each bundle in `alloc01`: both agents hold one good. -/
theorem value_alloc01 (i : Fin 2) : value alloc01 i = 1 :=
  fin2_forall (C := fun i => value alloc01 i = 1) (by decide) (by decide) i

/-- The unit valuation of each bundle in `alloc10`: both agents hold one good. -/
theorem value_alloc10 (i : Fin 2) : value alloc10 i = 1 :=
  fin2_forall (C := fun i => value alloc10 i = 1) (by decide) (by decide) i

/-- In `alloc00` agent `0` holds both goods. -/
theorem value_alloc00_zero : value alloc00 0 = 2 := by decide
/-- In `alloc00` agent `1` holds nothing. -/
theorem value_alloc00_one : value alloc00 1 = 0 := by decide
/-- In `alloc11` agent `0` holds nothing. -/
theorem value_alloc11_zero : value alloc11 0 = 0 := by decide
/-- In `alloc11` agent `1` holds both goods. -/
theorem value_alloc11_one : value alloc11 1 = 2 := by decide

/-- The diagonal allocation `alloc01` is EF1: neither agent envies the other. -/
theorem ef1_alloc01 : ef1 alloc01 := by
  intro i j
  left
  intro henv
  simp only [envy, value_alloc01] at henv
  exact absurd henv (by decide)

/-- The diagonal allocation `alloc10` is EF1: neither agent envies the other. -/
theorem ef1_alloc10 : ef1 alloc10 := by
  intro i j
  left
  intro henv
  simp only [envy, value_alloc10] at henv
  exact absurd henv (by decide)

/-- `alloc00` is NOT EF1: agent `1` (holding nothing) envies agent `0` (holding
both goods), and removing any single good from agent `0`'s bundle leaves it with
value `1 > 0`. -/
theorem not_ef1_alloc00 : ¬ ef1 alloc00 := by
  intro h
  have h10 := h 1 0
  rcases h10 with hnoenv | ⟨g, hg, hle⟩
  · have hlt : value alloc00 1 < value alloc00 0 := by decide
    exact hnoenv hlt
  · rw [value_alloc00_zero, value_alloc00_one] at hle
    exact absurd hle (by decide)

/-- `alloc11` is NOT EF1: agent `0` (holding nothing) envies agent `1` (holding
both goods), and removing any single good still leaves value `1 > 0`. -/
theorem not_ef1_alloc11 : ¬ ef1 alloc11 := by
  intro h
  have h01 := h 0 1
  rcases h01 with hnoenv | ⟨g, hg, hle⟩
  · have hlt : value alloc11 0 < value alloc11 1 := by decide
    exact hnoenv hlt
  · rw [value_alloc11_one, value_alloc11_zero] at hle
    exact absurd hle (by decide)

/-- The Boolean size-gap predicate on the four named allocations. -/
theorem isEF1_alloc00 : isEF1 alloc00 = false := by decide
theorem isEF1_alloc01 : isEF1 alloc01 = true := by decide
theorem isEF1_alloc10 : isEF1 alloc10 = true := by decide
theorem isEF1_alloc11 : isEF1 alloc11 = false := by decide

/-- **Classification.** The only EF1 allocations of the `2 × 2` instance with
unit valuations are the two diagonals. -/
theorem ef1_classification (a : Alloc 2 2) (h : ef1 a) :
    a = alloc01 ∨ a = alloc10 := by
  rcases alloc_cases22 a with h00 | h01 | h10 | h11
  · rw [h00] at h; exact (not_ef1_alloc00 h).elim
  · exact Or.inl h01
  · exact Or.inr h10
  · rw [h11] at h; exact (not_ef1_alloc11 h).elim

/-- On the `2 × 2` instance the literal EF1 predicate `ef1` agrees with the
computable size-gap predicate `isEF1`. -/
theorem ef1_iff_bool (a : Alloc 2 2) : ef1 a ↔ isEF1 a = true := by
  constructor
  · intro h
    rcases ef1_classification a h with rfl | rfl
    · exact isEF1_alloc01
    · exact isEF1_alloc10
  · intro h
    rcases alloc_cases22 a with h00 | h01 | h10 | h11
    · rw [h00] at h; exact absurd h (by decide)
    · rw [h01]; exact ef1_alloc01
    · rw [h10]; exact ef1_alloc10
    · rw [h11] at h; exact absurd h (by decide)

/-- **Exactly two allocations are EF1.** There are two EF1 allocations
(`alloc01` and `alloc10`), every EF1 allocation is one of these two, and a
filter of the four-allocation list counts exactly two. -/
theorem exactly_two_ef1 :
    ef1 alloc01 ∧ ef1 alloc10 ∧
    (∀ a : Alloc 2 2, ef1 a → a = alloc01 ∨ a = alloc10) ∧
    (allAllocs22.filter isEF1).length = 2 :=
  ⟨ef1_alloc01, ef1_alloc10, ef1_classification, by decide⟩

/-! ## The swap graph: adjacency, edges, and reachability -/

/-- Hamming distance between two allocations: the number of goods whose owner
changes. A single-good transfer is exactly a change of one coordinate. -/
abbrev hamming {n m : Nat} (a b : Alloc n m) : Nat :=
  ((List.finRange m).filter (fun g => decide (a g ≠ b g))).length

/-- **Swap-graph adjacency**: two allocations are adjacent when they differ in
exactly one coordinate, i.e. they are related by a single-good transfer. -/
abbrev Adj {n m : Nat} (a b : Alloc n m) : Prop := hamming a b = 1

/-- **No edge joins two EF1 allocations.** Any two EF1 allocations of the
`2 × 2` instance are the two diagonals, whose Hamming distance is `2`, so they
are not related by any single-good transfer. -/
theorem no_adj_ef1 (a b : Alloc 2 2) (ha : ef1 a) (hb : ef1 b) : ¬ Adj a b := by
  rcases ef1_classification a ha with rfl | rfl <;>
  rcases ef1_classification b hb with rfl | rfl <;>
  decide

/-- Reachability in the swap graph, restricted to EF1 vertices: `ReachN a k b`
means there is a length-`k` walk from `a` to `b` in which every vertex is EF1
and every step is a single-good transfer. The restriction to EF1 vertices is
essential: the full Hamming graph on all four allocations does connect the two
diagonals through the non-EF1 allocations. -/
inductive ReachN (a : Alloc 2 2) : Nat → Alloc 2 2 → Prop
  | zero : ReachN a 0 a
  | succ {k : Nat} {b c : Alloc 2 2} :
      ReachN a k b → ef1 c → Adj b c → ReachN a (k + 1) c

/-- Since there are no edges between EF1 allocations, every walk in the swap
graph starting at an EF1 allocation is trivial: its endpoint equals its start. -/
theorem reachN_eq {a : Alloc 2 2} (ha : ef1 a) :
    ∀ k b, ReachN a k b → b = a := by
  intro k
  induction k with
  | zero =>
      intro b h
      cases h
      rfl
  | succ k ih =>
      intro b h
      cases h with
      | succ hrec hc hadj =>
          have heq : _ = a := ih _ hrec
          rw [heq] at hadj
          exact (no_adj_ef1 a _ ha hc hadj).elim

/-- The two EF1 allocations are distinct; they differ at good `0`. -/
theorem alloc01_ne_alloc10 : alloc01 ≠ alloc10 := by
  intro h
  have h0 := congrArg (fun f : Alloc 2 2 => f 0) h
  exact (by decide : alloc01 0 ≠ alloc10 0) h0

/-- **No path connects the two EF1 allocations** in the swap graph. -/
theorem no_path_between_diagonals : ¬ (∃ k, ReachN alloc01 k alloc10) := by
  rintro ⟨k, hk⟩
  have heq : alloc10 = alloc01 := reachN_eq ef1_alloc01 k alloc10 hk
  exact alloc01_ne_alloc10 heq.symm

/-- The swap graph of the `2 × 2` instance is connected if every pair of EF1
allocations is joined by a walk in the graph. -/
def EF1Connected : Prop :=
  ∀ a b : Alloc 2 2, ef1 a → ef1 b → ∃ k, ReachN a k b

/-- **The swap graph is disconnected.** -/
theorem not_ef1_connected : ¬ EF1Connected := by
  intro h
  rcases h alloc01 alloc10 ef1_alloc01 ef1_alloc10 with ⟨k, hk⟩
  exact no_path_between_diagonals ⟨k, hk⟩

/-- The first conjunct of the conjecture for the `2 × 2` instance: the swap
graph is connected and has diameter at most `d`. -/
def SwapGraphDiameterAtMost (d : Nat) : Prop :=
  EF1Connected ∧ ∀ a b : Alloc 2 2, ef1 a → ef1 b → ∃ k, k ≤ d ∧ ReachN a k b

/-- **The claimed diameter bound fails.** The conjecture demands connectivity
with diameter at most `m (n-1) = 2 · (2-1) = 2`; the graph is in fact
disconnected, so the bound (indeed, any finite diameter bound) is false. -/
theorem claimed_diameter_bound_fails : ¬ SwapGraphDiameterAtMost 2 := by
  intro h
  exact not_ef1_connected h.1

/-- The numerical value of the conjectured bound at `n = m = 2`. -/
theorem bound_value : 2 * (2 - 1) = 2 := by decide

/-! ## The collected disproof -/

/-- **Conjecture `00000008234` is FALSE.** With `n = m = 2` and unit additive
(hence monotone) valuations: `alloc01` and `alloc10` are the only EF1
allocations; no edge of the swap graph joins two EF1 allocations; the two EF1
allocations are not connected by any walk in the swap graph; the swap graph is
disconnected; and the claimed diameter bound `m (n-1) = 2` (or any finite
diameter bound) fails. The first conjunct of the conjecture is false, hence so
is the conjunction. -/
theorem conjecture_00000008234_refuted :
    ef1 alloc01 ∧ ef1 alloc10 ∧
    (∀ a : Alloc 2 2, ef1 a → a = alloc01 ∨ a = alloc10) ∧
    (∀ a b : Alloc 2 2, ef1 a → ef1 b → ¬ Adj a b) ∧
    ¬ (∃ k, ReachN alloc01 k alloc10) ∧
    ¬ EF1Connected ∧
    ¬ SwapGraphDiameterAtMost 2 := by
  refine ⟨ef1_alloc01, ef1_alloc10, ef1_classification, ?_,
    no_path_between_diagonals, not_ef1_connected, claimed_diameter_bound_fails⟩
  intro a b ha hb
  exact no_adj_ef1 a b ha hb

end Tlmc8234
