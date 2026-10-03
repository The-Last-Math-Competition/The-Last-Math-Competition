import Mathlib

/-!
# Conjecture 00000003967: the 4-cycle attains the bound `2^d`

*Pebbling.* A distribution `p : V → ℕ` places pebbles on the vertices of a graph. A pebbling
move along an edge `u — v` removes two pebbles from `u` and adds one to `v`. A distribution
is `r`-solvable if some sequence of moves puts a pebble on the target `r`. The pebbling
number `π(G)` is the least `t` such that every distribution of `t` pebbles is `r`-solvable
for every target `r`.

Conjecture 00000003967 claims that the graphs attaining the bound `2^d` (`d` the diameter)
are exactly the paths, and that every 2-connected graph satisfies `π(G) ≤ 2^d (1 − c/log d)`
for a constant `c > 0`. The 4-cycle `C₄` has diameter `2` and `π(C₄) = 4 = 2²`, it is not a
path, and it is 2-connected; so both claims fail.

* `π(C₄) ≤ 4`: every distribution of four pebbles reaches every target within three moves
  (checked exhaustively by a verified bounded search).
* `π(C₄) ≥ 4`: with `t ≤ 3` pebbles on the vertex opposite the target, the weight
  `Ψ(p) = 4 p(0) + 2 p(1) + p(2) + 2 p(3)` (target `0`) never increases under moves, while a
  pebble on the target needs `Ψ ≥ 4`.
-/

namespace Submission00000003967

open SimpleGraph Finset

section Pebbling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distribution obtained from `p` by a pebbling move from `u` to `v`. -/
def moveFn (p : V → ℕ) (u v : V) : V → ℕ :=
  Function.update (Function.update p u (p u - 2)) v (p v + 1)

/-- A pebbling move along an edge `u — v` with at least two pebbles on `u`. -/
def Move (G : SimpleGraph V) (p q : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ p u ∧ q = moveFn p u v

/-- `p` is `r`-solvable: some sequence of moves puts at least one pebble on `r`. -/
def Solvable (G : SimpleGraph V) (p : V → ℕ) (r : V) : Prop :=
  ∃ q, Relation.ReflTransGen (Move G) p q ∧ 1 ≤ q r

/-- The pebbling number: the least `t` such that every distribution of `t` pebbles is
`r`-solvable for every target `r`. -/
noncomputable def pebblingNumber (G : SimpleGraph V) : ℕ :=
  sInf {t | ∀ p : V → ℕ, ∑ v, p v = t → ∀ r, Solvable G p r}

end Pebbling

/-- 2-connectedness: at least three vertices, connected, and still connected after deleting
any single vertex. -/
def TwoConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected

/-- First claim: a connected graph on `n` vertices attains `π(G) = 2^{diam G}` iff it is
(isomorphic to) a path. -/
def Claim1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    (pebblingNumber G = 2 ^ G.diam ↔ ∃ m, Nonempty (G ≃g pathGraph m))

/-- Second claim: for some constant `c > 0`, every 2-connected graph of diameter `d ≥ 2`
satisfies `π(G) ≤ 2^d (1 − c / log d)`. -/
def Claim2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), TwoConnected G → 2 ≤ G.diam →
    (pebblingNumber G : ℝ) ≤ 2 ^ G.diam * (1 - c / Real.log G.diam)

/-! ### The 4-cycle -/

/-- The 4-cycle `0 — 1 — 2 — 3 — 0` (Mathlib's `cycleGraph 4`). -/
abbrev C4 : SimpleGraph (Fin 4) := cycleGraph 4

theorem C4_connected : C4.Connected := by decide

theorem twoConnected_C4 : TwoConnected C4 := ⟨by simp, C4_connected, by decide⟩

/-- Any two vertices of `C₄` are equal, adjacent, or have a common neighbour. -/
theorem C4_close : ∀ u v : Fin 4, u = v ∨ C4.Adj u v ∨ ∃ w, C4.Adj u w ∧ C4.Adj w v := by
  decide

theorem diam_C4 : C4.diam = 2 := by
  have hle : C4.ediam ≤ 2 := by
    refine ediam_le_iff.2 fun u v => ?_
    rcases C4_close u v with rfl | h | ⟨w, h₁, h₂⟩
    · simp
    · rw [edist_eq_one_iff_adj.2 h]; norm_num
    · exact (edist_le (Walk.cons h₁ (Walk.cons h₂ Walk.nil))).trans (by simp)
  have hge : 2 ≤ C4.ediam := by
    refine le_trans ?_ (edist_le_ediam (u := 0) (v := 2))
    have h0 : C4.edist 0 2 ≠ 0 := fun h => by simpa using edist_eq_zero_iff.1 h
    have h1 : C4.edist 0 2 ≠ 1 := fun h => by
      have := edist_eq_one_iff_adj.1 h
      revert this; decide
    generalize C4.edist 0 2 = e at h0 h1
    induction e using ENat.recTopCoe with
    | top => exact le_top
    | coe e =>
      norm_cast at h0 h1 ⊢
      omega
  unfold SimpleGraph.diam
  rw [le_antisymm hle hge]
  rfl

instance (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

/-- `C₄` is not a path: it has four edges, while a path on four vertices has three. -/
theorem C4_not_path : ¬ ∃ m, Nonempty (C4 ≃g pathGraph m) := by
  rintro ⟨m, ⟨e⟩⟩
  have hm : m = 4 := by simpa using (Fintype.card_congr e.toEquiv).symm
  subst hm
  have := e.card_edgeFinset_eq
  revert this
  decide

/-! ### `π(C₄) ≤ 4`: a verified bounded search -/

/-- Depth-bounded search for a sequence of moves putting a pebble on `r`. -/
def solve : ℕ → (Fin 4 → ℕ) → Fin 4 → Bool
  | 0, p, r => decide (1 ≤ p r)
  | k + 1, p, r => decide (1 ≤ p r) || (List.finRange 4).any fun u =>
      (List.finRange 4).any fun v =>
        decide (C4.Adj u v) && decide (2 ≤ p u) && solve k (moveFn p u v) r

/-- The search is sound. -/
theorem solve_sound : ∀ k p r, solve k p r = true → Solvable C4 p r
  | 0, p, r, h => ⟨p, .refl, by simpa [solve] using h⟩
  | k + 1, p, r, h => by
    simp only [solve, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_finRange,
      true_and, Bool.and_eq_true] at h
    rcases h with h | ⟨u, v, ⟨hadj, hu⟩, hs⟩
    · exact ⟨p, .refl, h⟩
    · obtain ⟨q, hq, hqr⟩ := solve_sound k _ r hs
      exact ⟨q, .head ⟨u, v, hadj, hu, rfl⟩ hq, hqr⟩

/-- Every distribution of four pebbles on `C₄` reaches every target within three moves. -/
theorem solve_all : ∀ a b c d : Fin 5, (a : ℕ) + b + c + d = 4 →
    ∀ r, solve 3 ![(a : ℕ), b, c, d] r = true := by
  decide

theorem four_mem : ∀ p : Fin 4 → ℕ, ∑ v, p v = 4 → ∀ r, Solvable C4 p r := by
  intro p hp r
  rw [Fin.sum_univ_four] at hp
  have hpe : p = ![p 0, p 1, p 2, p 3] := by
    funext i; fin_cases i <;> rfl
  have := solve_all ⟨p 0, by omega⟩ ⟨p 1, by omega⟩ ⟨p 2, by omega⟩ ⟨p 3, by omega⟩ hp r
  rw [hpe]
  exact solve_sound 3 _ r this

/-! ### `π(C₄) ≥ 4`: a weight argument -/

/-- Weight for target `0`: `Ψ(p) = 4 p(0) + 2 p(1) + p(2) + 2 p(3)`. -/
def weight (p : Fin 4 → ℕ) : ℕ := 4 * p 0 + 2 * p 1 + p 2 + 2 * p 3

/-- A pebbling move never increases the weight. -/
theorem weight_move {p q : Fin 4 → ℕ} (h : Move C4 p q) : weight q ≤ weight p := by
  obtain ⟨u, v, hadj, hu, rfl⟩ := h
  have edges : ∀ u v : Fin 4, C4.Adj u v →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨ (u = 3 ∧ v = 0) ∨ (u = 0 ∧ v = 3) := by decide
  rcases edges u v hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [weight, moveFn, Function.update_apply] <;> simp <;> omega

theorem weight_reach {p q : Fin 4 → ℕ} (h : Relation.ReflTransGen (Move C4) p q) :
    weight q ≤ weight p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hmove ih => exact (weight_move hmove).trans ih

/-- With `t ≤ 3` pebbles, all on vertex `2`, the target `0` cannot be reached. -/
theorem not_solvable (t : ℕ) (ht : t ≤ 3) :
    ¬ Solvable C4 (fun v => if v = 2 then t else 0) 0 := by
  rintro ⟨q, hq, hq0⟩
  have := weight_reach hq
  simp [weight] at this
  omega

theorem pebblingNumber_C4 : pebblingNumber C4 = 4 := by
  have h4 : (4 : ℕ) ∈ {t | ∀ p : Fin 4 → ℕ, ∑ v, p v = t → ∀ r, Solvable C4 p r} := four_mem
  unfold pebblingNumber
  apply le_antisymm (Nat.sInf_le h4)
  refine le_csInf ⟨4, h4⟩ fun t ht => ?_
  by_contra hlt
  push Not at hlt
  exact not_solvable t (by omega) (ht (fun v => if v = 2 then t else 0) (by simp) 0)

/-! ### The two claims fail -/

/-- **The first claim fails**: `π(C₄) = 4 = 2^{diam C₄}`, but `C₄` is not a path. -/
theorem not_claim1 : ¬ Claim1 := by
  intro h
  have := (h 4 C4 C4_connected).1 (by rw [pebblingNumber_C4, diam_C4]; norm_num)
  exact C4_not_path this

/-- **The second claim fails**: `C₄` is 2-connected with `d = 2`, and
`π(C₄) = 4 > 4 (1 − c / log 2)` for every `c > 0`. -/
theorem not_claim2 : ¬ Claim2 := by
  rintro ⟨c, hc, h⟩
  have := h 4 C4 twoConnected_C4 (by rw [diam_C4])
  rw [pebblingNumber_C4, diam_C4] at this
  have hlog : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have hdiv : 0 < c / Real.log ((2 : ℕ) : ℝ) := div_pos hc hlog
  push_cast at this hdiv
  nlinarith

/-- **Conjecture 00000003967 is false**: both of its claims fail. -/
theorem conjecture_00000003967_false : ¬ Claim1 ∧ ¬ Claim2 := ⟨not_claim1, not_claim2⟩

end Submission00000003967

#print axioms Submission00000003967.conjecture_00000003967_false
