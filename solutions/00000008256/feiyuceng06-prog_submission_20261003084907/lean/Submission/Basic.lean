import Mathlib

/-!
# Conjecture 00000008256: a maximal Condorcet domain exceeds the stated bound

A *domain* is a set of strict linear orders (preferences) on `n` alternatives. It *admits
Condorcet winners* if every profile with an odd number of voters, all of whose preferences
lie in the domain, has a Condorcet winner: an alternative that beats every other one by a
strict majority. A *maximal Condorcet domain* admits Condorcet winners and is not contained
in any strictly larger domain that does.

The first claim of Conjecture 00000008256 is that every maximal Condorcet domain has at most
`2^{n-1} · n! / 2^{n(n-1)/2}` orders. For `n = 3` this bound is `4 · 6 / 8 = 3`. The
single-peaked domain for the axis `0 < 1 < 2`, i.e. the four orders in which the middle
alternative `1` is not ranked last, is a maximal Condorcet domain with `4 > 3` orders:

* it admits Condorcet winners (Black's median voter theorem for three alternatives): if a
  strict majority ranks `0` first, `0` wins; if a strict majority ranks `2` first, `2` wins;
  otherwise `1` beats `0` (every voter not ranking `0` first prefers `1` to `0`) and beats
  `2` likewise;
* it is maximal: the two remaining orders `0 ≻ 2 ≻ 1` and `2 ≻ 0 ≻ 1` each complete a
  Condorcet cycle with two orders of the domain.

A strict linear order on `Fin n` is encoded by its ranking `r : Fin n ≃ Fin n`, where `r a`
is the position of alternative `a` (`0` is the top) and `a` is preferred to `b` iff
`r a < r b`. Every linear order corresponds to exactly one ranking.
-/

namespace Submission00000008256

open Finset

/-- A strict linear order on the alternatives `Fin n`, encoded by its ranking: `r a` is the
position of `a`, with `0` the top, and `a` is preferred to `b` iff `r a < r b`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

/-- In the profile `v` (voter `i` has ranking `v i`), alternative `a` beats `b` by a strict
majority: more than half of the `m` voters prefer `a` to `b`. -/
def Beats {n m : ℕ} (v : Fin m → Ranking n) (a b : Fin n) : Prop :=
  m < 2 * #{i | v i a < v i b}

instance {n m : ℕ} (v : Fin m → Ranking n) (a b : Fin n) : Decidable (Beats v a b) := by
  unfold Beats; infer_instance

/-- `a` is a Condorcet winner of the profile `v`: it beats every other alternative. -/
def IsCondorcetWinner {n m : ℕ} (v : Fin m → Ranking n) (a : Fin n) : Prop :=
  ∀ b, b ≠ a → Beats v a b

instance {n m : ℕ} (v : Fin m → Ranking n) (a : Fin n) :
    Decidable (IsCondorcetWinner v a) := by
  unfold IsCondorcetWinner; infer_instance

/-- A domain admits Condorcet winners if every profile with an odd number of voters, all of
whose preferences lie in the domain, has a Condorcet winner. -/
def AdmitsCondorcetWinners {n : ℕ} (D : Finset (Ranking n)) : Prop :=
  ∀ m : ℕ, Odd m → ∀ v : Fin m → Ranking n, (∀ i, v i ∈ D) → ∃ a, IsCondorcetWinner v a

/-- A maximal Condorcet domain: it admits Condorcet winners, and every domain containing it
that admits Condorcet winners is equal to it. -/
def IsMaximalCondorcetDomain {n : ℕ} (D : Finset (Ranking n)) : Prop :=
  AdmitsCondorcetWinners D ∧
    ∀ D' : Finset (Ranking n), D ⊆ D' → AdmitsCondorcetWinners D' → D' = D

/-- The first claim of Conjecture 00000008256: every maximal Condorcet domain on `n`
alternatives has at most `2^{n-1} · n! / 2^{n(n-1)/2}` orders. -/
def SizeBound : Prop :=
  ∀ (n : ℕ) (D : Finset (Ranking n)), IsMaximalCondorcetDomain D →
    (D.card : ℝ) ≤ 2 ^ (n - 1) * (n.factorial : ℝ) / 2 ^ (n * (n - 1) / 2)

/-! ### The single-peaked domain on three alternatives -/

/-- The single-peaked domain for the axis `0 < 1 < 2`: the orders in which the middle
alternative `1` is not ranked last, namely `0≻1≻2`, `1≻0≻2`, `1≻2≻0`, `2≻1≻0`. -/
def singlePeaked : Finset (Ranking 3) := univ.filter fun r => r 1 ≠ 2

theorem card_singlePeaked : singlePeaked.card = 4 := by decide

/-- In the single-peaked domain, `1` is preferred to `0` exactly when `0` is not on top. -/
theorem prefers_one_zero : ∀ r ∈ singlePeaked, (r 1 < r 0 ↔ r 0 ≠ 0) := by decide

/-- In the single-peaked domain, `1` is preferred to `2` exactly when `2` is not on top. -/
theorem prefers_one_two : ∀ r ∈ singlePeaked, (r 1 < r 2 ↔ r 2 ≠ 0) := by decide

/-- The alternative on top is preferred to every other alternative. -/
theorem top_prefers {n : ℕ} [NeZero n] (r : Ranking n) {a b : Fin n} (ha : r a = 0) (hb : b ≠ a) :
    r a < r b := by
  rw [ha, Fin.pos_iff_ne_zero, ← ha]
  exact fun h => hb (r.injective h)

/-- If more than half of the voters rank `a` on top, then `a` is a Condorcet winner. -/
theorem condorcetWinner_of_majority_top {n m : ℕ} [NeZero n] (v : Fin m → Ranking n) (a : Fin n)
    (h : m < 2 * #{i | v i a = 0}) : IsCondorcetWinner v a := by
  intro b hb
  unfold Beats
  have : #{i | v i a = 0} ≤ #{i | v i a < v i b} :=
    card_le_card fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact top_prefers (v i) hi hb
  omega

/-- The number of voters not satisfying `p` is `m` minus the number satisfying it. -/
theorem card_filter_not {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    #{i | ¬ p i} = m - #{i | p i} := by
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]

/-- **Black's theorem for three alternatives**: the single-peaked domain admits Condorcet
winners. -/
theorem admitsCondorcetWinners_singlePeaked : AdmitsCondorcetWinners singlePeaked := by
  intro m hm v hv
  by_cases h0 : m < 2 * #{i | v i 0 = 0}
  · exact ⟨0, condorcetWinner_of_majority_top v 0 h0⟩
  by_cases h2 : m < 2 * #{i | v i 2 = 0}
  · exact ⟨2, condorcetWinner_of_majority_top v 2 h2⟩
  refine ⟨1, fun b hb => ?_⟩
  obtain ⟨k, rfl⟩ := hm
  unfold Beats
  have e0 : #{i | v i 1 < v i 0} = 2 * k + 1 - #{i | v i 0 = 0} := by
    rw [← card_filter_not]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact prefers_one_zero (v i) (hv i)
  have e2 : #{i | v i 1 < v i 2} = 2 * k + 1 - #{i | v i 2 = 0} := by
    rw [← card_filter_not]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact prefers_one_two (v i) (hv i)
  fin_cases b
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [e0]
    omega
  · exact absurd rfl hb
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e2]
    omega

/-- Each order outside the single-peaked domain completes a Condorcet cycle with two orders of
the domain: some three-voter profile has no Condorcet winner. -/
theorem cycle_of_not_mem : ∀ σ : Ranking 3, σ ∉ singlePeaked →
    ∃ τ₁ ∈ singlePeaked, ∃ τ₂ ∈ singlePeaked, ∀ a, ¬ IsCondorcetWinner ![σ, τ₁, τ₂] a := by
  decide

/-- The single-peaked domain on three alternatives is a maximal Condorcet domain. -/
theorem isMaximalCondorcetDomain_singlePeaked : IsMaximalCondorcetDomain singlePeaked := by
  refine ⟨admitsCondorcetWinners_singlePeaked, fun D' hsub hD' => ?_⟩
  refine Subset.antisymm (fun σ hσ => ?_) hsub
  by_contra hσD
  obtain ⟨τ₁, h₁, τ₂, h₂, hno⟩ := cycle_of_not_mem σ hσD
  obtain ⟨a, ha⟩ := hD' 3 (by decide) ![σ, τ₁, τ₂] (by
    intro i
    fin_cases i
    · exact hσ
    · exact hsub h₁
    · exact hsub h₂)
  exact hno a ha

/-- **Conjecture 00000008256 is false**: for `n = 3` the bound is `3`, but the single-peaked
domain is a maximal Condorcet domain with `4` orders. -/
theorem conjecture_00000008256_false : ¬ SizeBound := by
  intro h
  have := h 3 singlePeaked isMaximalCondorcetDomain_singlePeaked
  rw [card_singlePeaked] at this
  norm_num [Nat.factorial] at this

/-- The conjecture is the conjunction of four claims; whatever the other three claims
(`P`, `Q`, `R`) mean, the conjunction is false. -/
theorem conjecture_00000008256_false' (P Q R : Prop) : ¬ (SizeBound ∧ P ∧ Q ∧ R) :=
  fun h => conjecture_00000008256_false h.1

end Submission00000008256

#print axioms Submission00000008256.conjecture_00000008256_false
