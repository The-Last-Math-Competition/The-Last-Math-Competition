import Mathlib

/-!
# A counterexample to conjecture 00000000046

Let `G_n` be the prime-sum graph: vertices `1, …, n`, with `i ~ j` exactly when
`i ≠ j` and `i + j` is prime. Conjecture 00000000046 asserts that `G_n`
converges in cut distance to the constant graphon `W ≡ 1/2`.

It does not, and the obstruction is not a matter of speed: **every `G_n` is
triangle-free**. Two distinct positive integers of the same parity sum to an
even number at least `4`, which is not prime, so `G_n` has no edge inside the
odd vertices or inside the even ones — `G_n` is bipartite — and among any three
vertices two share a parity.

Consequently the triangle density of `G_n` is `0` for every `n`, whereas the
constant graphon `1/2` has triangle density `1/8`. By the counting lemma
`|t(F, U) - t(F, U')| ≤ e(F)·δ_□(U, U')`, applied with `F = K₃`,

  `δ_□(W_{G_n}, 1/2) ≥ (1/8)/3 = 1/24`  for every `n`,

so the sequence is bounded away from the asserted limit.

This file formalizes the combinatorial core: `G_n` is bipartite between the odd
and even vertices, and is triangle-free, with the triangle count equal to `0`
for every `n`. Mathlib has no graph-limit theory — no graphons, no cut norm, no
homomorphism densities — so the passage from "triangle-free" to "bounded away
in cut distance" is carried out in the paper, not here.
-/

namespace Submission00000000046

open Finset

/-- Adjacency in the prime-sum graph. -/
def Adj (i j : ℕ) : Prop := i ≠ j ∧ Nat.Prime (i + j)

instance : DecidableRel Adj := fun i j => by unfold Adj; infer_instance

/-- Two distinct positive vertices of the same parity are never adjacent: their
sum is even and at least `4`. This is exactly the bipartiteness of `G_n`. -/
theorem not_adj_of_same_parity {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hne : i ≠ j) (hpar : i % 2 = j % 2) : ¬ Adj i j := by
  rintro ⟨-, hp⟩
  have hdvd : 2 ∣ i + j := by omega
  have hgt : 2 < i + j := by omega
  rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega

/-- Adjacent vertices have opposite parity. -/
theorem parity_ne_of_adj {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h : Adj i j) :
    i % 2 ≠ j % 2 := fun hpar => not_adj_of_same_parity hi hj h.1 hpar h

/-- `G_n` is triangle-free: among any three vertices two share a parity. -/
theorem no_triangle {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : Adj a b) (hbc : Adj b c) (hac : Adj a c) : False := by
  have h2 : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2 := by omega
  rcases h2 with h | h | h
  · exact not_adj_of_same_parity ha hb hab.1 h hab
  · exact not_adj_of_same_parity hb hc hbc.1 h hbc
  · exact not_adj_of_same_parity ha hc hac.1 h hac

/-- The number of triangles of `G_n`, counted over increasing triples. -/
def triangleCount (n : ℕ) : ℕ :=
  ((Icc 1 n ×ˢ Icc 1 n ×ˢ Icc 1 n).filter
    (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      Adj t.1 t.2.1 ∧ Adj t.2.1 t.2.2 ∧ Adj t.1 t.2.2)).card

/-- `G_n` has no triangles, for every `n`. -/
theorem triangleCount_eq_zero (n : ℕ) : triangleCount n = 0 := by
  rw [triangleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b, c⟩ hmem ⟨-, -, hab, hbc, hac⟩
  simp only [Finset.mem_product, Finset.mem_Icc] at hmem
  exact no_triangle hmem.1.1 hmem.2.1.1 hmem.2.2.1 hab hbc hac

end Submission00000000046
