import Mathlib

/-!
# A counterexample to conjecture 00000000045

Let `G_n` be the prime-sum graph: vertices `1, …, n`, with `i ~ j` exactly when
`i + j` is prime. Conjecture 00000000045 asserts that `G_n` has a Hamilton
cycle for all sufficiently large `n`. It does not: **`G_n` has a Hamilton cycle
only when `n` is even**, so every odd `n ≥ 3` is a counterexample.

A Hamilton cycle is a cyclic arrangement `v₀, v₁, …, v_{n-1}` of all `n`
vertices with `vᵢ ~ v_{i+1}` throughout, indices mod `n`. Summing the edge
labels around the cycle,

  `∑ᵢ (vᵢ + v_{i+1}) = 2 ∑ᵢ vᵢ`,

because the cyclic shift permutes the positions. The left side is a sum of `n`
primes, each larger than `2` and therefore odd, so it is congruent to `n`
modulo `2`; the right side is even. Hence `n` is even.

Equivalently, `G_n` is bipartite between the odd and the even vertices — two
vertices of the same parity sum to an even number exceeding `2` — and a
bipartite graph with a Hamilton cycle has equal sides.
-/

namespace Submission00000000045

open Finset

variable {n : ℕ}

/-- The cyclic successor of a position: `i + 1`, wrapping to `0` at the end. -/
def cycSucc (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩
  else ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩

theorem cycSucc_injective : Function.Injective (cycSucc : Fin n → Fin n) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  simp only [cycSucc] at hv
  split_ifs at hv <;> simp only [] at hv <;> exact Fin.ext (by omega)

theorem cycSucc_bijective : Function.Bijective (cycSucc : Fin n → Fin n) :=
  Finite.injective_iff_bijective.1 cycSucc_injective

/-- For `n ≥ 3` a position is never its own cyclic successor. -/
theorem cycSucc_ne (hn : 3 ≤ n) (i : Fin n) : cycSucc i ≠ i := by
  intro hEq
  have hi := i.isLt
  have hv := congrArg Fin.val hEq
  simp only [cycSucc] at hv
  split_ifs at hv <;> simp only [] at hv <;> omega

/-- A Hamilton cycle of `G_n`: a cyclic arrangement of all `n` vertices
`1, …, n` — encoded by a permutation `σ` of the positions `Fin n`, the vertex at
position `i` being `σ i + 1` — in which consecutive vertices are adjacent, that
is, sum to a prime. -/
def HasPrimeHamiltonCycle (n : ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
    Nat.Prime (((σ i).val + 1) + ((σ (cycSucc i)).val + 1))

/-- Conjecture 00000000045. -/
def ConjectureHolds : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → HasPrimeHamiltonCycle n

/-- A Hamilton cycle in `G_n` forces `n` to be even. -/
theorem even_of_hasPrimeHamiltonCycle (hn : 3 ≤ n) (h : HasPrimeHamiltonCycle n) :
    Even n := by
  obtain ⟨σ, hσ⟩ := h
  set v : Fin n → ℕ := fun i => (σ i).val + 1 with hv
  -- The cyclic shift permutes the positions, so the shifted sum is unchanged.
  have hshift : ∑ i : Fin n, v (cycSucc i) = ∑ i : Fin n, v i :=
    Fintype.sum_bijective cycSucc cycSucc_bijective _ _ (fun _ => rfl)
  have hsum : ∑ i : Fin n, (v i + v (cycSucc i)) = 2 * ∑ i : Fin n, v i := by
    rw [Finset.sum_add_distrib, hshift]; ring
  -- Every edge label is a prime greater than 2, hence odd.
  have hodd : ∀ i : Fin n, (v i + v (cycSucc i)) % 2 = 1 := by
    intro i
    have hne : σ (cycSucc i) ≠ σ i := fun hEq => cycSucc_ne hn i (σ.injective hEq)
    have hvne : (σ (cycSucc i)).val ≠ (σ i).val := fun hEq => hne (Fin.ext hEq)
    have h2 : ((σ i).val + 1) + ((σ (cycSucc i)).val + 1) ≠ 2 := by omega
    obtain ⟨k, hk⟩ := (hσ i).odd_of_ne_two h2
    simp only [hv]
    omega
  -- A sum of n odd numbers is congruent to n modulo 2.
  have hmod : (∑ i : Fin n, (v i + v (cycSucc i))) % 2 = n % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => hodd i)]
    simp [Nat.mul_mod]
  rw [hsum] at hmod
  rw [Nat.even_iff]
  omega

/-- Conjecture 00000000045 is false: every odd `n ≥ 3` is a counterexample, so
no threshold `N` works. -/
theorem conjecture_00000000045_false : ¬ ConjectureHolds := by
  rintro ⟨N, hN⟩
  have hev := even_of_hasPrimeHamiltonCycle (n := 2 * N + 3) (by omega)
    (hN (2 * N + 3) (by omega))
  rw [Nat.even_iff] at hev
  omega

end Submission00000000045
