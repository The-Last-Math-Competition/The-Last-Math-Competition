import Mathlib

/-!
# Conjecture 00000000049

Conjecture 00000000049 asserts, of point sets in the plane all of whose
pairwise distances are prime, that the maximal size is `4` and that a set of
size `4` exists. Both are true. The plane is modeled as `ℂ` with its usual
metric, which is the Euclidean plane as a metric space.

## Contents

* `ConjectureHolds` — the conjecture, both parts.
* `witness`, `conjecture_part_b` — **part (b)**, in full: the four collinear
  points `0, 2, 5, 7`, whose six pairwise distances are `2, 5, 7, 3, 5, 2`.
* `no_five_collinear` — no five collinear points have pairwise prime
  distances. This is the final step of part (a), proved here in full.
* `no_prime_sq_add_sq_eq_sixteen`, `no_prime_sq_eq_sq_add_eight`,
  `circumradius_ne_two` — the arithmetic obstructions that the case analysis
  of part (a) appeals to in the accompanying paper.

## Scope

Part (a) — that no five points in the plane have pairwise prime distances — is
proved completely in the paper. Its proof runs through a Gram-determinant
identity for four coplanar points, a case analysis on which pairs lie at
distance `2`, and several coordinate computations. Those geometric steps are
**not** formalized here. What is formalized is part (b) in full, the final
collinear step of part (a), and the arithmetic obstructions used along the way.
-/

namespace Submission00000000049

/-- A family of points in the plane, pairwise distinct, all of whose pairwise
distances are prime. -/
def IsPrimeDistanceSet {n : ℕ} (P : Fin n → ℂ) : Prop :=
  Function.Injective P ∧
    ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ dist (P i) (P j) = (p : ℝ)

/-- Conjecture 00000000049: the maximal size is `4`, and size `4` occurs. -/
def ConjectureHolds : Prop :=
  (∀ (n : ℕ) (P : Fin n → ℂ), IsPrimeDistanceSet P → n ≤ 4) ∧
    (∃ P : Fin 4 → ℂ, IsPrimeDistanceSet P)

/-! ## Part (b): a configuration of size four -/

/-- The abscissae of the witness: four collinear points. -/
def xs : Fin 4 → ℝ := ![0, 2, 5, 7]

/-- The witness, as points of the plane. -/
def witness : Fin 4 → ℂ := fun i => (xs i : ℂ)

/-- The pairwise distances, tabulated (the diagonal is `0`). -/
def dTable : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 5, 7], ![2, 0, 3, 5], ![5, 3, 0, 2], ![7, 5, 2, 0]]

theorem dist_witness (i j : Fin 4) : dist (witness i) (witness j) = |xs i - xs j| := by
  have h : ((xs i : ℂ) - (xs j : ℂ)) = ((xs i - xs j : ℝ) : ℂ) := by push_cast; ring
  rw [witness, witness, Complex.dist_eq, h, Complex.norm_real, Real.norm_eq_abs]

theorem abs_xs_eq (i j : Fin 4) : |xs i - xs j| = (dTable i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> norm_num [xs, dTable]

theorem dTable_prime (i j : Fin 4) (hij : i ≠ j) : (dTable i j).Prime := by
  revert hij; fin_cases i <;> fin_cases j <;> decide

theorem witness_injective : Function.Injective witness := by
  intro i j hij
  by_contra hne
  have h0 : dist (witness i) (witness j) = 0 := by rw [hij, dist_self]
  rw [dist_witness, abs_xs_eq] at h0
  have hp := dTable_prime i j hne
  have : dTable i j = 0 := by exact_mod_cast h0
  exact hp.ne_zero this

theorem conjecture_part_b : ∃ P : Fin 4 → ℂ, IsPrimeDistanceSet P := by
  refine ⟨witness, witness_injective, fun i j hij => ⟨dTable i j, dTable_prime i j hij, ?_⟩⟩
  rw [dist_witness, abs_xs_eq]

/-! ## Parity lemmas -/

/-- The sum of two odd primes is never prime: it is even and exceeds `2`. -/
theorem not_prime_add_of_ne_two {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (hu2 : u ≠ 2) (hv2 : v ≠ 2) : ¬ (u + v).Prime := by
  obtain ⟨k, hk⟩ := hu.odd_of_ne_two hu2
  obtain ⟨l, hl⟩ := hv.odd_of_ne_two hv2
  have hu2' := hu.two_le
  have hv2' := hv.two_le
  intro h
  have hdvd : 2 ∣ u + v := ⟨k + l + 1, by omega⟩
  rcases h.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega

/-- If two primes sum to a prime, exactly one of them is `2`. -/
theorem eq_two_of_add_prime {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (h : (u + v).Prime) : (u = 2 ∧ v ≠ 2) ∨ (u ≠ 2 ∧ v = 2) := by
  by_cases hu2 : u = 2 <;> by_cases hv2 : v = 2
  · exact absurd h (by rw [hu2, hv2]; decide)
  · exact Or.inl ⟨hu2, hv2⟩
  · exact Or.inr ⟨hu2, hv2⟩
  · exact absurd h (not_prime_add_of_ne_two hu hv hu2 hv2)

/-! ## No five collinear points -/

/-- Five points on a line cannot have all ten pairwise distances prime.

Consecutive gaps `g₁, g₂, g₃, g₄` are prime, and so is each sum of consecutive
ones. No two adjacent gaps are both odd, so the pattern alternates between `2`
and an odd prime; either way the total span `g₁+g₂+g₃+g₄` is even and at least
`10`, hence not prime. -/
theorem no_five_collinear (g : Fin 4 → ℕ)
    (hg : ∀ i, (g i).Prime)
    (h2 : ∀ i : Fin 3, (g i.castSucc + g i.succ).Prime)
    (htot : (g 0 + g 1 + g 2 + g 3).Prime) : False := by
  have e01 := eq_two_of_add_prime (hg 0) (hg 1) (by simpa using h2 0)
  have e12 := eq_two_of_add_prime (hg 1) (hg 2) (by simpa using h2 1)
  have e23 := eq_two_of_add_prime (hg 2) (hg 3) (by simpa using h2 2)
  -- the pattern of twos alternates
  have key : (g 0 = 2 ∧ g 1 ≠ 2 ∧ g 2 = 2 ∧ g 3 ≠ 2) ∨
      (g 0 ≠ 2 ∧ g 1 = 2 ∧ g 2 ≠ 2 ∧ g 3 = 2) := by
    rcases e01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rcases e12 with ⟨h1', -⟩ | ⟨-, h2'⟩
      · exact absurd h1' h1
      · rcases e23 with ⟨-, h3⟩ | ⟨h2'', -⟩
        · exact Or.inl ⟨h0, h1, h2', h3⟩
        · exact absurd h2' h2''
    · rcases e12 with ⟨-, h2'⟩ | ⟨h1', -⟩
      · rcases e23 with ⟨h2'', -⟩ | ⟨-, h3⟩
        · exact absurd h2'' h2'
        · exact Or.inr ⟨h0, h1, h2', h3⟩
      · exact absurd h1 h1'
  -- either way the span is even and at least 10
  rcases key with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · obtain ⟨k, hk⟩ := (hg 1).odd_of_ne_two hb
    obtain ⟨l, hl⟩ := (hg 3).odd_of_ne_two hd
    have b1 := (hg 1).two_le
    have b3 := (hg 3).two_le
    have hdvd : 2 ∣ g 0 + g 1 + g 2 + g 3 := ⟨k + l + 3, by omega⟩
    rcases htot.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
  · obtain ⟨k, hk⟩ := (hg 0).odd_of_ne_two ha
    obtain ⟨l, hl⟩ := (hg 2).odd_of_ne_two hc
    have b0 := (hg 0).two_le
    have b2 := (hg 2).two_le
    have hdvd : 2 ∣ g 0 + g 1 + g 2 + g 3 := ⟨k + l + 3, by omega⟩
    rcases htot.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega

/-! ## Arithmetic obstructions used by the case analysis in the paper -/

/-- A rhombus of side `2` has diagonals `e, f` with `e² + f² = 16`; no two
primes do that, so the distance-two graph of a prime-distance quadruple has no
four-cycle. -/
theorem no_prime_sq_add_sq_eq_sixteen (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    p ^ 2 + q ^ 2 ≠ 16 := by
  intro h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hp4 : p ≤ 4 := by nlinarith
  have hq4 : q ≤ 4 := by nlinarith
  interval_cases p <;> interval_cases q <;> simp_all

/-- `q² = p² + 8` has no solution in odd primes; this kills the `r = p` branch
of the two-disjoint-edges case. -/
theorem no_prime_sq_eq_sq_add_eight (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) : q ^ 2 ≠ p ^ 2 + 8 := by
  intro h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hlt : p < q := by nlinarith
  have hle : q < p + 2 := by nlinarith
  have hq : q = p + 1 := by omega
  subst hq
  ring_nf at h
  omega

/-- No triangle with sides in `{2,3}` has circumradius `2`. In the form used:
with `16K² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴` the condition `R = 2` reads
`(abc)² = 4·16K²`, which fails for every choice. -/
theorem circumradius_ne_two (a b c : ℤ) (ha : a = 2 ∨ a = 3) (hb : b = 2 ∨ b = 3)
    (hc : c = 2 ∨ c = 3) :
    (a * b * c) ^ 2 ≠
      4 * (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2
        - a ^ 4 - b ^ 4 - c ^ 4) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

end Submission00000000049
