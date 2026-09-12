import Mathlib

/-!
# A counterexample to conjecture 00000000006

Conjecture 00000000006 asserts that a set `A ⊆ [N]` in which the average of any
two elements of the same parity is never prime satisfies `|A| ≤ (1/3 + ε) N`,
with `1/3` attained by the multiples of three.

Read with the two elements required to be **distinct** — the only non-vacuous
reading, since otherwise every prime `p ∈ A` violates the hypothesis through
`(p + p) / 2 = p` — the bound is false. The set

  `A = {n ≥ 1 : n % 12 ∈ {0, 3, 4, 8, 9}} = {multiples of 4} ∪ {n ≡ 3 [MOD 6]}`

satisfies the hypothesis and has density `5/12 > 1/3`.

Two halves are formalized here:

* `inA_admissible` — `A` satisfies the hypothesis, for Mathlib's `Nat.Prime`;
* `countA_lower` — `12 · |A ∩ [1,N]| + 55 ≥ 5N`, so the density is at least `5/12`;

and `conjecture_00000000006_false` combines them into the refutation.
-/

namespace Counterexample06

open Finset

/-- The counterexample, as a predicate on the positive integers. -/
def inA (n : ℕ) : Prop :=
  n % 12 = 0 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 8 ∨ n % 12 = 9

instance : DecidablePred inA := fun n => by unfold inA; infer_instance

/-! ## The set satisfies the hypothesis -/

/-- A number with a proper divisor above one is not prime. -/
theorem not_prime_of_dvd {p n : ℕ} (hp : 1 < p) (hpn : p < n) (hdvd : p ∣ n) :
    ¬ n.Prime := fun h => by
  rcases h.eq_one_or_self_of_dvd p hdvd with h1 | h2 <;> omega

/-- For distinct positive `a, b ∈ A` of equal parity the average is either even
and greater than `2`, or a multiple of `3` greater than `3`.

This is where the residues are used, and it is the step the informal argument
must not skip: the even elements of `A` are exactly the multiples of `4`, so
`a + b ≡ 0 [MOD 4]` and the average is even; the odd elements are exactly the
`n ≡ 3 [MOD 6]`, so `a + b ≡ 0 [MOD 6]` and the average is a multiple of `3`.
The lower bounds `2` and `3` likewise need the residues: they come from the
smallest admissible pairs `{4, 8}` and `{3, 9}`, not from mere distinctness. -/
theorem average_obstruction {a b : ℕ} (ha : inA a) (hb : inA b)
    (hpar : a % 2 = b % 2) (hne : a ≠ b) (hapos : 0 < a) (hbpos : 0 < b) :
    (2 ∣ (a + b) / 2 ∧ 2 < (a + b) / 2) ∨ (3 ∣ (a + b) / 2 ∧ 3 < (a + b) / 2) := by
  unfold inA at ha hb
  rcases ha with ha | ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb | hb <;>
    first
      | (left; exact ⟨⟨(a + b) / 2 / 2, by omega⟩, by omega⟩)
      | (right; exact ⟨⟨(a + b) / 2 / 3, by omega⟩, by omega⟩)

/-- `A` satisfies the hypothesis of the conjecture, stated with `Nat.Prime`. -/
theorem inA_admissible {a b : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (ha : inA a) (hb : inA b) (hne : a ≠ b) (hpar : a % 2 = b % 2) :
    ¬ Nat.Prime ((a + b) / 2) := by
  rcases average_obstruction ha hb hpar hne hapos hbpos with ⟨hd, hgt⟩ | ⟨hd, hgt⟩
  · exact not_prime_of_dvd (by norm_num) hgt hd
  · exact not_prime_of_dvd (by norm_num) hgt hd

/-! ## The set has density `5/12`

The counting half of the refutation, missing from the informal argument, where
`|A ∩ [1,N]| = 5N/12 + O(1)` is asserted from "five of twelve residue classes".
-/

/-- `countA N = |A ∩ [1, N]|`. -/
def countA (N : ℕ) : ℕ := ((range (N + 1)).filter (fun n => 0 < n ∧ inA n)).card

theorem countA_mono {M N : ℕ} (h : M ≤ N) : countA M ≤ countA N := by
  apply card_le_card
  intro x hx
  rw [mem_filter, mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- The five members of `A` in the block `(12q, 12q + 12]`. -/
def blockMember : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | 2 => 8
  | 3 => 9
  | _ => 12

theorem mod_five_cases (i : ℕ) :
    i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4 := by omega

/-- Enumerates `A` in order: the `i`-th element is in block `i / 5`. -/
def enumA (i : ℕ) : ℕ := 12 * (i / 5) + blockMember (i % 5)

theorem enumA_injOn (k : ℕ) : Set.InjOn enumA (range (5 * k)) := by
  intro i _ j _ hij
  simp only [enumA] at hij
  rcases mod_five_cases i with hi | hi | hi | hi | hi <;>
    rcases mod_five_cases j with hj | hj | hj | hj | hj <;>
      rw [hi, hj] at hij <;> simp only [blockMember] at hij <;> omega

theorem enumA_mem {k i : ℕ} (hi : i ∈ range (5 * k)) :
    enumA i ∈ (range (12 * k + 1)).filter (fun n => 0 < n ∧ inA n) := by
  rw [mem_range] at hi
  have h5 : i / 5 < k := by omega
  rw [mem_filter, mem_range]
  rcases mod_five_cases i with h | h | h | h | h <;>
    simp only [enumA, h, blockMember, inA] <;> omega

/-- Each block of twelve consecutive integers contributes five elements. -/
theorem five_mul_le_countA (k : ℕ) : 5 * k ≤ countA (12 * k) := by
  have := card_le_card_of_injOn enumA (fun i hi => enumA_mem hi) (enumA_injOn k)
  simpa [countA, card_range] using this

/-- The density of `A` is at least `5/12`, with an explicit additive constant. -/
theorem countA_lower (N : ℕ) : 5 * N ≤ 12 * countA N + 55 := by
  have h := five_mul_le_countA (N / 12)
  have hmono : countA (12 * (N / 12)) ≤ countA N := countA_mono (by omega)
  omega

/-! ## The refutation -/

/-- Conjecture 00000000006 is false.

`A` satisfies the hypothesis, yet for every `N ≥ 111` its counting function
exceeds `(1/3 + 1/24) N = 3N/8`, contradicting the asserted bound
`|A| ≤ (1/3 + ε) N` for every `ε < 1/12`. -/
theorem conjecture_00000000006_false :
    (∀ a b : ℕ, 0 < a → 0 < b → inA a → inA b → a ≠ b → a % 2 = b % 2 →
        ¬ Nat.Prime ((a + b) / 2)) ∧
      (∀ N, 111 ≤ N → 9 * N < 24 * countA N) := by
  refine ⟨fun a b ha hb hA hB hne hpar => inA_admissible ha hb hA hB hne hpar, ?_⟩
  intro N hN
  have := countA_lower N
  omega

/-- The multiples of three, the construction the conjecture proposes as extremal,
are indeed admissible — the conjecture's lower bound is correct; only its upper
bound fails. -/
theorem multiples_of_three_admissible {a b : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (ha : 3 ∣ a) (hb : 3 ∣ b) (hne : a ≠ b) (hpar : a % 2 = b % 2) :
    ¬ Nat.Prime ((a + b) / 2) := by
  refine not_prime_of_dvd (p := 3) (by norm_num) (by omega) ⟨(a + b) / 2 / 3, by omega⟩

end Counterexample06
